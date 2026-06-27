(* ExtractPulseBPF -- Extraction plugin for BPFStar.

   Translates BPFStar library calls to the correct Krml AST nodes
   for BPF C output. Runs as a pre-translation hook alongside
   ExtractPulse and ExtractPulseC. *)
module ExtractPulseBPF
friend FStarC.Extraction.Krml

open FStarC
open FStarC.Effect
open FStarC.Extraction
open FStarC.Extraction.ML
open FStarC.Extraction.ML.Syntax
open FStarC.Const
open FStarC.BaseTypes
open FStarC.Extraction.Krml

(* Extract the head name from a possibly type-applied expression *)
let rec head_name (e: mlexpr) : option mlpath =
  match e.expr with
  | MLE_Name p -> Some p
  | MLE_TApp ({ expr = MLE_Name p }, _) -> Some p
  | MLE_App (head, _) -> head_name head
  | _ -> None

(* Check if expression head matches a BPFStar function *)
let is_call (e: mlexpr) (name: string) : bool =
  match head_name e with
  | Some p -> string_of_mlpath p = name
  | None -> false

(* Flatten nested MLE_App and collect all arguments, stripping
   type applications. Returns (head_name, all_args). *)
let rec collect_args (e: mlexpr) : option mlpath & list mlexpr =
  match e.expr with
  | MLE_Name p -> (Some p, [])
  | MLE_TApp ({ expr = MLE_Name p }, _) -> (Some p, [])
  | MLE_App (head, args) ->
    let (p, prev_args) = collect_args head in
    (p, prev_args @ args)
  | _ -> (None, [])

(* Make a BPF helper call expression.
   For zero-arg calls, pass [EUnit] so Karamel emits f() not f *)
let bpf_call (name: string) (args: list expr) : expr =
  match args with
  | [] -> EApp (EQualified ([], name), [EUnit])
  | _ -> EApp (EQualified ([], name), args)

(* Extract a string constant from an ML expression.
   Used for field names in core_path. *)
let extract_string (e: mlexpr) : ML string =
  match e.expr with
  | MLE_Const (MLC_String s) -> s
  | _ -> failwith "ExtractPulseBPF: expected string constant in field name"

(* Walk a core_path ML expression and collect field names.
   The path is either:
     LeafImpl(name) -> [name]
     StepImpl(name, rest) -> name :: walk(rest) *)
let rec collect_core_path_fields (e: mlexpr) : ML (list string) =
  let (p, args) = collect_args e in
  match p with
  | Some p ->
    let name = string_of_mlpath p in
    if name = "BPFStar.Core.LeafImpl" then
      (match args with
       | [field_name] -> [extract_string field_name]
       | _ -> failwith "ExtractPulseBPF: LeafImpl expects 1 argument")
    else if name = "BPFStar.Core.StepImpl" then
      (match args with
       | [field_name; rest] ->
         extract_string field_name :: collect_core_path_fields rest
       | _ -> failwith "ExtractPulseBPF: StepImpl expects 2 arguments")
    else failwith ("ExtractPulseBPF: unexpected core_path constructor: " ^ name)
  | None -> failwith "ExtractPulseBPF: cannot extract core_path head"

(* Emit a BPF_CORE_READ(ptr, field1, field2, ...) macro call.
   Since BPF_CORE_READ is a C macro (not a function), we emit
   it as verbatim C text wrapped in an EApp of a macro name. *)
let emit_core_read (ptr: expr) (fields: list string) (macro: string) : ML expr =
  let field_args = String.concat ", " fields in
  (* Use EVerbatim to emit the macro call directly *)
  let macro_text = macro ^ "(" in
  EApp (
    EQualified ([], "__bpfstar_core_read"),
    [ptr; EConstant (UInt8, field_args)]
  )

(* Type translation: BPFStar abstract types -> C types *)
let bpf_translate_type_without_decay : translate_type_without_decay_t = fun env t ->
  match t with
  | MLTY_Named ([_; _], p)
    when string_of_mlpath p = "BPFStar.Map.bpf_map" ->
    TAny

  | MLTY_Named ([], p)
    when string_of_mlpath p = "BPFStar.RingBuf.bpf_ringbuf" ->
    TAny

  | MLTY_Named ([], p)
    when string_of_mlpath p = "BPFStar.Types.ctx_ptr" ->
    TAny

  (* kptr -> void* *)
  | MLTY_Named ([_], p)
    when string_of_mlpath p = "BPFStar.KPtr.kptr" ->
    TAny

  (* field -> erased (string at runtime, but not needed in C type) *)
  | MLTY_Named ([_; _], p)
    when string_of_mlpath p = "BPFStar.Core.field" ->
    TAny

  (* core_path -> erased *)
  | MLTY_Named ([_; _], p)
    when string_of_mlpath p = "BPFStar.Core.core_path" ->
    TAny

  (* core_path_impl -> erased *)
  | MLTY_Named ([], p)
    when string_of_mlpath p = "BPFStar.Core.core_path_impl" ->
    TAny

  (* bpf_spin_lock_t *)
  | MLTY_Named ([], p)
    when string_of_mlpath p = "BPFStar.SpinLock.bpf_spin_lock_t" ->
    TQualified ([], "struct bpf_spin_lock")

  | _ -> raise NotSupportedByKrmlExtension

(* Expression translation: BPFStar calls -> Krml AST *)
let bpf_translate_expr : translate_expr_t = fun env e ->
  let cb = translate_expr env in
  let (p, args) = collect_args e in
  match p with
  | None -> raise NotSupportedByKrmlExtension
  | Some p ->
  let name = string_of_mlpath p in

  (* --- BPF Helpers (pure queries, universal) ---
     These take a unit arg that we drop. *)
  if name = "BPFStar.Helpers.bpf_get_current_pid_tgid" then
    bpf_call "bpf_get_current_pid_tgid" []
  else if name = "BPFStar.Helpers.bpf_get_current_uid_gid" then
    bpf_call "bpf_get_current_uid_gid" []
  else if name = "BPFStar.Helpers.bpf_get_current_task" then
    bpf_call "bpf_get_current_task" []
  else if name = "BPFStar.Helpers.bpf_get_current_task_btf" then
    bpf_call "bpf_get_current_task_btf" []
  else if name = "BPFStar.Helpers.bpf_get_smp_processor_id" then
    bpf_call "bpf_get_smp_processor_id" []
  else if name = "BPFStar.Helpers.bpf_get_prandom_u32" then
    bpf_call "bpf_get_prandom_u32" []

  (* --- Time helpers (universal, unit arg) --- *)
  else if name = "BPFStar.Helpers.bpf_ktime_get_ns" then
    bpf_call "bpf_ktime_get_ns" []
  else if name = "BPFStar.Helpers.bpf_ktime_get_boot_ns" then
    bpf_call "bpf_ktime_get_boot_ns" []
  else if name = "BPFStar.Helpers.bpf_ktime_get_coarse_ns" then
    bpf_call "bpf_ktime_get_coarse_ns" []
  else if name = "BPFStar.Helpers.bpf_ktime_get_tai_ns" then
    bpf_call "bpf_ktime_get_tai_ns" []
  else if name = "BPFStar.Helpers.bpf_jiffies64" then
    bpf_call "bpf_jiffies64" []

  (* --- Memory readers (universal) --- *)
  else if name = "BPFStar.Helpers.bpf_probe_read_kernel" then
    (match args with
     | [dst; size; src] -> bpf_call "bpf_probe_read_kernel" [cb dst; cb size; cb src]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.bpf_probe_read_user" then
    (match args with
     | [dst; size; src] -> bpf_call "bpf_probe_read_user" [cb dst; cb size; cb src]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.bpf_probe_read_kernel_str" then
    (match args with
     | [dst; size; src] -> bpf_call "bpf_probe_read_kernel_str" [cb dst; cb size; cb src]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.bpf_probe_read_user_str" then
    (match args with
     | [dst; size; src] -> bpf_call "bpf_probe_read_user_str" [cb dst; cb size; cb src]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.bpf_get_current_comm" then
    (match args with
     | [buf; size] -> bpf_call "bpf_get_current_comm" [cb buf; cb size]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.bpf_copy_from_user" then
    (match args with
     | [dst; size; ptr] -> bpf_call "bpf_copy_from_user" [cb dst; cb size; cb ptr]
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- Signal helpers (universal) --- *)
  else if name = "BPFStar.Helpers.bpf_send_signal" then
    (match args with
     | [sig_] -> bpf_call "bpf_send_signal" [cb sig_]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.bpf_send_signal_thread" then
    (match args with
     | [sig_] -> bpf_call "bpf_send_signal_thread" [cb sig_]
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- Namespace helpers (universal) --- *)
  else if name = "BPFStar.Helpers.bpf_get_ns_current_pid_tgid" then
    (match args with
     | [dev; ino; nsdata; size] ->
       bpf_call "bpf_get_ns_current_pid_tgid" [cb dev; cb ino; cb nsdata; cb size]
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- Debug (universal) --- *)
  else if name = "BPFStar.Helpers.bpf_trace_printk" then
    (match args with
     | [fmt] -> bpf_call "bpf_trace_printk" [cb fmt]
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- Tail call (universal) --- *)
  else if name = "BPFStar.Helpers.bpf_tail_call" then
    (match args with
     | [ctx; prog_array; index] ->
       bpf_call "bpf_tail_call" [cb ctx; cb prog_array; cb index]
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- Tracing-family helpers ---
     Capability args are erased, so these have the same
     arg count as their C equivalents. *)
  else if name = "BPFStar.Helpers.bpf_probe_read" then
    (match args with
     | [dst; size; src] -> bpf_call "bpf_probe_read" [cb dst; cb size; cb src]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.bpf_probe_read_str" then
    (match args with
     | [dst; size; src] -> bpf_call "bpf_probe_read_str" [cb dst; cb size; cb src]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.bpf_probe_write_user" then
    (match args with
     | [dst; src; len] -> bpf_call "bpf_probe_write_user" [cb dst; cb src; cb len]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.bpf_get_stack" then
    (match args with
     | [ctx; buf; size; flags] ->
       bpf_call "bpf_get_stack" [cb ctx; cb buf; cb size; cb flags]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.bpf_get_stackid" then
    (match args with
     | [ctx; map; flags] -> bpf_call "bpf_get_stackid" [cb ctx; cb map; cb flags]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.bpf_get_attach_cookie" then
    (match args with
     | [ctx] -> bpf_call "bpf_get_attach_cookie" [cb ctx]
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- Advanced tracing (fentry/fexit/LSM) --- *)
  else if name = "BPFStar.Helpers.bpf_d_path" then
    (match args with
     | [path; buf; sz] -> bpf_call "bpf_d_path" [cb path; cb buf; cb sz]
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- Kprobe + fentry/fexit --- *)
  else if name = "BPFStar.Helpers.bpf_get_func_ip" then
    (match args with
     | [ctx] -> bpf_call "bpf_get_func_ip" [cb ctx]
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- Kprobe only --- *)
  else if name = "BPFStar.Helpers.bpf_override_return" then
    (match args with
     | [regs; rc] -> bpf_call "bpf_override_return" [cb regs; cb rc]
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- LSM only --- *)
  else if name = "BPFStar.Helpers.bpf_ima_inode_hash" then
    (match args with
     | [inode; dst; size] -> bpf_call "bpf_ima_inode_hash" [cb inode; cb dst; cb size]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.bpf_ima_file_hash" then
    (match args with
     | [file; dst; size] -> bpf_call "bpf_ima_file_hash" [cb file; cb dst; cb size]
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- Spin lock --- *)
  else if name = "BPFStar.SpinLock.bpf_spin_lock" then
    (match args with
     | [lock] -> bpf_call "bpf_spin_lock" [EAddrOf (cb lock)]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.SpinLock.bpf_spin_unlock" then
    (match args with
     | [lock] -> bpf_call "bpf_spin_unlock" [EAddrOf (cb lock)]
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- CO-RE: core_read ---
     core_read(ptr, path) -> BPF_CORE_READ(ptr, field1, ..., fieldN)
     The path is a StepImpl/LeafImpl chain carrying field name strings. *)
  else if name = "BPFStar.Core.core_read" then
    (match args with
     | [ptr; path] ->
       let fields = collect_core_path_fields path in
       let field_str = String.concat ", " fields in
       (* Emit as: BPF_CORE_READ(ptr, field1, field2, ...)
          Use EApp with a macro-style qualified name *)
       EApp (EQualified ([], "BPF_CORE_READ"),
             cb ptr :: List.Tot.map (fun f -> EQualified ([], f)) fields)
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- CO-RE: core_read_into ---
     core_read_into(ptr, path, dst) -> BPF_CORE_READ_INTO(dst, ptr, f1, ..., fN) *)
  else if name = "BPFStar.Core.core_read_into" then
    (match args with
     | [ptr; path; dst] ->
       let fields = collect_core_path_fields path in
       EApp (EQualified ([], "BPF_CORE_READ_INTO"),
             cb dst :: cb ptr :: List.Tot.map (fun f -> EQualified ([], f)) fields)
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- CO-RE: core_read_str ---
     core_read_str(ptr, path, dst, size) ->
       BPF_CORE_READ_STR_INTO(dst, size, ptr, f1, ..., fN) *)
  else if name = "BPFStar.Core.core_read_str" then
    (match args with
     | [ptr; path; dst; size] ->
       let fields = collect_core_path_fields path in
       EApp (EQualified ([], "BPF_CORE_READ_STR_INTO"),
             cb dst :: cb size :: cb ptr ::
             List.Tot.map (fun f -> EQualified ([], f)) fields)
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- CO-RE: core_field_exists ---
     core_field_exists(field) -> bpf_core_field_exists(...)
     The field is a string (mk_field extracts to the string directly). *)
  else if name = "BPFStar.Core.core_field_exists" then
    (* This is tricky -- bpf_core_field_exists needs a type+field
       expression, not just a string. Punt for now with a direct call. *)
    (match args with
     | [f] -> bpf_call "bpf_core_field_exists" [cb f]
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- CO-RE: mk_field / leaf / step ---
     These are constructors used within path definitions.
     If they appear as standalone expressions (let-bound paths),
     translate them through. *)
  else if name = "BPFStar.Core.mk_field" then
    (match args with
     | [s] -> cb s  (* pass through the string *)
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Core.LeafImpl" then
    (match args with
     | [s] -> cb s
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Core.StepImpl" then
    (match args with
     | [s; rest] -> cb rest  (* when used standalone, just pass through *)
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- Map operations ---

     map_lookup takes (map, key) by value. We emit:
       { typeof(key) __k = key; bpf_map_lookup_elem(&map, &__k); }
     Since map_lookup has admit() body, we intercept the call and
     emit the stack allocation + helper call directly. *)
  else if name = "BPFStar.Map.map_lookup" then
    (match args with
     | [m; k] ->
       (* Create a stack-allocated key and call bpf_map_lookup_elem *)
       ELet (
         { name = "__bpfstar_key"; typ = TAny; mut = true; meta = [] },
         cb k,
         bpf_call "bpf_map_lookup_elem" [
           EAddrOf (cb m);
           EAddrOf (EBound 0)
         ]
       )
     | _ -> raise NotSupportedByKrmlExtension)

  (* bpf_map_lookup_elem: low-level, takes refs *)
  else if name = "BPFStar.Map.bpf_map_lookup_elem" then
    (match args with
     | [m; k] -> bpf_call "bpf_map_lookup_elem" [EAddrOf (cb m); cb k]
     | _ -> raise NotSupportedByKrmlExtension)

  (* bpf_map_update_elem *)
  else if name = "BPFStar.Map.bpf_map_update_elem" then
    (match args with
     | [m; k; v; flags] -> bpf_call "bpf_map_update_elem" [EAddrOf (cb m); cb k; cb v; cb flags]
     | _ -> raise NotSupportedByKrmlExtension)

  (* bpf_map_delete_elem *)
  else if name = "BPFStar.Map.bpf_map_delete_elem" then
    (match args with
     | [m; k] -> bpf_call "bpf_map_delete_elem" [EAddrOf (cb m); cb k]
     | _ -> raise NotSupportedByKrmlExtension)

  (* release_map_value: no-op *)
  else if name = "BPFStar.Map.release_map_value" then
    EUnit

  (* read_map_value: dereference *)
  else if name = "BPFStar.Map.read_map_value" then
    (match args with
     | [_m; ptr] ->
       EBufRead (cb ptr, EQualified (["Pulse"; "Lib"; "Pervasives"], "_zero_for_deref"))
     | _ -> raise NotSupportedByKrmlExtension)

  (* write_map_value: write through pointer *)
  else if name = "BPFStar.Map.write_map_value" then
    (match args with
     | [_m; ptr; value] ->
       EBufWrite (cb ptr, EQualified (["Pulse"; "Lib"; "Pervasives"], "_zero_for_deref"), cb value)
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- Ring buffer operations --- *)

  else if name = "BPFStar.RingBuf.bpf_ringbuf_reserve" then
    (match args with
     | [rb; size; flags] -> bpf_call "bpf_ringbuf_reserve" [EAddrOf (cb rb); cb size; cb flags]
     | _ -> raise NotSupportedByKrmlExtension)

  else if name = "BPFStar.RingBuf.bpf_ringbuf_submit" then
    (match args with
     | [ptr; flags] -> bpf_call "bpf_ringbuf_submit" [cb ptr; cb flags]
     | _ -> raise NotSupportedByKrmlExtension)

  else if name = "BPFStar.RingBuf.bpf_ringbuf_discard" then
    (match args with
     | [ptr; flags] -> bpf_call "bpf_ringbuf_discard" [cb ptr; cb flags]
     | _ -> raise NotSupportedByKrmlExtension)

  (* map_update: map, key, value, flags -> stack-allocate key+value *)
  else if name = "BPFStar.Map.map_update" then
    (match args with
     | [m; k; v; flags] ->
       ELet (
         { name = "__bpfstar_key"; typ = TAny; mut = true; meta = [] },
         cb k,
         ELet (
           { name = "__bpfstar_val"; typ = TAny; mut = true; meta = [] },
           cb v,
           bpf_call "bpf_map_update_elem" [
             EAddrOf (cb m);
             EAddrOf (EBound 1);
             EAddrOf (EBound 0);
             cb flags
           ]
         )
       )
     | _ -> raise NotSupportedByKrmlExtension)

  (* map_delete: map, key -> stack-allocate key *)
  else if name = "BPFStar.Map.map_delete" then
    (match args with
     | [m; k] ->
       ELet (
         { name = "__bpfstar_key"; typ = TAny; mut = true; meta = [] },
         cb k,
         bpf_call "bpf_map_delete_elem" [
           EAddrOf (cb m);
           EAddrOf (EBound 0)
         ]
       )
     | _ -> raise NotSupportedByKrmlExtension)

  (* --- Map/RingBuf constructors ---
     These are used in global definitions. The actual C definition
     is emitted by the let-binding hook via Prologue+Verbatim. *)
  else if name = "BPFStar.Map.define_hash_map" then EUnit
  else if name = "BPFStar.Map.define_array_map" then EUnit
  else if name = "BPFStar.Map.define_lru_hash_map" then EUnit
  else if name = "BPFStar.Map.define_percpu_array_map" then EUnit
  else if name = "BPFStar.RingBuf.define_ringbuf" then EUnit

  (* --- Storage helpers ---
     release/read/write for storage values mirror map value ops. *)
  else if name = "BPFStar.Helpers.Storage.release_storage_value" then
    EUnit
  else if name = "BPFStar.Helpers.Storage.read_storage_value" then
    (match args with
     | [_m; ptr] ->
       EBufRead (cb ptr, EQualified (["Pulse"; "Lib"; "Pervasives"], "_zero_for_deref"))
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.Storage.write_storage_value" then
    (match args with
     | [_m; ptr; value] ->
       EBufWrite (cb ptr, EQualified (["Pulse"; "Lib"; "Pervasives"], "_zero_for_deref"), cb value)
     | _ -> raise NotSupportedByKrmlExtension)

  (* Storage get/delete helpers -- capability args erased *)
  else if name = "BPFStar.Helpers.Storage.bpf_inode_storage_get" then
    (match args with
     | [m; inode; value; flags] ->
       bpf_call "bpf_inode_storage_get" [EAddrOf (cb m); cb inode; cb value; cb flags]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.Storage.bpf_inode_storage_delete" then
    (match args with
     | [m; inode] -> bpf_call "bpf_inode_storage_delete" [EAddrOf (cb m); cb inode]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.Storage.bpf_task_storage_get" then
    (match args with
     | [m; task; value; flags] ->
       bpf_call "bpf_task_storage_get" [EAddrOf (cb m); cb task; cb value; cb flags]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.Storage.bpf_task_storage_delete" then
    (match args with
     | [m; task] -> bpf_call "bpf_task_storage_delete" [EAddrOf (cb m); cb task]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.Storage.bpf_cgrp_storage_get" then
    (match args with
     | [m; cgroup; value; flags] ->
       bpf_call "bpf_cgrp_storage_get" [EAddrOf (cb m); cb cgroup; cb value; cb flags]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.Storage.bpf_cgrp_storage_delete" then
    (match args with
     | [m; cgroup] -> bpf_call "bpf_cgrp_storage_delete" [EAddrOf (cb m); cb cgroup]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.Storage.bpf_sk_storage_get" then
    (match args with
     | [m; sk; value; flags] ->
       bpf_call "bpf_sk_storage_get" [EAddrOf (cb m); cb sk; cb value; cb flags]
     | _ -> raise NotSupportedByKrmlExtension)
  else if name = "BPFStar.Helpers.Storage.bpf_sk_storage_delete" then
    (match args with
     | [m; sk] -> bpf_call "bpf_sk_storage_delete" [EAddrOf (cb m); cb sk]
     | _ -> raise NotSupportedByKrmlExtension)

  else raise NotSupportedByKrmlExtension

(* --- Map type name mapping ---
   Maps Pulse type names to C type names for BTF __type() macros. *)
let c_type_name (t: mlty) : ML string =
  match t with
  | MLTY_Named ([], p) ->
    let s = string_of_mlpath p in
    if s = "FStar.UInt8.t" then "u8"
    else if s = "FStar.UInt16.t" then "u16"
    else if s = "FStar.UInt32.t" then "u32"
    else if s = "FStar.UInt64.t" then "u64"
    else if s = "FStar.Int8.t" then "s8"
    else if s = "FStar.Int16.t" then "s16"
    else if s = "FStar.Int32.t" then "s32"
    else if s = "FStar.Int64.t" then "s64"
    else
      (* Use just the type name without module prefix, matching -no-prefix *)
      let (_, short_name) = p in
      short_name
  | _ -> "void"

(* Generate BTF struct definition for a BPF map *)
let map_definition (map_type: string) (name: string)
    (key_type: string) (value_type: string) (max_entries: string) : string =
  "struct {\n" ^
  "  __uint(type, " ^ map_type ^ ");\n" ^
  "  __uint(max_entries, " ^ max_entries ^ ");\n" ^
  "  __type(key, " ^ key_type ^ ");\n" ^
  "  __type(value, " ^ value_type ^ ");\n" ^
  "} " ^ name ^ " SEC(\".maps\");\n"

(* Generate BTF struct definition for a BPF ring buffer *)
let ringbuf_definition (name: string) (size: string) : string =
  "struct {\n" ^
  "  __uint(type, BPF_MAP_TYPE_RINGBUF);\n" ^
  "  __uint(max_entries, " ^ size ^ ");\n" ^
  "} " ^ name ^ " SEC(\".maps\");\n"

(* Let-binding translation: intercept BPF map/ringbuf definitions *)
let bpf_translate_let : translate_let_t = fun env flavor lb ->
  match lb with
  | { mllb_name = name;
      mllb_tysc = Some ([], t);
      mllb_def = def;
      mllb_meta = meta } ->
    let (head, args) = collect_args def in
    (match head with
     | Some p ->
       let fn_name = string_of_mlpath p in
       let qname = env.module_name, name in
       let flags = translate_flags meta in

       (* define_hash_map #kt #vt max_entries *)
       if fn_name = "BPFStar.Map.define_hash_map" ||
          fn_name = "BPFStar.Map.define_array_map" ||
          fn_name = "BPFStar.Map.define_lru_hash_map" ||
          fn_name = "BPFStar.Map.define_percpu_array_map" then
         let map_type =
           if fn_name = "BPFStar.Map.define_hash_map" then "BPF_MAP_TYPE_HASH"
           else if fn_name = "BPFStar.Map.define_array_map" then "BPF_MAP_TYPE_ARRAY"
           else if fn_name = "BPFStar.Map.define_lru_hash_map" then "BPF_MAP_TYPE_LRU_HASH"
           else "BPF_MAP_TYPE_PERCPU_ARRAY"
         in
         (* Extract key and value types from the type annotation *)
         let (key_t, val_t) = match t with
           | MLTY_Named ([kt; vt], _) -> (c_type_name kt, c_type_name vt)
           | _ -> ("void", "void")
         in
         (* Extract max_entries from the argument *)
         let max_entries = match args with
           | [e] ->
             (match e.expr with
              | MLE_Const (MLC_Int (s, _)) -> s
              | _ -> "0")
           | _ -> "0"
         in
         let prologue = map_definition map_type name key_t val_t max_entries in
         Some (DGlobal (Verbatim :: Prologue prologue :: flags, qname, 0, TAny, EUnit))

       (* define_ringbuf size *)
       else if fn_name = "BPFStar.RingBuf.define_ringbuf" then
         let size = match args with
           | [e] ->
             (match e.expr with
              | MLE_Const (MLC_Int (s, _)) -> s
              | _ -> "0")
           | _ -> "0"
         in
         let prologue = ringbuf_definition name size in
         Some (DGlobal (Verbatim :: Prologue prologue :: flags, qname, 0, TAny, EUnit))

       (* mk_field / LeafImpl / StepImpl: field and path definitions
          are compile-time only; suppress the C declaration *)
       else if fn_name = "BPFStar.Core.mk_field" ||
               fn_name = "BPFStar.Core.LeafImpl" ||
               fn_name = "BPFStar.Core.StepImpl" ||
               fn_name = "BPFStar.Core.leaf" ||
               fn_name = "BPFStar.Core.step" then
         Some (DGlobal (Verbatim :: flags, qname, 0, TAny, EUnit))

       else raise NotSupportedByKrmlExtension
     | _ -> raise NotSupportedByKrmlExtension)
  | _ -> raise NotSupportedByKrmlExtension

(* Register hooks *)
let _ =
  register_pre_translate_type_without_decay bpf_translate_type_without_decay;
  register_pre_translate_expr bpf_translate_expr;
  register_pre_translate_let bpf_translate_let
