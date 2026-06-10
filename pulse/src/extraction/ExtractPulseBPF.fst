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

  | _ -> raise NotSupportedByKrmlExtension

(* Expression translation: BPFStar calls -> Krml AST *)
let bpf_translate_expr : translate_expr_t = fun env e ->
  let cb = translate_expr env in
  let (p, args) = collect_args e in
  match p with
  | None -> raise NotSupportedByKrmlExtension
  | Some p ->
  let name = string_of_mlpath p in

  (* --- BPF Helpers (pure queries) ---
     These take a unit arg that we drop. *)
  if name = "BPFStar.Helpers.bpf_get_current_pid_tgid" then
    bpf_call "bpf_get_current_pid_tgid" []
  else if name = "BPFStar.Helpers.bpf_get_current_uid_gid" then
    bpf_call "bpf_get_current_uid_gid" []
  else if name = "BPFStar.Helpers.bpf_ktime_get_boot_ns" then
    bpf_call "bpf_ktime_get_boot_ns" []
  else if name = "BPFStar.Helpers.bpf_get_smp_processor_id" then
    bpf_call "bpf_get_smp_processor_id" []
  else if name = "BPFStar.Helpers.bpf_get_prandom_u32" then
    bpf_call "bpf_get_prandom_u32" []

  (* --- BPF Helpers (memory readers) --- *)
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
  else if name = "BPFStar.Helpers.bpf_get_current_comm" then
    (match args with
     | [buf; size] -> bpf_call "bpf_get_current_comm" [cb buf; cb size]
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

       else raise NotSupportedByKrmlExtension
     | _ -> raise NotSupportedByKrmlExtension)
  | _ -> raise NotSupportedByKrmlExtension

(* Register hooks *)
let _ =
  register_pre_translate_type_without_decay bpf_translate_type_without_decay;
  register_pre_translate_expr bpf_translate_expr;
  register_pre_translate_let bpf_translate_let
