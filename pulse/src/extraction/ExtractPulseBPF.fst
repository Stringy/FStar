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

  (* --- Program attributes (compile-time only) --- *)
  else if name = "BPFStar.Program.bpf_section" then EUnit
  else if name = "BPFStar.Program.bpf_license" then EUnit

  else raise NotSupportedByKrmlExtension

(* Register hooks *)
let _ =
  register_pre_translate_type_without_decay bpf_translate_type_without_decay;
  register_pre_translate_expr bpf_translate_expr
