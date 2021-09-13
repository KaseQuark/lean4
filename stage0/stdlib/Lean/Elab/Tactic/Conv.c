// Lean compiler output
// Module: Lean.Elab.Tactic.Conv
// Imports: Init Lean.Elab.Tactic.Conv.Basic Lean.Elab.Tactic.Conv.Congr Lean.Elab.Tactic.Conv.Rewrite Lean.Elab.Tactic.Conv.Change Lean.Elab.Tactic.Conv.Simp Lean.Elab.Tactic.Conv.Pattern Lean.Elab.Tactic.Conv.Delta
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Congr(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Rewrite(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Change(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Simp(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Pattern(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Delta(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Tactic_Conv(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Congr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Rewrite(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Change(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Simp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Pattern(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Delta(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif