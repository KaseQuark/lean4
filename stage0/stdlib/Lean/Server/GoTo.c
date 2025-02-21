// Lean compiler output
// Module: Lean.Server.GoTo
// Imports: Init Lean.Data.Json.FromToJson Lean.Util.Path Lean.Server.Utils
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_Uri_pathToUri(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lean_noConfusionExt;
LEAN_EXPORT lean_object* l_Lean_Server_instFromJsonGoToKind;
lean_object* l_Lean_findModuleOf_x3f___at_Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_orElseLazy___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_instToJsonGoToKind___closed__1;
static lean_object* l_Lean_Server_documentUriFromModule___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_locationLinksFromDecl___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instBEqGoToKind;
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__3;
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonGoToKind;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__3___closed__1;
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__1;
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__2;
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_instBEqGoToKind___closed__1;
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_toCtorIdx(uint8_t);
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__1;
static lean_object* l_Lean_Server_GoToKind_noConfusion___rarg___closed__1;
static lean_object* l_Lean_Server_instFromJsonGoToKind___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1(lean_object*);
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40_(uint8_t);
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_toCtorIdx___boxed(lean_object*);
lean_object* l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at_Lean_findDeclarationRanges_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___closed__1;
static lean_object* l_Lean_Server_locationLinksFromDecl___lambda__2___closed__2;
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__6;
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_beqGoToKind____x40_Lean_Server_GoTo___hyg_16____boxed(lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedDeclarationRanges;
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_GoTo_0__Lean_Server_beqGoToKind____x40_Lean_Server_GoTo___hyg_16_(uint8_t, uint8_t);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_noConfusion___rarg___lambda__1___boxed(lean_object*);
static lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__5;
extern lean_object* l_Lean_builtinDeclRanges;
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Server_GoToKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_GoToKind_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_GoToKind_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_GoToKind_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_GoToKind_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_GoToKind_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Server_GoToKind_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_GoTo_0__Lean_Server_beqGoToKind____x40_Lean_Server_GoTo___hyg_16_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Server_GoToKind_toCtorIdx(x_1);
x_4 = l_Lean_Server_GoToKind_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_beqGoToKind____x40_Lean_Server_GoTo___hyg_16____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Server_GoTo_0__Lean_Server_beqGoToKind____x40_Lean_Server_GoTo___hyg_16_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_instBEqGoToKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_GoTo_0__Lean_Server_beqGoToKind____x40_Lean_Server_GoTo___hyg_16____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_instBEqGoToKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_instBEqGoToKind___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declaration", 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("definition", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40_(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__4;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__6;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40_(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_instToJsonGoToKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_instToJsonGoToKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_instToJsonGoToKind___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("no inductive constructor matched", 32);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___closed__2;
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__2;
x_2 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__1;
x_3 = l_Except_orElseLazy___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__3;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__1;
x_9 = l_Except_orElseLazy___rarg(x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__1;
x_13 = l_Except_orElseLazy___rarg(x_11, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__3;
return x_14;
}
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__3___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_2);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___rarg(x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___rarg(x_11, x_7);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_13 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__3___closed__1;
x_14 = l_Except_orElseLazy___rarg(x_13, x_7);
return x_14;
}
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__5;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__2;
x_5 = l_Lean_Json_parseTagged(x_1, x_2, x_3, x_4);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__3___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Except_orElseLazy___rarg(x_5, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Except_orElseLazy___rarg(x_10, x_6);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__3;
x_13 = l_Except_orElseLazy___rarg(x_12, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonGoToKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonGoToKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_instFromJsonGoToKind___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_documentUriFromModule___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Server_documentUriFromModule___closed__1;
x_5 = l_Lean_SearchPath_findModuleWithExt(x_1, x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_io_realpath(x_15, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_System_Uri_pathToUri(x_18);
lean_ctor_set(x_6, 0, x_19);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = l_System_Uri_pathToUri(x_20);
lean_ctor_set(x_6, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_6);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_io_realpath(x_28, x_13);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = l_System_Uri_pathToUri(x_30);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_32)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_32;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_38 = x_29;
} else {
 lean_dec_ref(x_29);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
return x_5;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_5, 0);
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_5);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_declRangeExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_instInhabitedDeclarationRanges;
x_12 = l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2___closed__1;
x_13 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_11, x_12, x_10, x_1);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_instInhabitedDeclarationRanges;
x_18 = l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2___closed__1;
x_19 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_17, x_18, x_16, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
static lean_object* _init_l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_builtinDeclRanges;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1___closed__1;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_RBNode_find___at_Lean_findDeclarationRanges_x3f___spec__1(x_13, x_1);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l_Lean_RBNode_find___at_Lean_findDeclarationRanges_x3f___spec__1(x_15, x_1);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
}
static lean_object* _init_l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_noConfusionExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_isRec___at___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getKeyArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_1);
lean_inc(x_10);
x_14 = lean_is_aux_recursor(x_10, x_1);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___closed__1;
lean_inc(x_1);
x_16 = l_Lean_TagDeclarationExtension_isTagged(x_15, x_10, x_1);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_unbox(x_12);
lean_dec(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_1);
x_18 = l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2(x_1, x_2, x_3, x_4, x_5, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1(x_1, x_19, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = l_Lean_Name_getPrefix(x_1);
x_23 = l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2(x_22, x_2, x_3, x_4, x_5, x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1(x_1, x_24, x_2, x_3, x_4, x_5, x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
x_27 = l_Lean_Name_getPrefix(x_1);
x_28 = l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2(x_27, x_2, x_3, x_4, x_5, x_13);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1(x_1, x_29, x_2, x_3, x_4, x_5, x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_12);
lean_dec(x_10);
x_32 = l_Lean_Name_getPrefix(x_1);
x_33 = l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2(x_32, x_2, x_3, x_4, x_5, x_13);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1(x_1, x_34, x_2, x_3, x_4, x_5, x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Server_locationLinksFromDecl___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_locationLinksFromDecl___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_locationLinksFromDecl___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Server_locationLinksFromDecl___lambda__2___closed__1;
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_9);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_apply_6(x_13, x_14, x_4, x_5, x_6, x_7, x_12);
return x_15;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_9);
lean_dec(x_11);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_apply_6(x_13, x_16, x_4, x_5, x_6, x_7, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 3);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_25, x_26);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_nat_sub(x_29, x_26);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 3);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_nat_sub(x_38, x_26);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_nat_sub(x_41, x_26);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_20);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_2);
lean_ctor_set(x_45, 1, x_20);
lean_ctor_set(x_45, 2, x_32);
lean_ctor_set(x_45, 3, x_44);
x_46 = l_Lean_Server_locationLinksFromDecl___lambda__2___closed__2;
x_47 = lean_array_push(x_46, x_45);
lean_ctor_set(x_9, 0, x_47);
return x_9;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_9);
x_50 = l_Lean_Server_locationLinksFromDecl___lambda__2___closed__1;
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
x_51 = lean_box(0);
x_52 = lean_apply_6(x_50, x_51, x_4, x_5, x_6, x_7, x_49);
return x_52;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_48);
lean_dec(x_2);
x_53 = lean_box(0);
x_54 = lean_apply_6(x_50, x_53, x_4, x_5, x_6, x_7, x_49);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 0);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 3);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_62, x_63);
lean_dec(x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
lean_dec(x_60);
x_67 = lean_nat_sub(x_66, x_63);
lean_dec(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_ctor_get(x_55, 1);
lean_inc(x_70);
lean_dec(x_55);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 3);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_nat_sub(x_75, x_63);
lean_dec(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_72);
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_nat_sub(x_78, x_63);
lean_dec(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_74);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_57);
x_82 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_82, 0, x_2);
lean_ctor_set(x_82, 1, x_57);
lean_ctor_set(x_82, 2, x_69);
lean_ctor_set(x_82, 3, x_81);
x_83 = l_Lean_Server_locationLinksFromDecl___lambda__2___closed__2;
x_84 = lean_array_push(x_83, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_49);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_3);
x_10 = l_Lean_findModuleOf_x3f___at_Lean_Elab_Info_fmtHover_x3f_fmtModule_x3f___spec__1(x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = l_Lean_Server_locationLinksFromDecl___lambda__2(x_3, x_4, x_13, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_st_ref_get(x_8, x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_7, 5);
lean_inc(x_19);
x_20 = l_Lean_Server_documentUriFromModule(x_1, x_16, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Server_locationLinksFromDecl___lambda__2(x_3, x_4, x_21, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_21);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_io_error_to_string(x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_io_error_to_string(x_30);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_10);
if (x_37 == 0)
{
return x_10;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_10, 0);
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_10);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_locationLinksFromDecl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Server_locationLinksFromDecl___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_FromToJson(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Path(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Utils(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_GoTo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_FromToJson(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_GoToKind_noConfusion___rarg___closed__1 = _init_l_Lean_Server_GoToKind_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_GoToKind_noConfusion___rarg___closed__1);
l_Lean_Server_instBEqGoToKind___closed__1 = _init_l_Lean_Server_instBEqGoToKind___closed__1();
lean_mark_persistent(l_Lean_Server_instBEqGoToKind___closed__1);
l_Lean_Server_instBEqGoToKind = _init_l_Lean_Server_instBEqGoToKind();
lean_mark_persistent(l_Lean_Server_instBEqGoToKind);
l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__1 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__1();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__1);
l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__2 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__2();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__2);
l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__3 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__3();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__3);
l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__4 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__4();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__4);
l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__5 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__5();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__5);
l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__6 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__6();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_toJsonGoToKind____x40_Lean_Server_GoTo___hyg_40____closed__6);
l_Lean_Server_instToJsonGoToKind___closed__1 = _init_l_Lean_Server_instToJsonGoToKind___closed__1();
lean_mark_persistent(l_Lean_Server_instToJsonGoToKind___closed__1);
l_Lean_Server_instToJsonGoToKind = _init_l_Lean_Server_instToJsonGoToKind();
lean_mark_persistent(l_Lean_Server_instToJsonGoToKind);
l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___closed__1 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___closed__1);
l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___closed__2 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__1___closed__2);
l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__1 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__1);
l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__2 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__2);
l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__3 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__2___closed__3);
l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__3___closed__1 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____lambda__3___closed__1);
l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__1 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__1();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__1);
l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__2 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__2();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__2);
l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__3 = _init_l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__3();
lean_mark_persistent(l___private_Lean_Server_GoTo_0__Lean_Server_fromJsonGoToKind____x40_Lean_Server_GoTo___hyg_79____closed__3);
l_Lean_Server_instFromJsonGoToKind___closed__1 = _init_l_Lean_Server_instFromJsonGoToKind___closed__1();
lean_mark_persistent(l_Lean_Server_instFromJsonGoToKind___closed__1);
l_Lean_Server_instFromJsonGoToKind = _init_l_Lean_Server_instFromJsonGoToKind();
lean_mark_persistent(l_Lean_Server_instFromJsonGoToKind);
l_Lean_Server_documentUriFromModule___closed__1 = _init_l_Lean_Server_documentUriFromModule___closed__1();
lean_mark_persistent(l_Lean_Server_documentUriFromModule___closed__1);
l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2___closed__1 = _init_l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2___closed__1();
lean_mark_persistent(l_Lean_findDeclarationRangesCore_x3f___at_Lean_Server_locationLinksFromDecl___spec__2___closed__1);
l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1___closed__1 = _init_l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___lambda__1___closed__1);
l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___closed__1 = _init_l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___closed__1();
lean_mark_persistent(l_Lean_findDeclarationRanges_x3f___at_Lean_Server_locationLinksFromDecl___spec__1___closed__1);
l_Lean_Server_locationLinksFromDecl___lambda__2___closed__1 = _init_l_Lean_Server_locationLinksFromDecl___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_locationLinksFromDecl___lambda__2___closed__1);
l_Lean_Server_locationLinksFromDecl___lambda__2___closed__2 = _init_l_Lean_Server_locationLinksFromDecl___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Server_locationLinksFromDecl___lambda__2___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
