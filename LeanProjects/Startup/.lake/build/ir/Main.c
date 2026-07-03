// Lean compiler output
// Module: Main
// Imports: public import Init public meta import Init public import MyProject.Basic public import MyProject.Theorems
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lp_myProject_MyProject_factorial(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_get_stdout();
lean_object* lp_myProject_MyProject_double(lean_object*);
lean_object* lp_myProject_MyProject_fibonacci(lean_object*);
static const lean_string_object lp_myProject_List_foldl___at___00List_toString___at___00main_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* lp_myProject_List_foldl___at___00List_toString___at___00main_spec__1_spec__2___closed__0 = (const lean_object*)&lp_myProject_List_foldl___at___00List_toString___at___00main_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* lp_myProject_List_foldl___at___00List_toString___at___00main_spec__1_spec__2(lean_object*, lean_object*);
static const lean_string_object lp_myProject_List_toString___at___00main_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* lp_myProject_List_toString___at___00main_spec__1___closed__0 = (const lean_object*)&lp_myProject_List_toString___at___00main_spec__1___closed__0_value;
static const lean_string_object lp_myProject_List_toString___at___00main_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_myProject_List_toString___at___00main_spec__1___closed__1 = (const lean_object*)&lp_myProject_List_toString___at___00main_spec__1___closed__1_value;
static const lean_string_object lp_myProject_List_toString___at___00main_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_myProject_List_toString___at___00main_spec__1___closed__2 = (const lean_object*)&lp_myProject_List_toString___at___00main_spec__1___closed__2_value;
LEAN_EXPORT lean_object* lp_myProject_List_toString___at___00main_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_myProject_List_foldl___at___00main_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_myProject_List_foldl___at___00main_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_myProject_List_foldl___at___00main_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_myProject_List_foldl___at___00main_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_myProject_IO_print___at___00IO_println___at___00main_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_myProject_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_myProject_IO_println___at___00main_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_myProject_IO_println___at___00main_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object lp_myProject_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 22, .m_data = "=== 欢迎来到 Lean 4 项目！==="};
static const lean_object* lp_myProject_main___closed__0 = (const lean_object*)&lp_myProject_main___closed__0_value;
static const lean_string_object lp_myProject_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* lp_myProject_main___closed__1 = (const lean_object*)&lp_myProject_main___closed__1_value;
static const lean_string_object lp_myProject_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 6, .m_data = "【基本运算】"};
static const lean_object* lp_myProject_main___closed__2 = (const lean_object*)&lp_myProject_main___closed__2_value;
static const lean_string_object lp_myProject_main___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "  double 5     = "};
static const lean_object* lp_myProject_main___closed__3 = (const lean_object*)&lp_myProject_main___closed__3_value;
static lean_once_cell_t lp_myProject_main___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__4;
static lean_once_cell_t lp_myProject_main___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__5;
static lean_once_cell_t lp_myProject_main___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__6;
static const lean_string_object lp_myProject_main___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "  factorial 6  = "};
static const lean_object* lp_myProject_main___closed__7 = (const lean_object*)&lp_myProject_main___closed__7_value;
static lean_once_cell_t lp_myProject_main___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__8;
static lean_once_cell_t lp_myProject_main___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__9;
static lean_once_cell_t lp_myProject_main___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__10;
static const lean_string_object lp_myProject_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "  fibonacci 10 = "};
static const lean_object* lp_myProject_main___closed__11 = (const lean_object*)&lp_myProject_main___closed__11_value;
static lean_once_cell_t lp_myProject_main___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__12;
static lean_once_cell_t lp_myProject_main___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__13;
static lean_once_cell_t lp_myProject_main___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__14;
static const lean_string_object lp_myProject_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 6, .m_data = "【列表操作】"};
static const lean_object* lp_myProject_main___closed__15 = (const lean_object*)&lp_myProject_main___closed__15_value;
static const lean_ctor_object lp_myProject_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_myProject_main___closed__16 = (const lean_object*)&lp_myProject_main___closed__16_value;
static const lean_ctor_object lp_myProject_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)&lp_myProject_main___closed__16_value)}};
static const lean_object* lp_myProject_main___closed__17 = (const lean_object*)&lp_myProject_main___closed__17_value;
static const lean_ctor_object lp_myProject_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1)),((lean_object*)&lp_myProject_main___closed__17_value)}};
static const lean_object* lp_myProject_main___closed__18 = (const lean_object*)&lp_myProject_main___closed__18_value;
static const lean_ctor_object lp_myProject_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&lp_myProject_main___closed__18_value)}};
static const lean_object* lp_myProject_main___closed__19 = (const lean_object*)&lp_myProject_main___closed__19_value;
static const lean_ctor_object lp_myProject_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)&lp_myProject_main___closed__19_value)}};
static const lean_object* lp_myProject_main___closed__20 = (const lean_object*)&lp_myProject_main___closed__20_value;
static const lean_ctor_object lp_myProject_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)&lp_myProject_main___closed__20_value)}};
static const lean_object* lp_myProject_main___closed__21 = (const lean_object*)&lp_myProject_main___closed__21_value;
static const lean_ctor_object lp_myProject_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&lp_myProject_main___closed__21_value)}};
static const lean_object* lp_myProject_main___closed__22 = (const lean_object*)&lp_myProject_main___closed__22_value;
static const lean_ctor_object lp_myProject_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&lp_myProject_main___closed__22_value)}};
static const lean_object* lp_myProject_main___closed__23 = (const lean_object*)&lp_myProject_main___closed__23_value;
static const lean_ctor_object lp_myProject_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&lp_myProject_main___closed__23_value)}};
static const lean_object* lp_myProject_main___closed__24 = (const lean_object*)&lp_myProject_main___closed__24_value;
static const lean_ctor_object lp_myProject_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&lp_myProject_main___closed__24_value)}};
static const lean_object* lp_myProject_main___closed__25 = (const lean_object*)&lp_myProject_main___closed__25_value;
static const lean_string_object lp_myProject_main___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 8, .m_data = "  原始列表: "};
static const lean_object* lp_myProject_main___closed__26 = (const lean_object*)&lp_myProject_main___closed__26_value;
static lean_once_cell_t lp_myProject_main___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__27;
static lean_once_cell_t lp_myProject_main___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__28;
static const lean_string_object lp_myProject_main___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 6, .m_data = "  总和: "};
static const lean_object* lp_myProject_main___closed__29 = (const lean_object*)&lp_myProject_main___closed__29_value;
static lean_once_cell_t lp_myProject_main___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__30;
static lean_once_cell_t lp_myProject_main___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__31;
static lean_once_cell_t lp_myProject_main___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__32;
static const lean_string_object lp_myProject_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 7, .m_data = "  最大值: "};
static const lean_object* lp_myProject_main___closed__33 = (const lean_object*)&lp_myProject_main___closed__33_value;
static lean_once_cell_t lp_myProject_main___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__34;
static lean_once_cell_t lp_myProject_main___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__35;
static lean_once_cell_t lp_myProject_main___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_myProject_main___closed__36;
static const lean_string_object lp_myProject_main___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 14, .m_data = "Lean 4 项目运行成功！"};
static const lean_object* lp_myProject_main___closed__37 = (const lean_object*)&lp_myProject_main___closed__37_value;
LEAN_EXPORT lean_object* _lean_main();
LEAN_EXPORT lean_object* lp_myProject_main___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_myProject_List_foldl___at___00List_toString___at___00main_spec__1_spec__2(lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
return v_x_2_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_head_4_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_head_4_);
v_tail_5_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_tail_5_);
lean_dec_ref(v_x_3_);
v___x_6_ = ((lean_object*)(lp_myProject_List_foldl___at___00List_toString___at___00main_spec__1_spec__2___closed__0));
v___x_7_ = lean_string_append(v_x_2_, v___x_6_);
v___x_8_ = l_Nat_reprFast(v_head_4_);
v___x_9_ = lean_string_append(v___x_7_, v___x_8_);
lean_dec_ref(v___x_8_);
v_x_2_ = v___x_9_;
v_x_3_ = v_tail_5_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_myProject_List_toString___at___00main_spec__1(lean_object* v_x_14_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(lp_myProject_List_toString___at___00main_spec__1___closed__0));
return v___x_15_;
}
else
{
lean_object* v_tail_16_; 
v_tail_16_ = lean_ctor_get(v_x_14_, 1);
if (lean_obj_tag(v_tail_16_) == 0)
{
lean_object* v_head_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_head_17_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_head_17_);
lean_dec_ref(v_x_14_);
v___x_18_ = ((lean_object*)(lp_myProject_List_toString___at___00main_spec__1___closed__1));
v___x_19_ = l_Nat_reprFast(v_head_17_);
v___x_20_ = lean_string_append(v___x_18_, v___x_19_);
lean_dec_ref(v___x_19_);
v___x_21_ = ((lean_object*)(lp_myProject_List_toString___at___00main_spec__1___closed__2));
v___x_22_ = lean_string_append(v___x_20_, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_head_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint32_t v___x_28_; lean_object* v___x_29_; 
lean_inc(v_tail_16_);
v_head_23_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_head_23_);
lean_dec_ref(v_x_14_);
v___x_24_ = ((lean_object*)(lp_myProject_List_toString___at___00main_spec__1___closed__1));
v___x_25_ = l_Nat_reprFast(v_head_23_);
v___x_26_ = lean_string_append(v___x_24_, v___x_25_);
lean_dec_ref(v___x_25_);
v___x_27_ = lp_myProject_List_foldl___at___00List_toString___at___00main_spec__1_spec__2(v___x_26_, v_tail_16_);
v___x_28_ = 93;
v___x_29_ = lean_string_push(v___x_27_, v___x_28_);
return v___x_29_;
}
}
}
}
LEAN_EXPORT lean_object* lp_myProject_List_foldl___at___00main_spec__3(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
if (lean_obj_tag(v_x_31_) == 0)
{
lean_inc(v_x_30_);
return v_x_30_;
}
else
{
lean_object* v_head_32_; lean_object* v_tail_33_; uint8_t v___x_34_; 
v_head_32_ = lean_ctor_get(v_x_31_, 0);
v_tail_33_ = lean_ctor_get(v_x_31_, 1);
v___x_34_ = lean_nat_dec_le(v_x_30_, v_head_32_);
if (v___x_34_ == 0)
{
v_x_31_ = v_tail_33_;
goto _start;
}
else
{
v_x_30_ = v_head_32_;
v_x_31_ = v_tail_33_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_myProject_List_foldl___at___00main_spec__3___boxed(lean_object* v_x_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_myProject_List_foldl___at___00main_spec__3(v_x_37_, v_x_38_);
lean_dec(v_x_38_);
lean_dec(v_x_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_myProject_List_foldl___at___00main_spec__2(lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
if (lean_obj_tag(v_x_41_) == 0)
{
return v_x_40_;
}
else
{
lean_object* v_head_42_; lean_object* v_tail_43_; lean_object* v___x_44_; 
v_head_42_ = lean_ctor_get(v_x_41_, 0);
v_tail_43_ = lean_ctor_get(v_x_41_, 1);
v___x_44_ = lean_nat_add(v_x_40_, v_head_42_);
lean_dec(v_x_40_);
v_x_40_ = v___x_44_;
v_x_41_ = v_tail_43_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_myProject_List_foldl___at___00main_spec__2___boxed(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_myProject_List_foldl___at___00main_spec__2(v_x_46_, v_x_47_);
lean_dec(v_x_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_myProject_IO_print___at___00IO_println___at___00main_spec__0_spec__0(lean_object* v_s_49_){
_start:
{
lean_object* v___x_51_; lean_object* v_putStr_52_; lean_object* v___x_53_; 
v___x_51_ = lean_get_stdout();
v_putStr_52_ = lean_ctor_get(v___x_51_, 4);
lean_inc_ref(v_putStr_52_);
lean_dec_ref(v___x_51_);
v___x_53_ = lean_apply_2(v_putStr_52_, v_s_49_, lean_box(0));
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_myProject_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(lean_object* v_s_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_myProject_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lp_myProject_IO_println___at___00main_spec__0(lean_object* v_s_57_){
_start:
{
uint32_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = 10;
v___x_60_ = lean_string_push(v_s_57_, v___x_59_);
v___x_61_ = lp_myProject_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_myProject_IO_println___at___00main_spec__0___boxed(lean_object* v_s_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_myProject_IO_println___at___00main_spec__0(v_s_62_);
return v_res_64_;
}
}
static lean_object* _init_lp_myProject_main___closed__4(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(5u);
v___x_70_ = lp_myProject_MyProject_double(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_lp_myProject_main___closed__5(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_obj_once(&lp_myProject_main___closed__4, &lp_myProject_main___closed__4_once, _init_lp_myProject_main___closed__4);
v___x_72_ = l_Nat_reprFast(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_lp_myProject_main___closed__6(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_obj_once(&lp_myProject_main___closed__5, &lp_myProject_main___closed__5_once, _init_lp_myProject_main___closed__5);
v___x_74_ = ((lean_object*)(lp_myProject_main___closed__3));
v___x_75_ = lean_string_append(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_lp_myProject_main___closed__8(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(6u);
v___x_78_ = lp_myProject_MyProject_factorial(v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_lp_myProject_main___closed__9(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_obj_once(&lp_myProject_main___closed__8, &lp_myProject_main___closed__8_once, _init_lp_myProject_main___closed__8);
v___x_80_ = l_Nat_reprFast(v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_lp_myProject_main___closed__10(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_obj_once(&lp_myProject_main___closed__9, &lp_myProject_main___closed__9_once, _init_lp_myProject_main___closed__9);
v___x_82_ = ((lean_object*)(lp_myProject_main___closed__7));
v___x_83_ = lean_string_append(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_lp_myProject_main___closed__12(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(10u);
v___x_86_ = lp_myProject_MyProject_fibonacci(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_lp_myProject_main___closed__13(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_obj_once(&lp_myProject_main___closed__12, &lp_myProject_main___closed__12_once, _init_lp_myProject_main___closed__12);
v___x_88_ = l_Nat_reprFast(v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_lp_myProject_main___closed__14(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&lp_myProject_main___closed__13, &lp_myProject_main___closed__13_once, _init_lp_myProject_main___closed__13);
v___x_90_ = ((lean_object*)(lp_myProject_main___closed__11));
v___x_91_ = lean_string_append(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_lp_myProject_main___closed__27(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = ((lean_object*)(lp_myProject_main___closed__25));
v___x_125_ = lp_myProject_List_toString___at___00main_spec__1(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_lp_myProject_main___closed__28(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_obj_once(&lp_myProject_main___closed__27, &lp_myProject_main___closed__27_once, _init_lp_myProject_main___closed__27);
v___x_127_ = ((lean_object*)(lp_myProject_main___closed__26));
v___x_128_ = lean_string_append(v___x_127_, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_lp_myProject_main___closed__30(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = ((lean_object*)(lp_myProject_main___closed__25));
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lp_myProject_List_foldl___at___00main_spec__2(v___x_131_, v___x_130_);
return v___x_132_;
}
}
static lean_object* _init_lp_myProject_main___closed__31(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_obj_once(&lp_myProject_main___closed__30, &lp_myProject_main___closed__30_once, _init_lp_myProject_main___closed__30);
v___x_134_ = l_Nat_reprFast(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_lp_myProject_main___closed__32(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_obj_once(&lp_myProject_main___closed__31, &lp_myProject_main___closed__31_once, _init_lp_myProject_main___closed__31);
v___x_136_ = ((lean_object*)(lp_myProject_main___closed__29));
v___x_137_ = lean_string_append(v___x_136_, v___x_135_);
return v___x_137_;
}
}
static lean_object* _init_lp_myProject_main___closed__34(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = ((lean_object*)(lp_myProject_main___closed__25));
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lp_myProject_List_foldl___at___00main_spec__3(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_lp_myProject_main___closed__35(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_obj_once(&lp_myProject_main___closed__34, &lp_myProject_main___closed__34_once, _init_lp_myProject_main___closed__34);
v___x_143_ = l_Nat_reprFast(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_lp_myProject_main___closed__36(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&lp_myProject_main___closed__35, &lp_myProject_main___closed__35_once, _init_lp_myProject_main___closed__35);
v___x_145_ = ((lean_object*)(lp_myProject_main___closed__33));
v___x_146_ = lean_string_append(v___x_145_, v___x_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* _lean_main(){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(lp_myProject_main___closed__0));
v___x_150_ = lp_myProject_IO_println___at___00main_spec__0(v___x_149_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec_ref(v___x_150_);
v___x_151_ = ((lean_object*)(lp_myProject_main___closed__1));
v___x_152_ = lp_myProject_IO_println___at___00main_spec__0(v___x_151_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref(v___x_152_);
v___x_153_ = ((lean_object*)(lp_myProject_main___closed__2));
v___x_154_ = lp_myProject_IO_println___at___00main_spec__0(v___x_153_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec_ref(v___x_154_);
v___x_155_ = lean_obj_once(&lp_myProject_main___closed__6, &lp_myProject_main___closed__6_once, _init_lp_myProject_main___closed__6);
v___x_156_ = lp_myProject_IO_println___at___00main_spec__0(v___x_155_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec_ref(v___x_156_);
v___x_157_ = lean_obj_once(&lp_myProject_main___closed__10, &lp_myProject_main___closed__10_once, _init_lp_myProject_main___closed__10);
v___x_158_ = lp_myProject_IO_println___at___00main_spec__0(v___x_157_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec_ref(v___x_158_);
v___x_159_ = lean_obj_once(&lp_myProject_main___closed__14, &lp_myProject_main___closed__14_once, _init_lp_myProject_main___closed__14);
v___x_160_ = lp_myProject_IO_println___at___00main_spec__0(v___x_159_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v___x_161_; 
lean_dec_ref(v___x_160_);
v___x_161_ = lp_myProject_IO_println___at___00main_spec__0(v___x_151_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec_ref(v___x_161_);
v___x_162_ = ((lean_object*)(lp_myProject_main___closed__15));
v___x_163_ = lp_myProject_IO_println___at___00main_spec__0(v___x_162_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec_ref(v___x_163_);
v___x_164_ = lean_obj_once(&lp_myProject_main___closed__28, &lp_myProject_main___closed__28_once, _init_lp_myProject_main___closed__28);
v___x_165_ = lp_myProject_IO_println___at___00main_spec__0(v___x_164_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec_ref(v___x_165_);
v___x_166_ = lean_obj_once(&lp_myProject_main___closed__32, &lp_myProject_main___closed__32_once, _init_lp_myProject_main___closed__32);
v___x_167_ = lp_myProject_IO_println___at___00main_spec__0(v___x_166_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec_ref(v___x_167_);
v___x_168_ = lean_obj_once(&lp_myProject_main___closed__36, &lp_myProject_main___closed__36_once, _init_lp_myProject_main___closed__36);
v___x_169_ = lp_myProject_IO_println___at___00main_spec__0(v___x_168_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v___x_170_; 
lean_dec_ref(v___x_169_);
v___x_170_ = lp_myProject_IO_println___at___00main_spec__0(v___x_151_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec_ref(v___x_170_);
v___x_171_ = ((lean_object*)(lp_myProject_main___closed__37));
v___x_172_ = lp_myProject_IO_println___at___00main_spec__0(v___x_171_);
return v___x_172_;
}
else
{
return v___x_170_;
}
}
else
{
return v___x_169_;
}
}
else
{
return v___x_167_;
}
}
else
{
return v___x_165_;
}
}
else
{
return v___x_163_;
}
}
else
{
return v___x_161_;
}
}
else
{
return v___x_160_;
}
}
else
{
return v___x_158_;
}
}
else
{
return v___x_156_;
}
}
else
{
return v___x_154_;
}
}
else
{
return v___x_152_;
}
}
else
{
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* lp_myProject_main___boxed(lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = _lean_main();
return v_res_174_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_myProject_MyProject_Basic(uint8_t builtin);
lean_object* initialize_myProject_MyProject_Theorems(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_myProject_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_myProject_MyProject_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_myProject_MyProject_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
void lean_initialize_runtime_module();
#if defined(WIN32) || defined(_WIN32)
#include <windows.h>
#endif
lean_object* run_main(int argc, char ** argv) {
    return _lean_main();
}
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* res;
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  res = initialize_myProject_Main(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_ok(res)) {
    int ret = 0;
    lean_dec_ref(res);
    return ret;
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
}
#ifdef __cplusplus
}
#endif
