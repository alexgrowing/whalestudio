import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

noncomputable section
namespace GlobalTheory.EtC.SwapTransfer

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.SwapTransfer.negOnePow_sq' (n m : ℤ) :
    (n.negOnePow : ℤ) * ((m.negOnePow : ℤ) * (n.negOnePow : ℤ)) = m.negOnePow := by
  rw [mul_left_comm, ← Units.val_mul, Int.units_mul_self, Units.val_one, mul_one]

def flipPair {I J K : Cx R} (μ : Pair I J K) : Pair J I K where
  mul U t s w h := (((s * t).negOnePow : ℤ) • μ.mul U s t w (by omega)).flip
  nat g t s w h b a := by
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, Sec.res, map_zsmul]
    rw [← Sec.res, μ.nat]
  leibniz U t s w h b a := by
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, Sec.map, map_zsmul]
    rw [← Sec.map, μ.leibniz]
    have h1 : (s * (t + 1)).negOnePow = (s * t).negOnePow * s.negOnePow := by
      rw [mul_add, mul_one, Int.negOnePow_add]
    have h2 : ((s + 1) * t).negOnePow = (s * t).negOnePow * t.negOnePow := by
      rw [add_mul, one_mul, Int.negOnePow_add]
    rw [h1, h2]
    simp only [Units.smul_def, smul_add, smul_smul, Units.val_mul]
    rw [negOnePow_sq']
    exact add_comm _ _

def swIdx {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w}) : {p : ℤ × ℤ // p.1 + p.2 = w} :=
  ⟨(p.1.2, p.1.1), by have := p.2; simp only at this ⊢; omega⟩

def swapT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens J I U w := by
  classical
  exact DirectSum.toModule _ _ _ fun p =>
    ((p.1.1 * p.1.2).negOnePow : ℤ) • ((DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (J.X q.1.1) U ⊗[ULift.{1} R] Sec (I.X q.1.2) U) (swIdx p)) ∘ₗ
      (TensorProduct.comm (ULift.{1} R) (Sec (I.X p.1.1) U) (Sec (J.X p.1.2) U)).toLinearMap)

end GlobalTheory.EtC.SwapTransfer

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem flipPair_mul_eq_negOnePow_smul_mul {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    (_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ).mul U t s w (by omega) b a = (s * t).negOnePow • μ.mul U s t w h a b := by
  rw [Units.smul_def]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem koszulSwap_lof_tmul_lemma_5 (I J : _root_.GlobalTheory.EtC.Cx R) (U : Scheme.{0}) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      (s * t).negOnePow • DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (J.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (I.X q.1.2) U)
          ⟨(t, s), by omega⟩ (b ⊗ₜ a) := by
  unfold _root_.GlobalTheory.EtC.SwapTransfer.swapT
  erw [DirectSum.toModule_lof]
  rw [Units.smul_def]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem lift_lof_tmul {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    μ.lift U w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) = μ.mul U s t w h a b := by
  unfold _root_.GlobalTheory.EtC.Pair.lift
  erw [DirectSum.toModule_lof]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem lift_comp_swapT_eq_flipPair_lift {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) (w : ℤ) :
    μ.lift U w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w =
      (_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ).lift U w := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨t, s⟩, h⟩
  apply TensorProduct.ext'
  intro b a
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, lift_lof_tmul, lift_lof_tmul, Units.smul_def, mul_comm t s]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem swapT_comp_swapT (I J : _root_.GlobalTheory.EtC.Cx R) (U : Scheme.{0}) (w : ℤ) :
    _root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w = LinearMap.id := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, koszulSwap_lof_tmul_lemma_5, smul_smul, mul_comm t s, Int.units_mul_self, one_smul]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem tensorRestrict_lof_tmul_lemma_7 (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}} (g : V ⟶ U) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.Tens.res g w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) V ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) V)
          ⟨(s, t), h⟩ (_root_.GlobalTheory.EtC.Sec.res g a ⊗ₜ _root_.GlobalTheory.EtC.Sec.res g b) := by
  unfold _root_.GlobalTheory.EtC.Tens.res
  erw [DirectSum.lmap_lof]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem res_comp_swapT (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    _root_.GlobalTheory.EtC.Tens.res g w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w =
      _root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w ∘ₗ _root_.GlobalTheory.EtC.Tens.res g w := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, tensorRestrict_lof_tmul_lemma_7, tensorRestrict_lof_tmul_lemma_7, koszulSwap_lof_tmul_lemma_5]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in

theorem _root_.GlobalTheory.EtC.Pair.exists_isFlip (R : Type) [CommRing R]
    {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) :
    ∃ ν : _root_.GlobalTheory.EtC.Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧
      (μ.IsTensor → ν.IsTensor) := by
  refine ⟨_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ, ?_, ?_, ?_⟩
  · intro U s t w h a b
    exact flipPair_mul_eq_negOnePow_smul_mul μ U s t w h a b
  · intro U t s w h b a
    rw [flipPair_mul_eq_negOnePow_smul_mul μ U s t w (by omega) a b, smul_smul, mul_comm t s, Int.units_mul_self, one_smul]
  · rintro ⟨hsurj, hinj⟩
    refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
    · obtain ⟨S, hS, hP⟩ := hsurj U w y
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨x, hx⟩ := hP V g hg
      refine ⟨_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w x, ?_⟩
      rw [← lift_comp_swapT_eq_flipPair_lift, LinearMap.comp_apply, ← LinearMap.comp_apply (_root_.GlobalTheory.EtC.SwapTransfer.swapT J I V w), swapT_comp_swapT, LinearMap.id_apply]
      exact hx
    · have hx' : μ.lift U w (_root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w x) = 0 := by
        rw [← LinearMap.comp_apply, lift_comp_swapT_eq_flipPair_lift]
        exact hx
      obtain ⟨S, hS, hP⟩ := hinj U w _ hx'
      refine ⟨S, hS, fun V g hg => ?_⟩
      have hV := congrArg (_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w) (hP V g hg)
      rw [← LinearMap.comp_apply (_root_.GlobalTheory.EtC.Tens.res g w), res_comp_swapT, LinearMap.comp_apply,
        ← LinearMap.comp_apply (_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w), swapT_comp_swapT, LinearMap.id_apply, map_zero] at hV
      exact hV

end GlobalTheory.EtC

end
