import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.HermLineZeros

section Ring

variable {A : Type} [CommRing A] {M : ℕ}

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {A : Type} [CommRing A] {M : ℕ} in
theorem _root_.GlobalTheory.HermLineZeros.hform_expand (s : A →+* A) (J : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) (c : A) :
    _root_.Formalism.UG.hform s J (x + c • y) (x + c • y) =
      _root_.Formalism.UG.hform s J x x + c * _root_.Formalism.UG.hform s J x y + s c * _root_.Formalism.UG.hform s J y x
        + s c * c * _root_.Formalism.UG.hform s J y y := by
  unfold _root_.Formalism.UG.hform
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {A : Type} [CommRing A] {M : ℕ} in
theorem _root_.GlobalTheory.HermLineZeros.hform_single (s : A →+* A) (J : Matrix (Fin M) (Fin M) A)
    (i j : Fin M) :
    _root_.Formalism.UG.hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [_root_.Formalism.UG.hform, Pi.single_apply, apply_ite s]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.HermLineZeros.conj_invol (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.HermLineZeros.exists_conj_ne (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : ∃ d, σ d ≠ d := by
  by_contra! hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx := h.2.2.2 τ x
    rw [hσ x] at hx
    simpa [ComplexEmbedding.conjugate_coe_eq] using hx.symm
  have hcx := (h.2.1).isComplex (InfinitePlace.mk τ)
  rw [InfinitePlace.isComplex_mk_iff] at hcx
  exact hcx hreal

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.HermLineZeros.exists_of_fixed (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ f, algebraMap F E f = e := by
  obtain ⟨d, hd⟩ := _root_.GlobalTheory.HermLineZeros.exists_conj_ne h
  let S : Subalgebra F E := AlgHom.equalizer σ (AlgHom.id F E)
  have hS : S ≠ ⊤ := by
    intro hS
    have hdS : d ∈ S := hS ▸ Algebra.mem_top
    exact hd hdS
  have hle : Module.finrank F S ≤ 2 :=
    h.2.2.1 ▸ Submodule.finrank_le (Subalgebra.toSubmodule S)
  have hne : Module.finrank F S ≠ 2 := by
    intro h2
    apply hS
    apply Subalgebra.toSubmodule.injective
    rw [Algebra.top_toSubmodule]
    exact Submodule.eq_top_of_finrank_eq (h2.trans h.2.2.1.symm)
  have hpos : 0 < Module.finrank F S := Module.finrank_pos
  have hbot : S = ⊥ := Subalgebra.finrank_eq_one_iff.mp (by omega)
  have heS : e ∈ S := he
  rw [hbot] at heS
  exact Algebra.mem_bot.mp heS

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
private theorem hE_self_conj_fixed (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) (v : Fin M → E) :
    σ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J v v) = _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J v v := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE _root_.Formalism.UG.hform
  rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [AlgHom.coe_toRingHom, map_mul, _root_.GlobalTheory.HermLineZeros.conj_invol h, hJ.1]
  ring

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.HermLineZeros.exists_anisotropic (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {M : ℕ} (hM : 1 ≤ M)
    {J : Matrix (Fin M) (Fin M) E} (hJ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) :
    ∃ (y : Fin M → E) (a : F), a ≠ 0 ∧ _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y y = algebraMap F E a := by
  suffices hv : ∃ v, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J v v ≠ 0 by
    obtain ⟨v, hv⟩ := hv
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.HermLineZeros.exists_of_fixed h _ (hE_self_conj_fixed h hJ v)
    refine ⟨v, a, ?_, ha.symm⟩
    rintro rfl
    exact hv (by rw [← ha, map_zero])
  by_cases hd : ∃ i, J i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    exact ⟨Pi.single i 1, by rwa [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, _root_.GlobalTheory.HermLineZeros.hform_single]⟩
  push_neg at hd
  let i₀ : Fin M := ⟨0, hM⟩
  obtain ⟨j, hj⟩ : ∃ j, J i₀ j ≠ 0 := by
    by_contra! hrow
    exact hJ.2 (Matrix.det_eq_zero_of_row_eq_zero i₀ hrow)
  refine ⟨Pi.single i₀ 1 + (J i₀ j)⁻¹ • Pi.single j 1, ?_⟩
  have hji : J j i₀ = σ (J i₀ j) := (hJ.1 j i₀).symm
  rw [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, _root_.GlobalTheory.HermLineZeros.hform_expand, _root_.GlobalTheory.HermLineZeros.hform_single,
    _root_.GlobalTheory.HermLineZeros.hform_single, _root_.GlobalTheory.HermLineZeros.hform_single,
    _root_.GlobalTheory.HermLineZeros.hform_single, hd, hd, hji]
  simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]
  rw [inv_mul_cancel₀ hj, ← map_mul, inv_mul_cancel₀ hj, map_one]
  norm_num

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in

theorem _root_.GlobalTheory.HermLineZeros.finite_zeros_on_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K], ∃ y : Fin M → K ⊗[F] E, ∀ x : Fin M → K ⊗[F] E, {t : K | _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR K σ J (x + t • y) = 0}.Finite := by
  intro F E _ _ _ _ _ σ h M hM J hJ K _ _
  obtain ⟨y₀, a, ha, hy⟩ := _root_.GlobalTheory.HermLineZeros.exists_anisotropic h hM hJ
  let φ : E →ₐ[F] K ⊗[F] E := Algebra.TensorProduct.includeRight
  let S := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR K σ
  let JR := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := F) K J
  set y : Fin M → K ⊗[F] E := fun i => φ (y₀ i)
  refine ⟨y, fun x => ?_⟩
  have hSc : ∀ t : K, S (algebraMap K (K ⊗[F] E) t) = algebraMap K (K ⊗[F] E) t := fun t => by
    simp [S, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]
  have hSφ : ∀ e : E, S (φ e) = φ (σ e) := fun e => by simp [S, φ, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  have hyy : _root_.Formalism.UG.hform S JR y y = algebraMap K (K ⊗[F] E) (algebraMap F K a) := by
    rw [← IsScalarTower.algebraMap_apply, ← φ.commutes, ← hy]
    simp only [_root_.Formalism.UG.hform, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, map_sum, map_mul, y, hSφ, JR, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
    rfl
  have htr : Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR y y)
      = Module.finrank K (K ⊗[F] E) • algebraMap F K a := by
    rw [hyy, Algebra.trace_algebraMap]
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hfr : Module.finrank K (K ⊗[F] E) ≠ 0 := by
    rw [Module.finrank_baseChange, h.2.2.1]; norm_num
  set α := algebraMap F K (1 / 2) * Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR y y) with hα
  set β := algebraMap F K (1 / 2) * Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR x y + _root_.Formalism.UG.hform S JR y x)
  set γ := algebraMap F K (1 / 2) * Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR x x)
  have hα0 : α ≠ 0 := by
    rw [hα, htr]
    refine mul_ne_zero ?_ (smul_ne_zero hfr ?_)
    · rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; norm_num
    · rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact ha
  let p : Polynomial K := Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ
  have hp : p ≠ 0 := by
    intro hp
    have := congrArg (Polynomial.coeff · 2) hp
    simp [p, Polynomial.coeff_X, Polynomial.coeff_C] at this
    exact hα0 this
  refine (Polynomial.finite_setOf_isRoot hp).subset fun t ht => ?_
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [Polynomial.IsRoot.def, ← ht]
  have hsmul : t • y = algebraMap K (K ⊗[F] E) t • y := by
    funext i; simp [Algebra.smul_def]
  have hexp := _root_.GlobalTheory.HermLineZeros.hform_expand S JR x y (algebraMap K (K ⊗[F] E) t)
  rw [hSc] at hexp
  have hq : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR K σ J (x + t • y) = algebraMap F K (1 / 2) *
      Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR (x + algebraMap K (K ⊗[F] E) t • y)
        (x + algebraMap K (K ⊗[F] E) t • y)) := by
    rw [← hsmul]; rfl
  have htc : ∀ z, Algebra.trace K (K ⊗[F] E) (algebraMap K (K ⊗[F] E) t * z)
      = t * Algebra.trace K (K ⊗[F] E) z := fun z => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [hq, hexp, mul_assoc (algebraMap K (K ⊗[F] E) t), map_add, map_add, map_add, htc, htc, htc, htc]
  simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, α, β, γ, map_add]
  ring

end GlobalTheory.HermLineZeros
