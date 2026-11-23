import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE

open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.Model

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}

open NumberField in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
theorem _root_.GlobalTheory.TestLat.Model.mem_sumLat (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (T : C → Submodule (𝓞 K) (_root_.Formalism.L2.DIV.VV K lam))
    (u : Fin N → K) : u ∈ _root_.GlobalTheory.TestLat.sumLat lam e T ↔
      ∀ c, _root_.GlobalTheory.TestLat.valAt lam e c u ∈ T c := by
  simp only [_root_.GlobalTheory.TestLat.sumLat, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

omit [NumberField K] in
theorem valAt_apply (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) (c : C) (u : Fin N → K) :
    valAt lam e c u = ∑ i, u (e.symm (c, i)) • bVV K lam i := by
  simp [valAt, Module.Basis.equivFun_symm_apply, LinearMap.funLeft_apply]

open NumberField in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
omit [NumberField K] in

theorem _root_.GlobalTheory.TestLat.Model.valAt_bijective (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam) :
    Function.Bijective fun (u : Fin N → K) (c : C) => _root_.GlobalTheory.TestLat.valAt lam e c u := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun f a => (_root_.Formalism.L2.DIV.bVV K lam).equivFun (f (e a).1) (e a).2, fun u => ?_, fun f => ?_⟩
  · ext a
    simp only [_root_.GlobalTheory.TestLat.valAt, LinearMap.comp_apply, LinearMap.funLeft_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Prod.mk.eta, Equiv.symm_apply_apply]
  · ext c
    simp [_root_.GlobalTheory.TestLat.valAt, LinearMap.funLeft_apply]

open NumberField in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
omit [NumberField K] in

theorem _root_.GlobalTheory.TestLat.Model.sumGram_form [StarRing K] [Fintype C] (lam : ι → _root_.Formalism.BasicNotions.DomWeight n)
    (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (G : ι → Matrix (Fin n) (Fin n) K) (u w : Fin N → K) :
    star u ⬝ᵥ (_root_.GlobalTheory.TestLat.sumGram lam e G *ᵥ w) =
      ∑ c, _root_.Formalism.L2.DIV.pairK lam G (_root_.GlobalTheory.TestLat.valAt lam e c u)
        (_root_.GlobalTheory.TestLat.valAt lam e c w) := by
  classical
  simp only [dotProduct, Matrix.mulVec, _root_.GlobalTheory.TestLat.sumGram, Matrix.of_apply, Pi.star_apply]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [_root_.GlobalTheory.TestLat.valAt, LinearMap.comp_apply, LinearMap.funLeft_apply,
    LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply, map_sum, map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single c (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [if_pos rfl]
  simp only [RingHom.id_apply, starRingEnd_apply]
  ring

theorem isMetric_one : IsMetric (1 : Matrix (Fin N) (Fin N) K) fun _ => 1 := by
  intro v
  simp

theorem isMetric_four : IsMetric ((4 : K) • (1 : Matrix (Fin 1) (Fin 1) K))
    fun _ => (2⁻¹ : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  intro v
  have h : ((2⁻¹ : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ))⁻¹ = (2 : ℂ) • 1 := by
    apply Matrix.inv_eq_left_inv
    simp [smul_smul]
  refine ⟨by simp, ?_⟩
  simp only [h]
  ext a b
  fin_cases a; fin_cases b
  simp [Matrix.mul_apply, map_ofNat]
  norm_num

theorem not_isMetric_zero (X : InfinitePlace K → Matrix (Fin 1) (Fin 1) ℂ) : ¬ IsMetric (0 : Matrix (Fin 1) (Fin 1) K) X := by
  intro h
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  obtain ⟨h1, h2⟩ := h v
  have h3 := congrArg Matrix.det h2
  have h4 : (X v)⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det _ h1).ne_zero
  rw [Matrix.det_mul, Matrix.det_conjTranspose] at h3
  simp only [Matrix.map_zero _ (map_zero _), Matrix.det_zero, mul_eq_zero, star_eq_zero, or_self] at h3
  exact h4 h3

omit [NumberField K] in
theorem isDefGram_one [StarRing K] : IsDefGram (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro a b
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro φ
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.PosDef.one

def stdLat (K : Type) [Field K] [NumberField K] (n : ℕ) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))

theorem mem_stdLat (x : Fin n → K) : x ∈ stdLat K n ↔ ∀ a, x a ∈ (algebraMap (𝓞 K) K).range := by
  rw [stdLat, Module.Basis.mem_span_iff_repr_mem]
  simp

theorem isLattice_stdLat : Submodule.IsLattice K (stdLat K n) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [stdLat, Submodule.span_span_of_tower]
    exact (Pi.basisFun K (Fin n)).span_eq

theorem map_mem_range (σ : K →+* K) {x : K} (hx : x ∈ (algebraMap (𝓞 K) K).range) :
    σ x ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨σ y, (RingOfIntegers.isIntegral_coe y).map σ.toIntAlgHom⟩, rfl⟩

theorem isSelfDualE_std (σ : K →+* K) : IsSelfDualE σ (1 : Matrix (Fin n) (Fin n) K) (stdLat K n) := by
  refine ⟨isLattice_stdLat, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [mem_stdLat] at hx hy
    refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
    refine Subring.mul_mem _ (Subring.mul_mem _ (map_mem_range σ (hx i)) ?_) (hy j)
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [mem_stdLat]
    intro a
    have := h (Pi.single a 1) (by
      rw [mem_stdLat]; intro b; rw [Pi.single_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _)
    simpa [Formalism.UG.hform, Matrix.one_apply, Pi.single_apply, apply_ite σ] using this

theorem isSelfDualK_std [StarRing K] : IsSelfDualK (1 : Matrix (Fin n) (Fin n) K) (stdLat K n) := by
  refine ⟨isLattice_stdLat, ?_⟩
  ext y
  rw [(isSelfDualE_std (starRingEnd K)).2 y]
  change (∀ x ∈ stdLat K n, _) ↔ _
  refine forall₂_congr fun x _ => ?_
  simp [Formalism.UG.hform, Matrix.one_apply, dotProduct, Submodule.mem_one, starRingEnd_apply]

theorem not_isSelfDualE_two (σ : K →+* K) :
    ¬ IsSelfDualE σ (1 : Matrix (Fin 1) (Fin 1) K) (Submodule.span (𝓞 K) {fun _ => (2 : K)}) := by
  intro h
  have h1 : (fun _ => (1 : K)) ∈ (Submodule.span (𝓞 K) {fun _ : Fin 1 => (2 : K)}) := by
    rw [h.2]
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have : Formalism.UG.hform σ (1 : Matrix (Fin 1) (Fin 1) K) (a • fun _ => (2 : K)) (fun _ => 1) =
        σ (algebraMap (𝓞 K) K (a * 2)) := by
      simp [Formalism.UG.hform, Algebra.smul_def, map_ofNat]
    rw [this]
    exact map_mem_range σ ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  have h2 : algebraMap (𝓞 K) K a * 2 = 1 := by simpa [Algebra.smul_def] using congrFun ha 0
  have h3 : IsIntegral ℤ (algebraMap ℚ K 2⁻¹) := by
    have : algebraMap ℚ K 2⁻¹ = algebraMap (𝓞 K) K a := by
      rw [map_inv₀, map_ofNat]
      exact (eq_inv_of_mul_eq_one_left h2).symm
    rw [this]
    exact RingOfIntegers.isIntegral_coe a
  rw [isIntegral_algebraMap_iff (algebraMap ℚ K).injective] at h3
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have h4 : (z : ℚ) * 2 = 1 := by
    have : (z : ℚ) = 2⁻¹ := hz
    rw [this]; norm_num
  have h5 : z * 2 = 1 := by exact_mod_cast h4
  omega

def wOne : DomWeight 2 := ⟨![1, 0], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

theorem spreadLe_wOne (R : ℝ) : SpreadLe (fun _ : Unit => wOne) R ↔ 1 ≤ R := by
  constructor
  · intro h
    simpa [wOne] using h () 0 1
  · intro h _ i j
    fin_cases i <;> fin_cases j <;> simp [wOne] <;> linarith

theorem bound_one_two : bound 1 2 1 = 8 * Real.log 2 := by
  simp [bound]; norm_num

end GlobalTheory.TestLat.Model
