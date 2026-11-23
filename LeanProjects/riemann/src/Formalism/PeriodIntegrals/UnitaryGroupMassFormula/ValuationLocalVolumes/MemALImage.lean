import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUHerm

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolV

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def aL (g : Fv F v) (θ : Fv F v ⊗[F] E) : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
  LinearMap.id + (g - 1) • (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)).smulRight θ

theorem aL_apply (g : Fv F v) (θ z : Fv F v ⊗[F] E) :
    aL v g θ z = z + ((g - 1) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z) • θ := by
  simp [aL, LinearMap.smulRight_apply, smul_smul]

theorem trace_aL (g : Fv F v) (θ z : Fv F v ⊗[F] E) (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (aL v g θ z) = g * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z := by
  rw [aL_apply, map_add, map_smul, hθ, smul_eq_mul]
  ring

theorem det_aL (hfin : Module.finrank F E = 2) (g : Fv F v) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) : LinearMap.det (aL v g θ) = g := by
  classical
  have hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange, hfin]
  have hli : LinearIndependent (Fv F v) ![θ, Δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) hst
    simp only [map_add, map_smul, hθ, hΔ, smul_eq_mul, mul_one, mul_zero, add_zero, map_zero] at h1
    subst h1
    rw [zero_smul, zero_add, smul_eq_zero] at hst
    exact ⟨rfl, hst.resolve_right hΔ0⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [hrank]; rfl)
  have hb0 : b 0 = θ := by simp [b]
  have hb1 : b 1 = Δ := by simp [b]
  have hf0 : aL v g θ (b 0) = g • b 0 := by
    rw [hb0, aL_apply, hθ, mul_one, sub_smul, one_smul]
    abel
  have hf1 : aL v g θ (b 1) = b 1 := by
    rw [hb1, aL_apply, hΔ, mul_zero, zero_smul, add_zero]
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, hf0, hf1, map_smul, b.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  simp

private theorem int_of_alg_lemma (z : Fv F v ⊗[F] E) (hz : z ∈ OEv (E := E) v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
  change z ∈ Submodule.span (v.adicCompletionIntegers F) _ at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR]
    have hint : IsIntegral ℤ (Algebra.trace F E (a : E)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe a)
    have := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) (v := v) (⟨_, hint⟩ : 𝓞 F)
    convert this using 1
    exact (IsScalarTower.algebraMap_apply (𝓞 F) F (Fv F v) (⟨_, hint⟩ : 𝓞 F)).symm
  | zero => rw [map_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [map_add]; exact add_mem hy hw
  | smul c y _ hy =>
    rw [show c • y = (c : Fv F v) • y from rfl, map_smul, smul_eq_mul]
    exact mul_mem c.2 hy

private theorem int_of_alg_lemma_2 (a : 𝓞 E) (z : Fv F v ⊗[F] E) (hz : z ∈ OEv (E := E) v) :
    inclR (Fv F v) (a : E) * z ∈ OEv (E := E) v := by
  change z ∈ Submodule.span (v.adicCompletionIntegers F) _ at hz
  change _ ∈ Submodule.span (v.adicCompletionIntegers F) _
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, -, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨a * b, Set.mem_univ _, ?_⟩
    show inclR (Fv F v) ((a * b : 𝓞 E) : E) = inclR (Fv F v) (a : E) * inclR (Fv F v) (b : E)
    rw [show ((a * b : 𝓞 E) : E) = (a : E) * (b : E) from rfl, map_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [mul_add]; exact add_mem hy hw
  | smul c y _ hy =>
    rw [show c • y = (c : Fv F v) • y from rfl, mul_smul_comm]
    exact Submodule.smul_mem _ c hy

private theorem int_of_alg_lemma_3 (x z : Fv F v ⊗[F] E) (hx : x ∈ OEv (E := E) v) (hz : z ∈ OEv (E := E) v) :
    x * z ∈ OEv (E := E) v := by
  change x ∈ Submodule.span (v.adicCompletionIntegers F) _ at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    exact int_of_alg_lemma_2 v a z hz
  | zero => rw [zero_mul]; exact (Submodule.span _ _).zero_mem
  | add y w _ _ hy hw =>
    rw [add_mul]
    exact (Submodule.span (v.adicCompletionIntegers F) _).add_mem hy hw
  | smul c y _ hy =>
    rw [show c • y = (c : Fv F v) • y from rfl, smul_mul_assoc]
    exact (Submodule.span (v.adicCompletionIntegers F) _).smul_mem c hy

theorem int_of_alg {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) {x : Fv F v}
    (hx : algebraMap (Fv F v) (Fv F v ⊗[F] E) x ∈ OEv (E := E) v) : x ∈ v.adicCompletionIntegers F := by
  have h := int_of_alg_lemma v _ (int_of_alg_lemma_3 v _ _ hx hθO)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, hθ, smul_eq_mul, mul_one] at h
  exact h

theorem mem_aL_image (σ : E →ₐ[F] E)
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (y : Fv F v ⊗[F] E) :
    y ∈ aL v (g : Fv F v) θ '' OEv (E := E) v ↔
      y ∈ OEv (E := E) v ∧ (y + sigR (Fv F v) σ y) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v := by
  classical
  have hsc : ∀ c : Fv F v, sc (E := E) v c = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, ← Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul, mul_one]
  have hcond : (y + sigR (Fv F v) σ y) * sc (E := E) v (g : Fv F v)⁻¹ =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y * (g : Fv F v)⁻¹) := by
    rw [← htr, hsc, map_mul]
  have hone : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
    have := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.inclR_mem (E := E) v 1
    simp only [OneMemClass.coe_one, map_one] at this
    exact this
  have hsmul : ∀ c ∈ v.adicCompletionIntegers F, ∀ x ∈ OEv (E := E) v, c • x ∈ OEv (E := E) v :=
    fun c hc x hx => by
      rw [← Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul]
      exact Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_mem v hc hx
  have halg : ∀ c ∈ v.adicCompletionIntegers F, algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ OEv (E := E) v :=
    fun c hc => by
      rw [Algebra.algebraMap_eq_smul_one]
      exact hsmul c hc 1 hone
  have hgO : (g : Fv F v) - 1 ∈ v.adicCompletionIntegers F :=
    sub_mem (Formalism.L2.SG.Pf.NcVal.VolTU.natCast_memO v g) (one_mem _)
  have hgne : (g : Fv F v) ≠ 0 := Formalism.L2.SG.Pf.NcVal.VolTU.natCast_ne_zero v hg0
  rw [hcond]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have htz := int_of_alg_lemma v z hz
    refine ⟨?_, ?_⟩
    · rw [aL_apply]
      exact add_mem hz (hsmul _ (mul_mem hgO htz) θ hθO)
    · rw [trace_aL v _ θ z hθ, mul_comm, ← mul_assoc, inv_mul_cancel₀ hgne, one_mul]
      exact halg _ htz
  · rintro ⟨hy, ht⟩
    have htO := int_of_alg v hθO hθ ht
    set t := Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y * (g : Fv F v)⁻¹ with ht_def
    refine ⟨y - (((g : Fv F v) - 1) * t) • θ, sub_mem hy (hsmul _ (mul_mem hgO htO) θ hθO), ?_⟩
    have htr' : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y = (g : Fv F v) * t := by
      rw [ht_def, mul_comm, mul_assoc, inv_mul_cancel₀ hgne, mul_one]
    rw [aL_apply]
    have : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (y - (((g : Fv F v) - 1) * t) • θ) = t := by
      rw [map_sub, map_smul, hθ, smul_eq_mul, mul_one, htr']
      ring
    rw [this, sub_add_cancel]

end Formalism.L2.SG.Pf.NcVal.VolV
