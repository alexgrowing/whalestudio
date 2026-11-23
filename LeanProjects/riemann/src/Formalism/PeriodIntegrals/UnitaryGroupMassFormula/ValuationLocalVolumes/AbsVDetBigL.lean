import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.MemALImage

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolV

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem absV_pow (x : Fv F v) (n : ℕ) : absV v (x ^ n) = absV v x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, VolOrdW.absV_one]
  | succ n ih => rw [pow_succ, VolOrdW.absV_mul, ih, pow_succ]

theorem meas_image (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → Fv F v ⊗[F] E))
    [μ.IsAddHaarMeasure] (f : (ι → Fv F v ⊗[F] E) →ₗ[Fv F v] (ι → Fv F v ⊗[F] E))
    (hf : LinearMap.det f ≠ 0) (S : Set (ι → Fv F v ⊗[F] E)) (hS : MeasurableSet S) :
    μ (f '' S) = ENNReal.ofReal (absV v (LinearMap.det f)) * μ S := by
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.locallyCompact_Fv v
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  let b := Module.finBasis (Fv F v) (Fv F v ⊗[F] E)
  let eR : (Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { b.equivFun with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eR.toHomeomorph.secondCountableTopology
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (ι → Fv F v ⊗[F] E) := Pi.borelSpace
  let e0 : (ι → Fv F v ⊗[F] E) ≃ₗ[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    (LinearEquiv.piCongrRight fun _ : ι => b.equivFun).trans
      (LinearEquiv.curry (Fv F v) (Fv F v) ι (Fin _)).symm
  let eV : (ι → Fv F v ⊗[F] E) ≃L[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  have hLM := PI.NglqJacSplitW.linModulusV_of
    (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)
  rw [hLM (Fv F v) (ι → Fv F v ⊗[F] E) (ι × Fin _) ⟨eV⟩ f hf μ inferInstance S hS,
    PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v _ hf]
  rfl

section Big

variable (r : ℕ)

def famL (g : Fv F v) (θ : Fv F v ⊗[F] E) (p : Fin (r + 1) × Fin (r + 1)) :
    (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
  if p.1 < p.2 then g • LinearMap.id else if p.1 = p.2 then aL v g θ else LinearMap.id

def bigL (g : Fv F v) (θ : Fv F v ⊗[F] E) :
    (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  LinearMap.pi fun p => (famL v r g θ p).comp (LinearMap.proj p)

theorem det_famL_mul (hfin : Module.finrank F E = 2) (g : Fv F v) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) (p : Fin (r + 1) × Fin (r + 1)) :
    LinearMap.det (famL v r g θ p) * LinearMap.det (famL v r g θ p.swap) = g ^ 2 := by
  have hr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hfin
  have hs : LinearMap.det (g • (LinearMap.id : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E))) = g ^ 2 := by
    rw [LinearMap.det_smul, LinearMap.det_id, hr, mul_one]
  have ha := det_aL v hfin g θ Δ hθ hΔ hΔ0
  obtain ⟨i, j⟩ := p
  simp only [Prod.swap_prod_mk]
  rcases lt_trichotomy i j with h | h | h
  · have h1 : ¬ j < i := not_lt.2 h.le
    have h2 : j ≠ i := h.ne'
    simp only [famL, if_pos h, if_neg h1, if_neg h2, hs, LinearMap.det_id, mul_one]
  · subst h
    simp only [famL, lt_irrefl, if_false, if_true, ha, sq]
  · have h1 : ¬ i < j := not_lt.2 h.le
    have h2 : i ≠ j := h.ne'
    simp only [famL, if_pos h, if_neg h1, if_neg h2, hs, LinearMap.det_id, one_mul]

theorem det_bigL_sq (hfin : Module.finrank F E = 2) (g : Fv F v) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) : LinearMap.det (bigL v r g θ) ^ 2 = (g ^ 2) ^ ((r + 1) ^ 2) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [bigL, LinearMap.det_pi, sq]
  have e : ∏ p : Fin (r + 1) × Fin (r + 1), LinearMap.det (famL v r g θ p.swap) =
      ∏ p : Fin (r + 1) × Fin (r + 1), LinearMap.det (famL v r g θ p) :=
    Fintype.prod_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)
  conv_lhs => arg 2; rw [← e]
  rw [← Finset.prod_mul_distrib]
  simp only [det_famL_mul v r hfin g θ Δ hθ hΔ hΔ0, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, sq]

theorem absV_det_bigL (hfin : Module.finrank F E = 2) {g : ℕ} (hg0 : g ≠ 0)
    (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) :
    LinearMap.det (bigL v r (g : Fv F v) θ) ≠ 0 ∧
      absV v (LinearMap.det (bigL v r (g : Fv F v) θ)) = (g : ℝ)⁻¹ ^ ((r + 1) ^ 2) := by
  have hgv : (g : Fv F v) ≠ 0 := VolTU.natCast_ne_zero v hg0
  have h2 := det_bigL_sq v r hfin (g : Fv F v) θ Δ hθ hΔ hΔ0
  have hD : LinearMap.det (bigL v r (g : Fv F v) θ) ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at h2
    exact (pow_ne_zero _ (pow_ne_zero _ hgv)) h2.symm
  refine ⟨hD, ?_⟩
  have h3 := congrArg (absV v) h2
  rw [absV_pow, absV_pow, absV_pow, hg] at h3
  have hpos := (VolOrdW.absV_pos v hD).le
  have hgpos : (0 : ℝ) ≤ (g : ℝ)⁻¹ ^ ((r + 1) ^ 2) := by positivity
  refine (pow_left_inj₀ hpos hgpos two_ne_zero).1 ?_
  rw [h3, ← pow_mul, ← pow_mul, mul_comm]

end Big

end Formalism.L2.SG.Pf.NcVal.VolV
