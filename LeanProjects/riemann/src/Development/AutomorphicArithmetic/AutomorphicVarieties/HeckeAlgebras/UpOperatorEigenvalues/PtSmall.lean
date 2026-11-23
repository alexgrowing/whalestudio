import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PtLt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Hi.Up

private theorem int_iff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

variable {l : ℕ} [Fact l.Prime] {c : Coef l}

theorem coef_le (a : c.O) : ‖algebraMap c.O (Qbar l) a‖ ≤ 1 :=
  (int_iff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map c.O.val)

section Pt

variable {R : Type} [CommRing R] [Algebra c.O R]

theorem pt_lt [IsLocalRing R] (y : R →ₐ[c.O] Qbar l) (a : R) (ha : a ∈ maximalIdeal R) : ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.Gs4b.pt_lt y a ha

variable [Alg.IsCO c.O R] (y : R →ₐ[c.O] Qbar l)

theorem pt_res (b : R) (a : c.O) (h : Alg.res c.O R b = residue c.O a) : ‖y b - algebraMap c.O (Qbar l) a‖ < 1 := by
  rw [← y.commutes, ← map_sub]
  refine pt_lt y _ ((Alg.res_eq_zero_iff c.O R _).1 ?_)
  rw [map_sub, h, AlgHom.commutes]
  exact sub_self _

theorem pt_le (b : R) : ‖y b‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := Alg.IsCO.res_surj (O := c.O) b
  have h := IsUltrametricDist.norm_add_le_max (y (b - algebraMap c.O R a)) (algebraMap c.O (Qbar l) a)
  rw [← y.commutes, ← map_add, sub_add_cancel, y.commutes] at h
  exact h.trans (max_le (pt_lt y _ ha).le (coef_le a))

theorem pt_unit (b : Rˣ) : ‖y b‖ = 1 := by
  have h : ‖y b‖ * ‖y (b⁻¹ : Rˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (pt_le y _) ?_
  nlinarith [pt_le y (b⁻¹ : Rˣ), norm_nonneg (y b), norm_nonneg (y (b⁻¹ : Rˣ))]

theorem pt_small (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ b ∈ maximalIdeal R ^ N, ‖y b‖ < ε := by
  have key : ∀ (I : Ideal R) (S : Set R) (t : ℝ), 0 ≤ t → (∀ b ∈ S, ‖y b‖ ≤ t) → ∀ b ∈ Ideal.span S, ‖y b‖ ≤ t := by
    intro I S t ht hS b hb
    induction hb using Submodule.span_induction with
    | mem z hz => exact hS z hz
    | zero => simpa using ht
    | add a b _ _ ha hb => rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    | smul a b _ hb =>
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (pt_le y a)).trans hb
  obtain ⟨S, hS⟩ : (maximalIdeal R).FG := IsNoetherian.noetherian _
  obtain ⟨t, t0, t1, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ ∀ b ∈ maximalIdeal R, ‖y b‖ ≤ t := by
    refine ⟨((S.sup fun b => ‖y b‖₊ : NNReal) : ℝ), NNReal.coe_nonneg _, ?_, ?_⟩
    · have : (S.sup fun b => ‖y b‖₊) < 1 :=
        (Finset.sup_lt_iff (by simp)).2 fun b hb => pt_lt y b (hS ▸ Ideal.subset_span hb)
      exact_mod_cast this
    · rw [← hS]
      exact key ⊥ _ _ (NNReal.coe_nonneg _) fun b hb => Finset.le_sup (f := fun b => ‖y b‖₊) hb
  have hp : ∀ N : ℕ, ∀ b ∈ maximalIdeal R ^ N, ‖y b‖ ≤ t ^ N := by
    intro N
    induction N with
    | zero => intro b _; simpa using pt_le y b
    | succ N ih =>
      intro b hb
      rw [pow_succ] at hb
      refine Submodule.mul_induction_on hb (fun a ha b hb => ?_) fun a b ha hb => ?_
      · rw [map_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih a ha) (ht b hb) (norm_nonneg _) (pow_nonneg t0 _)
      · rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε t1
  exact ⟨N, fun b hb => (hp N b hb).trans_lt hN⟩

theorem pt_cont {Γ : Type} [TopologicalSpace Γ] {f : Γ → R} (hf : Alg.AdicCont (maximalIdeal R) f) :
    Continuous fun g => y (f g) := by
  refine continuous_iff_continuousAt.2 fun g => Metric.continuousAt_iff'.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := pt_small y ε hε
  filter_upwards [(hf N).eventually_eq g] with g' hg'
  rw [dist_eq_norm, ← map_sub]
  exact hN _ (Ideal.Quotient.eq.1 hg')

theorem pt_ext (x : R →ₐ[c.O] Qbar l) (S : Set R)
    (hS : ∀ (N : ℕ) (b : R), ∃ z ∈ Algebra.adjoin c.O S, b - z ∈ maximalIdeal R ^ N) (h : ∀ z ∈ S, x z = y z) : x = y := by
  refine AlgHom.ext fun b => eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨N, hN⟩ := pt_small x ε hε
  obtain ⟨M, hM⟩ := pt_small y ε hε
  obtain ⟨z, hz, hb⟩ := hS (max N M) b
  have e : x z = y z := Algebra.adjoin_le (S := AlgHom.equalizer x y) h hz
  have h1 := hN _ (Ideal.pow_le_pow_right (le_max_left _ _) hb)
  have h2 := hM _ (Ideal.pow_le_pow_right (le_max_right _ _) hb)
  rw [map_sub, ← dist_eq_norm] at h1 h2
  rw [← e, dist_comm] at h2
  exact (IsUltrametricDist.dist_triangle_max _ _ _).trans (max_le h1.le h2.le)

end Pt

end UpperTheory.V.Hi.Up
