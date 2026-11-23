import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexCompletedStandardNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanHeisenbergTranslatesVacuumEqTopStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.Vacuum

theorem sd_std (D : D7) (N : ℕ) : SD D (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  exact h2 ▸ (h1 1).2

theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ)
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (m • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, map_nsmul]
  exact smul_comm _ _ _

theorem map_nsmul_inc (D : D7) {N N' : ℕ} (m : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    (m • z).map (inc D) = m • z.map (inc D) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul]

theorem nsmul_inv_smul {X : Type*} [AddCommGroup X] [Module ℚ X] {m : ℕ} (hm : 0 < m) (a : X) :
    m • ((m : ℚ)⁻¹ • a) = a := by
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hm.ne'), one_smul]

theorem level_fixed {D : D7} (hg : admG1 D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ}
    {w : 𝓞 D.host.E} {γ : XA D N N' → XA D N N' → ℂ}
    {WA : XA D N N' → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N'}
    (hM : GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA) (v : TTs D (tor0 D cc δ) N N') (m : ℕ)
    (hv : ∀ x ∈ La0 D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (m • x) v = v) :
    ∀ b ∈ latA D cc N N', WA (m • b) v = v := by
  intro b hb
  obtain ⟨-, -, -, hW, hC⟩ := hM
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hg cc δ hc N N'
  obtain ⟨m', hm', h⟩ := hC (m • b) v
  obtain ⟨z, a, ha, hz⟩ := h3 b m' hm'
  have hz' : pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N' := by
    rw [← h1, hz]
    exact add_mem hb (nsmul_mem ha _)
  have e : (m • z).map (inc D) = m • b + m' • (m • a) := by
    rw [map_nsmul_inc, hz, smul_add, smul_comm m m' a]
  rw [← h _ (nsmul_mem ha m), ← e]
  apply Subtype.ext
  rw [hW, pt_nsmul]
  exact hv _ hz'

theorem vacuum_fixed_span : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∃ h : e0 ∈ TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') ⟨e0, h⟩ ∧ Submodule.span ℂ (Set.range fun ζ => WA ζ ⟨e0, h⟩) = ⊤ := by
  intro D hg cc δ hc N N' w γ WA hM e0 he0 hne
  obtain ⟨hL, hWd, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg cc δ hc N N' (La0 D (tor0 D cc δ) N N')
    (Or.inr ⟨_, _, sd_std D _, sd_std D _, rfl⟩)
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hg cc δ hc N N'
  have h0 : ∀ x ∈ La0 D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) ((1 : ℕ) • x) e0 = e0 := fun x hx => by
    rw [one_smul, hWd x hx]
    funext z
    exact he0.2 x hx z
  have hT : e0 ∈ TTs D (tor0 D cc δ) N N' := ⟨he0.1, 1, one_pos, h0⟩
  refine ⟨hT, fun a ha => ?_, ?_⟩
  · have := level_fixed hg hc hM ⟨e0, hT⟩ 1 h0 a ha
    rwa [one_smul] at this
  refine GlobalTheory.T.span_heisenberg_translates_vacuum_eq_top hM.1 _ hM.2.1 _ (fun v hv => ?_) (fun v => ?_)
  · have hv' : (v : VC D N N' → ℂ) ∈ ThSp D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := by
      refine ⟨v.2.1, fun x hx y => ?_⟩
      have e := hWd x hx v
      obtain ⟨z, rfl⟩ := h2 x hx
      rw [← hM.2.2.2.1, hv _ ((h1 z).2 hx)] at e
      exact (congrFun e y).symm
    obtain ⟨c, hc'⟩ := hL _ hv' e0 he0 hne
    exact ⟨c, Subtype.ext hc'⟩
  · obtain ⟨-, m, hm, hv⟩ := v.2
    refine ⟨(latA D cc N N').comap (m • LinearMap.id), GlobalTheory.T.heisenbergRelativeIndex_completedStandard_ne_zero D hg cc δ hc N N' m hm _ (fun ζ hζ => hζ),
      fun a _ hT' => ?_⟩
    have hb : (m : ℚ)⁻¹ • a ∈ latA D cc N N' := by
      refine (hM.2.1 _).2 fun a' ha' => ?_
      have ht : (m : ℚ)⁻¹ • a' ∈ (latA D cc N N').comap (m • LinearMap.id) := by
        change m • ((m : ℚ)⁻¹ • a') ∈ latA D cc N N'
        rwa [nsmul_inv_smul hm]
      rw [← nsmul_inv_smul hm a', hM.1.nsmul_right, ← hM.1.nsmul_left, nsmul_inv_smul hm]
      exact hT' _ ht
    have := level_fixed hg hc hM v m hv _ hb
    rwa [nsmul_inv_smul hm] at this

end GlobalTheory.FinWeil.Vacuum
