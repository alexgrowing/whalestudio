import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtBigRun
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem wtBig_run_alt : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m →
    WtBig (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)) := by
  obtain ⟨ε1, hε1, H⟩ := GlobalTheory.T.runSizes_quotientGaps_large
  refine ⟨ε1, hε1, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨x0, hx0⟩ := hK Fm CH hc hL
  refine ⟨0, le_rfl, x0, fun x hx hxx ι p _ i hi => ?_⟩
  obtain ⟨hD1, hDT, hG⟩ := hx0 x hx hxx ι
  obtain ⟨hr, hdim, hgap⟩ := GlobalTheory.T.anchoredWeight_indefiniteLift_gaps p (Fm.params x hx ι) i hi
  have hlen : lenT p i (Fm.parT x hx ι).PP = ⌈(Fm.parT x hx ι).PP ^ 2 *
      (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) / ((Fm.D x ι).R.m : ℝ)⌉₊ := by
    rw [lenT, GlobalTheory.CompHS.dimFlag_eq, hdim]
  obtain ⟨hG1, hG2⟩ := hG _ _ rfl hlen
  have hc0 : ((cZero (Fm.D x ι) ((i : ℕ) + 1) : ℤ) : ℝ) ≤ 22 * ((Fm.D x ι).R.f : ℝ) ^ 2 * ((Fm.D x ι).R.r : ℝ) ^ 4 := by
    exact_mod_cast (cZero_spec (Fm.D x ι) ((i : ℕ) + 1)).2.2
  clear H hK hx0 hG
  refine ⟨fun τ k hk => ?_, ?_, ?_⟩
  · rw [WtPar.gap_u₁ _ τ hk, WtPar.gap_uMinus_sub_kap _ τ hk]
    simp only [WtPar.T₁]
    rw [hdim]
    have hGeq : ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * ((dat p i).p + (dat p i).q) +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) =
        ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) := by rw [hr]
    rw [hGeq]
    have hr2 : (((dat p i).p + (dat p i).q : ℕ) : ℤ) = (Fm.D x ι).R.r := by exact_mod_cast hr
    generalize ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) = G at hG1 hG2 ⊢
    generalize lenT p i (Fm.parT x hx ι).PP = T at hG1 hG2 ⊢
    generalize (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 = Dd at hG1 hG2 ⊢
    have hT : (0 : ℤ) < (T : ℤ) + (Dd : ℤ) + 1 := by positivity
    refine Int.le_ediv_of_mul_le hT ?_
    obtain ⟨g1, g2⟩ := hgap τ k hk
    by_cases hb : k + 1 = (dat p i).p
    · rw [if_pos hb, hr2]
      have e := g2 hb
      have : (((G : ℤ) * ((T : ℤ) + (Dd : ℤ) + 1) : ℤ) : ℝ) ≤
          ((gap (uW p i τ) k + (-(cZero (Fm.D x ι) ((i : ℕ) + 1)) - (2 * ((Fm.D x ι).R.r : ℤ) - 2)) : ℤ) : ℝ) := by
        push_cast at hG2 e ⊢
        linarith
      exact_mod_cast this
    · rw [if_neg hb]
      have e := g1 hb
      have : (((G : ℤ) * ((T : ℤ) + (Dd : ℤ) + 1) : ℤ) : ℝ) ≤ ((gap (uW p i τ) k + 2 : ℤ) : ℝ) := by
        push_cast at hG1 e ⊢
        linarith
      exact_mod_cast this
  · show GlobalTheory.FlagTan.dimFlag (dat p i) + 1 ≤ lenT p i (Fm.parT x hx ι).PP
    rw [hdim, hlen]; exact hDT
  · show 1 ≤ GlobalTheory.FlagTan.dimFlag (dat p i)
    rw [hdim]; exact hD1
end GlobalTheory.HSApp
end
end
