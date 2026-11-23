import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PhiTTmul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.IsProperOfProj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthWittCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedWittIsNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarePullBijectiveOfAcyclicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredModuleFiniteOfGradedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneVanishAboveDimStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneGradedFiniteStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

private lemma isHecke_div_and_resEtaPow_div {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (d : ℕ)
    (hvan : ∀ j, Subsingleton (CH.H (sq (sFil Q (↑d + 1)) (IdF.bot (sP Q).A)) j))
    (hN : IsNoetherianRing b.R)
    (hgr : ∀ r j : ℕ, Module.Finite b.R (CH.H (sq (sFil Q ↑r) (sFil Q (↑r + 1))) j)) (j : ℕ) :
    Module.Finite b.R (HO Q j) := by
  have hfin := GlobalTheory.T.filtered_module_finite_of_graded (sFil Q) (fun r r' h T => (isFil Q).anti h T) (d + 1) (fun r _ j' => hgr r j') j
  rw [Nat.cast_add, Nat.cast_one] at hfin
  have ha : ∀ T, (sFil Q 0).S T = ⊤ := fun T => (isFil Q).top 0 le_rfl T
  have hb := GlobalTheory.T.square_pull_bijective_of_acyclic (sFil Q 0) (sFil Q (↑d + 1)) ha ?hv j
  · exact Module.Finite.of_surjective (hM := hfin) (LinearEquiv.ofBijective _ hb).symm.toLinearMap
      (LinearEquiv.ofBijective _ hb).symm.surjective
  · exact hvan

theorem wittCohomology_finite_length {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] [Smooth q] (ρ : O →+* k) (j : ℕ) :
    IsFiniteLength (WittVector l k) (CH.H (Wc.OM l (B.schFn q) ρ 1) j) := by
  obtain ⟨U⟩ := (CrystallineSemistableComparison.Pb.cov_ex q).1 inferInstance
  refine GlobalTheory.T.finite_length_witt_cohomology q ρ j ?_
  have hvan := GlobalTheory.T.witt_level_one_vanish_above_dim q ρ U (Finset.univ.sup U.d) (fun α => Finset.le_sup (Finset.mem_univ α))
  have hfin := isHecke_div_and_resEtaPow_div _ _ hvan ?hN ?hgr j
  · refine Module.Finite.of_surjective (hM := hfin)
      (LinearEquiv.ofBijective ((incl ?hle).o.pull j) ?hb).symm.toLinearMap (LinearEquiv.surjective _)
    · intro T hT
      exact ⟨hT.1, ⊤, Set.mem_singleton _, by simp [InU]⟩
    · refine (CrystallineSemistableComparison.Pb.zar ⊤ ?u (Set.range U.U) {⊤} _ ?hcov j).2.2
      · exact Or.inr ⟨(Fact.out : l.Prime).ne_zero, Or.inl rfl⟩
      · intro W hW
        rw [Set.mem_singleton_iff.mp hW, sSup_range, U.cover]
  · exact GlobalTheory.T.truncated_witt_isNoetherian
  · exact GlobalTheory.T.witt_level_one_graded_finite q ρ U

theorem smooth_model_finite_length_link {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K)
    (hM : M.Sm) (j : ℕ) : IsFiniteLength (WittVector l r.k) ((Wc.HS l (B.schFn M.p) r.ρ j).M 1) := by
  have : IsProper M.p := sm_proper hM
  have : Smooth M.p := hM.2
  exact wittCohomology_finite_length M.p r.ρ j

end CrystallineSemistableComparison.Pb
