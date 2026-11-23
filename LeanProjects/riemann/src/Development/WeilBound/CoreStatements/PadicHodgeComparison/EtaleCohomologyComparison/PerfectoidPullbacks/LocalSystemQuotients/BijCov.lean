import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.BijOfSub
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittSiteRestrictBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittSiteQuotientRestrictBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelMorphismCoverCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittCoordQuotientPullBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb.SubquotientResolution

open CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.LsQ

section Q

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k)

set_option maxHeartbeats 4000000 in

theorem bij_cov (U : Cov q) {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    Function.Bijective (((mq (F := B.schFn q) (ρ := ρ) hn).o (IdF.span _ ((l : WittVector l k) ^ n))
      (fun _ => le_rfl)).pull j) := by
  have hUs : sSup (Set.range U.U) = ⊤ := by
    rw [sSup_range]
    exact U.cover
  have g := GlobalTheory.T.witt_level_morphism_cover_compat q ρ U n ((l : WittVector l k) ^ n) (mq (F := B.schFn q) (ρ := ρ) hn) (hGq q ρ hn)
    (fun S hS j => by
      obtain ⟨α, hα⟩ := hS
      obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα : (⨅ α ∈ S, U.U α) ≤ U.U α) (U.inter S ⟨α, hα⟩)
      exact GlobalTheory.T.witt_coord_quotient_pull_bijective q ρ hn c' j) j
  have z0 := GlobalTheory.T.witt_site_restrict_bijective q ρ n (Set.range U.U) hUs j
  have zq := GlobalTheory.T.witt_site_quotient_restrict_bijective q ρ (n + 1) (Set.range U.U) ((l : WittVector l k) ^ n) hUs j
  exact bij_of_sub (mq (F := B.schFn q) (ρ := ρ) hn) (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1)
    (fun _ h => h.1) (hGq q ρ hn _) j z0 zq g

end Q

set_option maxHeartbeats 1000000 in

theorem bij : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm →
    ∀ (n : ℕ) (hn : n ≠ 0) (j : ℕ), Function.Bijective (((mq (F := B.schFn M.p) (ρ := r.ρ) hn).o
      (IdF.span _ ((l : WittVector l r.k) ^ n)) (fun _ => le_rfl)).pull j) := by
  intro l _ K r M hM n hn j
  have : IsProper M.p := GlobalTheory.CommonModel.isProper_of_isProjOver hM.1.1
  obtain ⟨U⟩ := (cov_ex M.p).1 hM.2
  exact bij_cov M.p r.ρ U hn j

end CrystallineSemistableComparison.Pb.SubquotientResolution

end
