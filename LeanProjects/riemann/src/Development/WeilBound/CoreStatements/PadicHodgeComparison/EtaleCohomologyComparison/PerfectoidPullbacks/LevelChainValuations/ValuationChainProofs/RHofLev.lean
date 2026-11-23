import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RestrictionInclusions.PullHcId
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.NmHONmPullBBMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.TwistAcrisZeroPreservesFiltration

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

namespace LevelIdentityMorphisms

def idMor (M : Model l K) (n : ℕ) :
    GlobalTheory.LogCris.Mor (B.Lc (B.schFn M.p) (okToOC l K) false n) (B.Lc (B.schFn M.p) (okToOC l K) false n) (RingHom.id _) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l false n) (b' := B.bs l false n) (ht := rfl) (ht' := rfl)
    (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism (𝟙 _) (fun _ _ _ => rfl)

abbrev idOm (M : Model l K) (n : ℕ) :
    CH.Mor (B.Oc (B.schFn M.p) (okToOC l K) false n) (B.Oc (B.schFn M.p) (okToOC l K) false n) (RingHom.id (Acris l)) :=
  B.omMor (idMor M n) (RingHom.id (Acris l)) (fun _ => rfl)

def idEta (M : Model l K) (n : ℕ) : (CH.Mor.id (B.Oc (B.schFn M.p) (okToOC l K) false n)).G ⟶ (idOm M n).G where
  app T := LevelPullbackIdentities.thHom ⟨fun j => Empty.elim j⟩ rfl (RingHom.id T.B) (fun r => rfl) (DPMorphism.id T.δ).isDPMorphism
    (fun _ h => h)
    (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => LevelPullbackIdentities.qid _ (fun _ h => h) _))
      (LevelPullbackIdentities.spec_qid _ (fun _ h => h) _)))
  naturality _ _ f := Thick.Hom.ext (RingHom.ext fun _ => rfl) (funext fun j => Empty.elim j)

theorem idMor_pull (M : Model l K) (n j : ℕ) (x : M.Hc false n j) : (idOm M n).pull j x = x := by
  have h1 : (CH.Mor.id (B.Oc (B.schFn M.p) (okToOC l K) false n)).pull j x = x :=
    (CrystallineSemistableComparison.P.pull_comp (CH.Mor.id _) (CH.Mor.id _) j x).2
  have h2 := CrystallineSemistableComparison.P.prism (CH.Mor.id (B.Oc (B.schFn M.p) (okToOC l K) false n)) (idOm M n) (idEta M n)
    (fun T x => rfl) j x
  exact h2.symm.trans h1

end LevelIdentityMorphisms

theorem nmHM_nmLevA_rHof_succ (M : Model l K) (m s n j : ℕ) (x : M.Hc false n j) :
    nmHM (nmLevA S hS m M) l s none n j (rHof (dOf S hS hC (m + 1)) (hcOf S hS hC (m + 1)) M s n j x) =
      rHof (dOf S hS hC m) (hcOf S hS hC m) M s n j x := by
  have hρ : ∀ y, (dOf S hS hC m n).ρ (RingHom.id _ y) = lnMap (S.dA m) l le_rfl ((dOf S hS hC (m + 1) n).ρ y) := by
    intro y
    obtain ⟨c, rfl⟩ := ((RL.base_acr (PAlg.base l) PAlg.isBase_base).2 n).1 y
    rw [RingHom.id_apply, hcOf, hcOf]
    exact congrArg (Ideal.Quotient.mk _) (hS.dlam m c).symm
  have e := red_nm (dOf S hS hC (m + 1) n) (dOf S hS hC m n) s (nmLevA S hS m M) (LevelIdentityMorphisms.idMor M n)
    ((PAlg.base l).cris n) ((PAlg.base l).cris n) (S.L (m + 1)).lam (S.L m).lam
    (hcOf S hS hC (m + 1) n) (hcOf S hS hC m n) (RingHom.id _) (fun _ => rfl) (fun _ _ => (Category.comp_id _).symm)
    hρ none j x
  exact (congrArg _ (LevelIdentityMorphisms.idMor_pull M n j x).symm).trans e |>.symm

end CrystallineSemistableComparison.Pb.Kap
