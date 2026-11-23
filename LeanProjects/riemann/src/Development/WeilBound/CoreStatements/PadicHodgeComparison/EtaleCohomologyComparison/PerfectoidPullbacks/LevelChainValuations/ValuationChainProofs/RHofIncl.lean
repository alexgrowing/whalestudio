import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoFirstChernLaw
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomLevGood
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.ReductionChangeLevel
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

theorem red_s_pf : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s s' : ℕ) (𝒱 : Set X.Opens) (h : TS γ q l s 𝒱 ≤ TS γ q l s' 𝒱) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ l X q κ) c) j),
    ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n))).pull j
      ((redMor q s' d 𝒱 c lam hc r).pull j x) = (redMor q s d 𝒱 c lam hc r).pull j x := by
  intro O A R Λ _ _ _ _ _ I γ J δ κ l n d X q s s' 𝒱 h c lam hc r j x
  rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := lam) (redMor q s' d 𝒱 c lam hc r) ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n))) j x).1]
  refine CrystallineSemistableComparison.P.prism ((redMor q s' d 𝒱 c lam hc r).comp (σ'' := lam) ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n)))) (redMor q s d 𝒱 c lam hc r) (𝟙 (redG q s d 𝒱)) (fun T y => ?_) j x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

theorem rHof_incl_pf (M : Model l K) (m : ℕ) {s s' : ℕ} (h : s ≤ s') (n j : ℕ) (x : M.Hc false n j) :
    inclHM M h n j (rHof (dOf S hS hC m) (hcOf S hS hC m) M s' n j x) = rHof (dOf S hS hC m) (hcOf S hS hC m) M s n j x :=
  red_s_pf _ M.p s s' {⊤} (ts_le _ M.p l h {⊤}) _ _ _ none j x

end CrystallineSemistableComparison.Pb.Kap
