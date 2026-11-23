import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre

theorem act_normPull_smul : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m : ℕ), Odd m → ∀ (th th' : SecA A F 1) (c : F), (∀ j, th.f j = liftFun A.A _ (cF R c) * th'.f j) → ∀ (s₁ σ t : SecA A F (m ^ 2)) (x : TFK (R := R) F ⟶ A.A) (θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := R) F)) (c' : F), x ^ (m ^ 2) = 1 → IsNormPull A ρ m (m ^ 2) th s₁ → SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ → IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₁ σ → ThC A ρ m th' x t c' → ∀ j, σ.f j = liftFun A.A _ (cF R c) * t.f j := by
  intro hLL R _ _ _ A F _ _ ρ hρ m hm th th' c hc s₁ σ t x θ c' hx ⟨α, hα, hn, hs₁⟩ hθ hσ
    ⟨α', s₁', θ', hα', hn', hs₁', hθ', ht', _⟩
  have hLaw : Laws := hLL.1
  have hL := A.isLB
  let T := TFK (R := R) F
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hm.pos.ne'))
  obtain ⟨-, huniq⟩ := hLaw.symLift _ A (m ^ 2) hm.pow hu T x hx
  have ea := gen_unique hL (fst T A.A).left (ptSecT A.A 1).left NormTheta.ptSec_fst
    (CommPairing.surj_fst hLaw.globalFns A.isAb T) hα hα' (fun y J hJ => by
      have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
      rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
  have eθ := huniq θ θ' hθ hθ'
  have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
  have f₁ : (mulT A.A T m).left ≫ (fst T A.A).left = (fst T A.A).left := by
    rw [← Over.comp_left, mulT, lift_fst]
  have f₂ : (translT A.A θ.pt).left ≫ (fst T A.A).left = (fst T A.A).left := by
    rw [← Over.comp_left, translT, lift_fst]
  have key : SecM.ofSec A.A σ = cF R c • SecM.ofSec A.A t := ThetaAct.sv_ext hL fun y J hJ => by
    refine Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm
    have a₁ := ThetaLin.sval_of_isTwistPull A.A hσ (𝟙 _) y hJ
    have a₂ := ThetaLin.sval_of_isTwistPull A.A hs₁ (𝟙 _ ≫ (translT A.A θ.pt).left) y hJ
    have a₃ := ThetaPtMove.sv_of_eq_mul hc ((𝟙 _ ≫ (translT A.A θ.pt).left) ≫ (mulT A.A T m).left) y hJ
    have b₁ := ThetaLin.sval_of_isTwistPull A.A ht' (𝟙 _) y hJ
    have b₂ := ThetaLin.sval_of_isTwistPull A.A hs₁' (𝟙 _ ≫ (translT A.A θ.pt).left) y hJ
    rw [← val_corr hJ eθ, ← ept, b₂, ← ea _ _ y J hJ] at b₁
    rw [Category.assoc _ (mulT A.A T m).left (fst T A.A).left, f₁, Category.assoc _ _ (fst T A.A).left, f₂] at a₃
    refine a₁.trans (Eq.trans ?_ (congrArg (_ * ·) b₁.symm))
    rw [a₂]
    refine (congrArg (fun q => _ * (_ * q)) a₃).trans ?_
    ring
  exact fun j => congrArg (fun q => q.1 j) key

end GlobalTheory.TestFibre
