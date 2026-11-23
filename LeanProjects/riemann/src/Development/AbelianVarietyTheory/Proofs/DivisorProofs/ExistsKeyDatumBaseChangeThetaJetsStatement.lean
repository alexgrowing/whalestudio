import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeThetaJets
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyDatumBaseChange_thetaJets : ∀ (K C : Type) [Field K] [Field C] (f : K →+* C) (x : KeyIn K), ∃ (xC : KeyIn C) (hg : xC.P.g = x.P.g) (io : (Over.mk (spMap f) ⟶ x.P.A) ≃* (baseOver (Sp C) ⟶ xC.P.A)), KeyPB xC x f ∧ (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs xC.P.A xC.P.L k (io a) (io b) z → WeilIs x.P.A x.P.L k a b z) ∧ ∀ (m : ℕ) (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap f)))) (I : Type) (pt : I → (Over.mk (spMap f) ⟶ x.P.A)) (y : Fin x.P.g → (Sp (DualNumber C) ⟶ (Over.mk (spMap f) ⊗ x.P.A).left)) (ϑ : I → C) (J : I → Fin x.P.g → C), IsPolAVSectionInverseImage x.P (Over.mk (spMap f)) x.th th → (∀ j, y j ≫ (fst (Over.mk (spMap f)) x.P.A).left = spMap (algebraMap C (DualNumber C)) ∧ y j ≫ (snd (Over.mk (spMap f)) x.P.A).left = spMap (dualMap f) ≫ (x.v j).left) → ThJetT x.P x.rig m (spMap f) th pt y ϑ J → ThJet xC hg m (fun i => io (pt i)) ϑ J := by
  first | exact @GlobalTheory.MBLow.exists_keyPB_thJet | exact GlobalTheory.MBLow.exists_keyPB_thJet | (intros; apply GlobalTheory.MBLow.exists_keyPB_thJet <;> assumption)
