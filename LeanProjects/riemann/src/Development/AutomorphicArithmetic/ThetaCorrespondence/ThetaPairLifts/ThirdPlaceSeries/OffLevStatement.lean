import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuadraticFamilyLevelIdentityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GVec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OffLev

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_family_level_identity_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → (∀ i, (G i).Chars (f.t t)) → (∀ j, j < D.R.m → ∀ (X : (f.t t).CC j) x, ∀ a ∈ GinfC _, (∀ i, (F.Q i).Typed j (rTrans (a * v.b j) (X.1 x))) ∧ ∀ κ, GlobalTheory.FinPl.InK _ (v.N j) (offP v w) κ → rTrans κ (rTrans (a * v.b j) (X.1 x)) = rTrans (a * v.b j) (X.1 x)) ∧ (∀ j, j + 1 < D.R.m → ∀ k ∈ v.JG (j + 1), ∃ a : ℂ, a ≠ 0 ∧ (∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) g → (f.t t).om j (1, k) (comb f.c.ψ _ _ (v.eG j) g) = a⁻¹ • comb f.c.ψ _ _ (v.eG j) g) ∧ (j + 1 + 1 < D.R.m → ∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) g → (f.t t).om (j + 1) (k, 1) (comb f.c.ψ _ _ (v.eG (j + 1)) g) = a • comb f.c.ψ _ _ (v.eG (j + 1)) g) ∧ ∀ (X : (f.t t).CC (j + 1)) x, rTrans k (rTrans (v.b (j + 1)) (X.1 x)) = a • rTrans (v.b (j + 1)) (X.1 x)) ∧ TopSph (t := f.t t) v := by
  first | exact @_root_.GlobalTheory.RowLevel.main_alt_alt | exact _root_.GlobalTheory.RowLevel.main_alt_alt | (intros; apply _root_.GlobalTheory.RowLevel.main_alt_alt <;> assumption)
end
