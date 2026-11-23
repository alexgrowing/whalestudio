import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataKeptClausesColumnChoices
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoreAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analyticData_kept_clauses_columnChoices : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (T : Top.TwDat X.B)
    (Wt : Set X.B.places.Pl) (Ks' : Type) [Field Ks'] [NumberField Ks'] [Algebra Ks' X.toD7.what₂.LL],
    GlobalTheory.Published.DiscreteSeriesExists → Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) → I.Ok → Set.range I.xi = T.set I.C →
    SelHalf I → GrpAt X I → ValsIn I → HostHyp X.toD7 →
    (∀ j, Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Seed.FrmC.StdLat (X.toD7.sp.V j) ∧
      (1 ≤ j → j ≤ X.toD7.R.m → Seed.FrmC.StdLat (X.toD7.sp.W j))) → Seed.FrmC.StdLat X.toD7.sp.X' →
    (∀ i, (Vc X.toD7 i).IsPosDef) →
    (∀ x ∈ X.B.Ks, ∃ y : Ks', algebraMap Ks' X.toD7.what₂.LL y = x) →
    (∀ x : X.toD7.host.E, ∃ y : Ks', algebraMap Ks' X.toD7.what₂.LL y = X.toD7.embE x) →
    (∀ (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I (usedOf I T Wt))), L.Is (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))) →
      L.C = Top.Fr.at X I.C → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 →
        ∃ y : Ks', ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap Ks' X.toD7.what₂.LL y)) →
    ∃ (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (R₀ : RealDat3 X.toD7 (famR X I hX (usedOf I T Wt) Xg tr₀) Ks')
      (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd),
      LevOf X I (usedOf I T Wt) R₀.toRealDat.toLevCh ∧ IsPlacewiseIdentity X (px := px) R₀.eG ∧ GoodSet X (px := px) (R₀.eG.trans cG) Xg ∧
      MuOf X I T Wt R₀.mu R₀.twPl ∧ IdemClass (D := X.toD7) (famR X I hX (usedOf I T Wt) Xg tr₀).A ∧
      R₀.toRealDat.Pre0 (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧ R₀.AllPlaces ∧
      Keep R₀.toRealDat (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 cG ∧ BrgStd X I hX (usedOf I T Wt) Xg tr₀ R₀.toRealDat  := by
  first | exact @GlobalTheory.Mem.R3.FrameCaseLifts.exists_realDat_keep | exact GlobalTheory.Mem.R3.FrameCaseLifts.exists_realDat_keep | (intros; apply GlobalTheory.Mem.R3.FrameCaseLifts.exists_realDat_keep <;> assumption)
