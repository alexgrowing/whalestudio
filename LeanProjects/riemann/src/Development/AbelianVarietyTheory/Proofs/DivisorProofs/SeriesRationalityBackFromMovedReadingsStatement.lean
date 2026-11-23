import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesRationalityBackFromMovedReadings
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullHeckeRealDatMovedReadings
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesRationality_back_from_movedReadings : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ), (∀ i σ, w i σ ∈ Subgroup.center Γ) → ∃ (S' : NX.RatDat D.ntw) (YS' : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w) cG S'), ∀ (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), RatRow YS' v₀ hρ i j b → RatRow YS v₀ hρ i j b := by
  first | exact @GlobalTheory.UnframeForms.ratRow_back | exact GlobalTheory.UnframeForms.ratRow_back | (intros; apply GlobalTheory.UnframeForms.ratRow_back <;> assumption)
