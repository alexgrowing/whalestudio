import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairCov

variable {D : D7} (O : Setup D) (R : ℝ) (c : O.s.Comp) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL))

def PairWit (E E' : (D.host.E →+* ℂ) → Bs.Modules) (h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ))
    (h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)) (u : ∀ σ, E σ ⟶ E' σ) {Bg : Scheme.{0}} (jB : Bg ⟶ Bs)
    (πB : Bg ⟶ gen O.s.T.Z) (t : ∀ σ, FrAssign O.s.T.Z (E σ) (O.S.Dw.mult σ) jB)
    (t' : ∀ σ, FrAssign O.s.T.Z (E' σ) (O.S.Dw.mult σ) jB) (G : ∀ σ', EigMet O.s.T.Z σ') : Prop :=
  IsPullback jB (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) ∧
    IsFinite πB ∧ Set.range πB = Set.range (O.Φ.C c).π ∧
    (∀ σ, IsLieFrames O.s.T.Z O.κ.e jB πB (E σ) _ σ false (t σ)) ∧
    (∀ σ, IsLieFrames O.s.T.Z O.κ.e jB πB (E' σ) _ σ false (t' σ)) ∧
    (∀ σ, Matches O.s.T.Z jB πB (u σ) (t σ) (t' σ)) ∧
    (∀ σ, IsLieLat O.s.T.Z O.κ.e jB πB (E σ) _ σ (ArIn.ind ∅) (fun _ => True) (t σ)) ∧
    (∀ σ, IsGrLat O.s.T.Z O.κ.e jB πB (E' σ) _ σ (t' σ)) ∧
    (∀ σ n, O.met.hm c (some R) σ n = (O.Φ.C c).met (G (embOf O.κ.e σ)) n) ∧
    (∀ σ, IsLieMet O.s.T.Z O.κ.e q jB πB (E σ) _ σ false rfl G (h σ) (t σ)) ∧
    ∀ σ, IsLieMet O.s.T.Z O.κ.e q jB πB (E' σ) _ σ false rfl G (h' σ) (t' σ)

theorem pairBase_iff (E E' : (D.host.E →+* ℂ) → Bs.Modules) (h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ))
    (h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)) (u : ∀ σ, E σ ⟶ E' σ) :
    PairBase O R c q E E' h h' u ↔ ∃ (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
      (t : ∀ σ, FrAssign O.s.T.Z (E σ) (O.S.Dw.mult σ) jB) (t' : ∀ σ, FrAssign O.s.T.Z (E' σ) (O.S.Dw.mult σ) jB)
      (G : ∀ σ', EigMet O.s.T.Z σ'), PairWit O R c q E E' h h' u jB πB t t' G := by
  constructor
  · rintro ⟨Bg, jB, πB, pb, t, t', G, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨Bg, jB, πB, t, t', G, pb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · rintro ⟨Bg, jB, πB, t, t', G, pb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨Bg, jB, πB, pb, t, t', G, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

variable {O c}

def IsFrameSecX (σ : D.host.E →+* ℂ) {M : Bs.Modules} (hM : IsVB M (O.S.Dw.mult σ)) {Bg : Scheme.{0}} (jB : Bg ⟶ Bs)
    (πB : Bg ⟶ gen O.s.T.Z) (t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB) {Y X : Scheme.{0}} (π : Y ⟶ Bs) (ρ : X ⟶ Y)
    (F : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult σ))
    {Gs : Scheme.{0}} [IsIntegral Gs] (j : Gs ⟶ X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg)
    (i : Fin (O.S.Dw.mult σ)) (r : ((F.root i).pull j).ι → Gs.functionFieldˣ) : Prop :=
  haveI := hM.isQuasicoherent
  haveI := (hM.pullback π).isQuasicoherent
  ∀ (ch : ((F.root i).pull j).ι) (V : Bs.Opens) (f : Fin (O.S.Dw.mult σ) → Γ(M, V)) (hf : IsFrame f) (W : X.Opens)
    (hW : W ≤ (ch PUnit.unit).U) (hWV : W ≤ ρ ⁻¹ᵁ (π ⁻¹ᵁ V))
    (s : Γ(F.F i.succ, W)), (F.π i).app W s = Twist.resM _ hW ((ch PUnit.unit).e 0) →
    ∀ (hx : ⊤ ≤ (genPt Gs ≫ j) ⁻¹ᵁ W) (hxV : ⊤ ≤ ((genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ V),
      let aG : Fin (O.S.Dw.mult σ) → Gs.functionField := fun b =>
        TangentOrigin.evalPt (genPt Gs ≫ j) W hx
          ((((hf.pullback π).pullback ρ).basis hWV).repr ((F.ι i.succ).app W s) b)
      let uu := t V f hf Gs.functionField (genPt Gs ≫ jG) hxV
      let v : Fin (O.S.Dw.mult σ) → (Sp (DualNumber Gs.functionField) ⟶ O.s.T.Z.t.G.left) :=
        fun k => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v σ k
      let x := genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z
      ∃ (w : Sp (DualNumber Gs.functionField) ⟶ O.s.T.Z.t.G.left) (cf : Fin (O.S.Dw.mult σ) → Gs.functionField),
        IsCombAtG O.s.T.Z.t x uu aG w ∧ IsCombAtG O.s.T.Z.t x v cf w ∧
          cf i = ((r ch)⁻¹ : Gs.functionFieldˣ) ∧ ∀ k, i < k → cf k = 0

variable (O c)

def CovCommon {Bg : Scheme.{0}} (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z) (G : ∀ σ', EigMet O.s.T.Z σ')
    {Y X Gs : Scheme.{0}} [IsIntegral Gs] (π : Y ⟶ Bs) (ρ : X ⟶ Y) (j : Gs ⟶ X) (πG : Gs ⟶ (O.var c).X)
    (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg) : Prop :=
  IsPullback jB (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) ∧
    IsFinite πB ∧ Set.range πB = Set.range (O.Φ.C c).π ∧
    (∀ σ n, O.met.hm c (some R) σ n = (O.Φ.C c).met (G (embOf O.κ.e σ)) n) ∧
    IsPullback j (πG ≫ (O.var c).str) (ρ ≫ π ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) ∧
    IsFinite πG ∧ Surjective πG ∧
    Gs.fromSpecStalk (genericPoint Gs) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) ∧
    jG ≫ jB = j ≫ ρ ≫ π ∧ jG ≫ πB = πG ≫ (O.Φ.C c).π

end GlobalTheory.PairCov

end
