import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCov

def genPt (G : Scheme.{0}) [IsIntegral G] : Sp G.functionField ⟶ G := G.fromSpecStalk (genericPoint G)

variable {D : D7} (O : Setup D) (B R : ℝ) (c : O.s.Comp) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
  (E : D.what₂.Tau × Bool → Bs.Modules) (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a))

def LieWit {Bg : Scheme.{0}} (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) (G : ∀ σ', EigMet O.s.T.Z σ') : Prop :=
  IsPullback jB (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) ∧
    IsFinite πB ∧ Set.range πB = Set.range (O.Φ.C c).π ∧
    (∀ a, IsLieFrames O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (!a.2) (u a)) ∧
    (∀ a, IsLieLat O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (ArIn.ind (FlagAr.setB O.Y B)) (fun _ => True) (u a)) ∧
    (∀ σ n, O.met.hm c (some R) σ n = (O.Φ.C c).met (G (embOf O.κ.e σ)) n) ∧
    ∀ a, ∃ hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a),
      IsLieMet O.s.T.Z O.κ.e q jB πB (E a) _ (embB D a) (!a.2) hr G (h a) (u a)

theorem lieBase_iff : LieBase O B R c q E h ↔ ∃ (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) (G : ∀ σ', EigMet O.s.T.Z σ'),
    LieWit O B R c q E h jB πB u G := by
  constructor
  · rintro ⟨Bg, jB, πB, pb, u, G, h1, h2, h3, h4, h5, h6⟩
    exact ⟨Bg, jB, πB, u, G, pb, h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨Bg, jB, πB, u, G, pb, h1, h2, h3, h4, h5, h6⟩
    exact ⟨Bg, jB, πB, pb, u, G, h1, h2, h3, h4, h5, h6⟩

variable {O c E}

def IsFrameSec (hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a)) {Bg : Scheme.{0}} (jB : Bg ⟶ Bs)
    (πB : Bg ⟶ gen O.s.T.Z) (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) {Y₀ : Scheme.{0}}
    (π₀ : Y₀ ⟶ Bs) (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    {G : Scheme.{0}} [IsIntegral G] (j : G ⟶ Y₀) (φ : (O.var c).Fn →+* G.functionField) (jG : G ⟶ Bg)
    (a : D.what₂.Tau × Bool) (i : Fin (rkB D.what₂.Tau O.N O.j a))
    (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a))
    (r : (((fl₀ a).root i).pull j).ι → G.functionFieldˣ) : Prop :=
  haveI := (hE a).isQuasicoherent
  ∀ (ch : (((fl₀ a).root i).pull j).ι) (V : Bs.Opens) (f : Fin (rkB D.what₂.Tau O.N O.j a) → Γ(E a, V))
    (hf : IsFrame f) (W : Y₀.Opens) (hW : W ≤ (ch PUnit.unit).U) (hWV : W ≤ π₀ ⁻¹ᵁ V)
    (t : Γ((fl₀ a).F i.succ, W)), ((fl₀ a).π i).app W t = Twist.resM _ hW ((ch PUnit.unit).e 0) →
    ∀ (hx : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W) (hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V),
      let aG : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField := fun b =>
        TangentOrigin.evalPt (genPt G ≫ j) W hx
          (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι i.succ).app W t) b)
      let uu := u a V f hf G.functionField (genPt G ≫ jG) hxV
      let v : Fin (O.S.Dw.mult (embB D a)) → (Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left) :=
        fun k => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) k
      let x := genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z
      cond a.2
        (∃ (w : Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left)
            (cf : Fin (O.S.Dw.mult (embB D a)) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu aG w ∧ IsCombAtG O.s.T.Z.t x v cf w ∧
            cf (Fin.cast hr i) = ((r ch)⁻¹ : G.functionFieldˣ) ∧ ∀ k, Fin.cast hr i < k → cf k = 0)
        (∀ (k : Fin (O.S.Dw.mult (embB D a))) (d : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu d (v k) →
            ((k : ℕ) + i + 1 < rkB D.what₂.Tau O.N O.j a → ∑ b, aG b * d b = 0) ∧
            ((k : ℕ) + i + 1 = rkB D.what₂.Tau O.N O.j a → ∑ b, aG b * d b = ((r ch)⁻¹ : G.functionFieldˣ)))

def FlagCover (hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a)) {Bg : Scheme.{0}} (jB : Bg ⟶ Bs)
    (πB : Bg ⟶ gen O.s.T.Z) (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) {Y₀ : Scheme.{0}}
    (π₀ : Y₀ ⟶ Bs) (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    {G : Scheme.{0}} [IsIntegral G] (j : G ⟶ Y₀) (πG : G ⟶ (O.var c).X) (φ : (O.var c).Fn →+* G.functionField)
    (jG : G ⟶ Bg) (r : ∀ a i, (((fl₀ a).root i).pull j).ι → G.functionFieldˣ) : Prop :=
  jG ≫ jB = j ≫ π₀ ∧ jG ≫ πB = πG ≫ (O.Φ.C c).π ∧
    ∀ a i (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)),
      IsFrameSec hE jB πB u π₀ fl₀ j φ jG a i hr (r a i)

end GlobalTheory.FlagCov

end
