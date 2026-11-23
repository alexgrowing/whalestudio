import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseAt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCov

variable {D : D7} {O : Setup D} {c : O.s.Comp} {Bs : Scheme.{0}} {E : D.what₂.Tau × Bool → Bs.Modules}

def FlagAgree (hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a)) {Bg : Scheme.{0}} (jB : Bg ⟶ Bs)
    (πB : Bg ⟶ gen O.s.T.Z) (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) {Y₀ : Scheme.{0}}
    (π₀ : Y₀ ⟶ Bs) (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    {G : Scheme.{0}} [IsIntegral G] (j : G ⟶ Y₀) (φ : (O.var c).Fn →+* G.functionField) (jG : G ⟶ Bg)
    (a : D.what₂.Tau × Bool) (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)) : Prop :=
  haveI := (hE a).isQuasicoherent
  (∀ (k : Fin (rkB D.what₂.Tau O.N O.j a + 1)) (V : Bs.Opens) (f : Fin (rkB D.what₂.Tau O.N O.j a) → Γ(E a, V))
    (hf : IsFrame f) (W : Y₀.Opens) (hWV : W ≤ π₀ ⁻¹ᵁ V) (t : Γ((fl₀ a).F k, W))
    (hx : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W) (hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V),
      let aG : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField := fun b =>
        TangentOrigin.evalPt (genPt G ≫ j) W hx (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι k).app W t) b)
      let uu := u a V f hf G.functionField (genPt G ≫ jG) hxV
      let v : Fin (O.S.Dw.mult (embB D a)) → (Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left) :=
        fun l => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) l
      let x := genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z
      cond a.2
        (∃ (w : Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left)
            (cf : Fin (O.S.Dw.mult (embB D a)) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu aG w ∧ IsCombAtG O.s.T.Z.t x v cf w ∧ ∀ l : Fin (O.S.Dw.mult (embB D a)), (k : ℕ) ≤ l → cf l = 0)
        (∀ (l : Fin (O.S.Dw.mult (embB D a))) (d : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu d (v l) → (l : ℕ) + k < rkB D.what₂.Tau O.N O.j a → ∑ b, aG b * d b = 0)) ∧
  ∀ (i : Fin (rkB D.what₂.Tau O.N O.j a)) (ch : (((fl₀ a).root i).pull j).ι) (V : Bs.Opens)
    (f : Fin (rkB D.what₂.Tau O.N O.j a) → Γ(E a, V)) (hf : IsFrame f) (W : Y₀.Opens) (hW : W ≤ (ch PUnit.unit).U)
    (hWV : W ≤ π₀ ⁻¹ᵁ V) (t : Γ((fl₀ a).F i.succ, W)), ((fl₀ a).π i).app W t = Twist.resM _ hW ((ch PUnit.unit).e 0) →
    ∀ (hx : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W) (hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V),
      let aG : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField := fun b =>
        TangentOrigin.evalPt (genPt G ≫ j) W hx
          (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι i.succ).app W t) b)
      let uu := u a V f hf G.functionField (genPt G ≫ jG) hxV
      let v : Fin (O.S.Dw.mult (embB D a)) → (Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left) :=
        fun l => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) l
      let x := genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z
      cond a.2
        (∃ (w : Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left)
            (cf : Fin (O.S.Dw.mult (embB D a)) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu aG w ∧ IsCombAtG O.s.T.Z.t x v cf w ∧ cf (Fin.cast hr i) ≠ 0)
        (∀ (l : Fin (O.S.Dw.mult (embB D a))) (d : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu d (v l) → (l : ℕ) + i + 1 = rkB D.what₂.Tau O.N O.j a → ∑ b, aG b * d b ≠ 0)

end GlobalTheory.FlagCov

end
