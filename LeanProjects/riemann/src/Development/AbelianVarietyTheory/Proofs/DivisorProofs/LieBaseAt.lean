import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BcRead

variable {D : D7} (O : Setup D)

def LieGen (c : O.s.Comp) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (E : D.what₂.Tau × Bool → Bs.Modules)
    {Bg : Scheme.{0}} (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) : Prop :=
  IsPullback jB (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) ∧
    IsFinite πB ∧ Set.range πB = Set.range (O.Φ.C c).π ∧
    ∀ a, IsLieFrames O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (!a.2) (u a)

def LieFin (P : Finset ℕ) {Bs : Scheme.{0}} (E : D.what₂.Tau × Bool → Bs.Modules)
    {Bg : Scheme.{0}} (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) : Prop :=
  ∀ a, IsLieLat O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (ArIn.ind P) (fun _ => True) (u a)

def LieInf (R : ℝ) (c : O.s.Comp) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) {Bg : Scheme.{0}} (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) : Prop :=
  ∃ G : ∀ σ', EigMet O.s.T.Z σ', (∀ σ n, O.met.hm c (some R) σ n = (O.Φ.C c).met (G (embOf O.κ.e σ)) n) ∧
    ∀ a, ∃ hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a),
      IsLieMet O.s.T.Z O.κ.e q jB πB (E a) _ (embB D a) (!a.2) hr G (h a) (u a)

def LieBaseAt (P : Finset ℕ) (R : ℝ) (c : O.s.Comp) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (E : D.what₂.Tau × Bool → Bs.Modules) (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) : Prop :=
  ∃ (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB),
    LieGen O c q E jB πB u ∧ LieFin O P E jB πB u ∧ LieInf O R c q E h jB πB u

theorem lieBase_iff (B R : ℝ) (c : O.s.Comp) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (E : D.what₂.Tau × Bool → Bs.Modules) (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) :
    LieBase O B R c q E h ↔ LieBaseAt O (FlagAr.setB O.Y B) R c q E h :=
  ⟨fun ⟨Bg, jB, πB, pb, u, G, h₁, h₂, h₃, h₄, h₅, h₆⟩ => ⟨Bg, jB, πB, u, ⟨pb, h₁, h₂, h₃⟩, h₄, G, h₅, h₆⟩,
    fun ⟨Bg, jB, πB, u, ⟨pb, h₁, h₂, h₃⟩, h₄, G, h₅, h₆⟩ => ⟨Bg, jB, πB, pb, u, G, h₁, h₂, h₃, h₄, h₅, h₆⟩⟩

end GlobalTheory.BcRead

end
