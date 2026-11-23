import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellAbs

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.Cell

variable {D : D7} {p : ℕ}

def cB (g : G D p) : Mx D p p := ((mat g).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

def dB (g : G D p) : Mx D p p := ((mat g).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

def cell (e : AE D) : Set (G D p) := {g | IsUnit (Matrix.det ((1 - e) • (1 : Mx D p p) + e • cB g))}

def UnitCrit : Prop := ∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e →
  ∃ (m : ℕ) (Ω : Fin m → Type) (_ : ∀ i, Field (Ω i)) (φ : ∀ i, AE D →+* Ω i), (∀ i, φ i e = 1) ∧
    ∀ z : AE D, IsUnit (1 - e + e * z) ↔ ∀ i, φ i z ≠ 0

def CellAlg : Prop := ∀ (D : D7) (p : ℕ) (nb : hermA D p → G D p), IsNMap nb → ∀ w, IsW w → ∀ (S : Finset (Pl D)) e, IsIdem S e →
  ∃ τ : G D p → hermS D p e, IsCell (P D p) (cell e) τ w (fun y => nb y.1) ∧ (∀ g ∈ cell e, ∀ u ∈ KOff D p S, g * u ∈ cell e) ∧
    ∀ g ∈ cell e, mm (e • cB g) (τ g).1.1 = e • dB g

def Decomp : Prop := ∀ (D : D7) (p : ℕ) (nb : hermA D p → G D p), IsNMap nb → ∀ w, IsW w → ∀ (S : Finset (Pl D)) e, IsIdem S e →
  ∀ g ∈ cell e, ∀ y : hermS D p e, mm (e • cB g) y.1.1 = e • dB g →
    ∃ q ∈ P D p, ∃ u ∈ KOff D p S, g = q * (w * nb y.1) * u ∧ ∀ x : hermS D p e, nb x.1 * u = u * nb x.1

def Move : Prop := ∀ (D : D7) (p : ℕ) (S : Finset (Pl D)) e, IsIdem S e → ∀ g : G D p, ∃ y : HermE D p,
  IsUnit (Matrix.det ((1 - e) • (1 : Mx D p p) + e • (cB g - mm (dB g) (rat y.1))))

def SmallRat : Prop := ∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∀ V ∈ 𝓝 (0 : AE D), ∀ M : ℕ,
  ∃ t : Fin M → ℚ, Function.Injective t ∧ ∀ j, incA D (t j : D.host.E) * e ∈ V

def FewC : Prop := ∀ (D : D7) (p : ℕ) (mu : (G D p → ℂ) → ℂ) (h : G D p → ℝ) (nb : hermA D p → G D p), IsNMap nb → ∀ w, IsW w →
  (∀ y, Inv (P D p) h mu (w * nb y * w⁻¹)) → ∀ (S : Finset (Pl D)) e, IsIdem S e → Few (P D p) h mu (cell e)

def SetC : Prop := ∀ (D : D7) (p : ℕ) (mu : (G D p → ℂ) → ℂ), IsResMu mu → ∃ h : G D p → ℝ, Setup (P D p) h mu ∧
  (∀ f, IsRho f ↔ Sec (P D p) h f) ∧ (∀ (S : Finset (Pl D)), ∀ u ∈ KOff D p S, ∀ g, h (g * u) = h g) ∧
  ∀ nb, IsNMap nb → ∀ w, IsW w → ∀ y, Inv (P D p) h mu (nb y) ∧ Inv (P D p) h mu (w * nb y * w⁻¹)

def TopC : Prop := ∀ (D : D7) (p : ℕ) (e : AE D), T2Space (G D p) ∧ LocallyCompactSpace (G D p) ∧
  SecondCountableTopology (G D p) ∧ T2Space (hermS D p e) ∧ LocallyCompactSpace (hermS D p e) ∧
  SecondCountableTopology (hermS D p e) ∧ BorelSpace (hermS D p e)

end PositivityTheory.Rg.Rsw.Cell

end
