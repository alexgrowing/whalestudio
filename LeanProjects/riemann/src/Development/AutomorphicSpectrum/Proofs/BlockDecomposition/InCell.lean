import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

def lowC (g : G D p) : Mx D p p :=
  (mat g).submatrix (fun i => finSumFinEquiv (Sum.inr i)) (fun j => finSumFinEquiv (Sum.inl j))

def lowD (g : G D p) : Mx D p p :=
  (mat g).submatrix (fun i => finSumFinEquiv (Sum.inr i)) (fun j => finSumFinEquiv (Sum.inr j))

def InCell (e : AE D) (g : G D p) : Prop := ∃ y : Mx D p p, mm y (lowC g) = e • (1 : Mx D p p)

def IsB (e : AE D) (g : G D p) (x : hermS D p e) : Prop := InCell e g ∧ mm (lowC g) x.1.1 = e • lowD g

open Classical in

def cellFn (e : AE D) (ξ : hermS D p e → ℝ) (g : G D p) : ℝ :=
  if h : ∃ x, IsB e g x then ξ h.choose else 0

def secV (D : D7) (p : ℕ) (S : Finset (Pl D)) : Submodule ℝ (G D p → ℝ) where
  carrier := {f | IsRho (fun g => (f g : ℂ)) ∧ ∀ u ∈ KOff D p S, ∀ g, f (g * u) = f g}
  add_mem' := by
    rintro f f' ⟨⟨c, l⟩, k⟩ ⟨⟨c', l'⟩, k'⟩
    refine ⟨⟨?_, ?_⟩, fun u hu g => by simp [k u hu, k' u hu]⟩
    · exact (c.add c').congr fun g => by simp
    · intro q hq a ha g
      have h1 := l q hq a ha g
      have h2 := l' q hq a ha g
      simp only [Pi.add_apply, Complex.ofReal_add] at *
      rw [h1, h2]; ring
  zero_mem' := by
    refine ⟨⟨by simpa using continuous_const, ?_⟩, fun _ _ _ => rfl⟩
    intro q hq a ha g
    simp
  smul_mem' := by
    rintro t f ⟨⟨c, l⟩, k⟩
    refine ⟨⟨?_, ?_⟩, fun u hu g => by simp [k u hu]⟩
    · exact ((continuous_const (y := (t : ℂ))).mul c).congr fun g => by simp
    · intro q hq a ha g
      have h1 := l q hq a ha g
      simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul] at *
      rw [h1]; ring

def Lf (mu : (G D p → ℂ) → ℂ) (f : G D p → ℝ) : ℝ := (mu fun g => (f g : ℂ)).re

end GlobalTheory.CompanionTheory.MuC

end
