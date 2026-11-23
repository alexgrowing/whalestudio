import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Formalism.LocalToGlobal.IndefiniteReal.InjectiveDecompositionAction

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

abbrev Ix {D : D7} (V W : HSp D) : Type := Fin V.rank × Fin W.rank × Fin (nE D)

def Co {D : D7} (V W : HSp D) (x : WA V W) (a : Ix V W) : AF D.host.F := Phi V W x a.1 a.2.1 a.2.2

def CoordFinP : Prop :=
  ∀ (D : D7) (V W : HSp D) (x : WA V W), x.map (finPart D) = 0 → ∀ a, (Co V W x a).2 = 0

def CoordInfP : Prop :=
  ∀ (D : D7) (V W : HSp D) (x : WA V W), x.map (infPart D) = 0 → ∀ a, (Co V W x a).1 = 0

def SymplCoordP : Prop :=
  ∀ (D : D7) (V W : HSp D), ∃ c : Ix V W → Ix V W → D.host.F, ∀ x y : WA V W,
    symplH V W x y = ∑ a, ∑ b, algebraMap D.host.F (AF D.host.F) (c a b) * Co V W x a * Co V W y b

open scoped Classical in

def SelP : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∃ r : ℝ, 0 < r ∧ ∀ (q q' : F) (x x' : AF F),
    ‖eM F (algebraMap F (AF F) q + x).1‖ ≤ r → (algebraMap F (AF F) q + x).2 ∈ Ohat F →
    ‖eM F (algebraMap F (AF F) q' + x').1‖ ≤ r → (algebraMap F (AF F) q' + x').2 ∈ Ohat F →
    ‖eM F (x' - x).1‖ < r → (x' - x).2 ∈ Ohat F → q = q'

open scoped Classical in

def BumpP : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (r : ℝ), 0 < r → ∃ b : mixedEmbedding.mixedSpace F → ℝ,
    ContDiff ℝ ∞ b ∧ b 0 ≠ 0 ∧ ∀ y, b y ≠ 0 → ‖y‖ ≤ r

def PsiOpenP : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∃ G : AddSubgroup (Af F), IsOpen (G : Set (Af F)) ∧ (∀ y ∈ G, ∀ z ∈ Ohat F, z * y ∈ G) ∧
      ∀ y ∈ G, ψ (pairA F 0 y) = 1

def PsiSmoothP : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (k : ℕ) (s : (Fin k → ℝ) →+ Ainf D.host.F), Continuous s →
      ContDiff ℝ ∞ fun t => ψ (pairA D.host.F (s t) 0)

def ThetaNZStd : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D), IsStdChar D ψ (-1) → Formalism.IndefR.InjectiveDecompositionAction.ThetaNZ ψ V W

end Formalism.IndefR.PHeisTh

end
