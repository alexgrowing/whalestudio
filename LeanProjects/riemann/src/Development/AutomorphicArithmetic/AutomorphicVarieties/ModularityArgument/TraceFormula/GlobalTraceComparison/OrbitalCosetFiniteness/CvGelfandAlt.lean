import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.EvaluationAtUnitaryOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8 UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

def OrbFin {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) : Prop :=
  ∀ C : Set G, IsCompact C → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) |
    (Quotient.out q)⁻¹ * δ * θ (Quotient.out q) ∈ C}.Finite

abbrev th2 {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) : GLw a w × GLw b w →* GLw a w × GLw b w :=
  (thL a w).prodMap (thL b w)

def gen2 {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (p : Fin (a + 1) × Fin (b + 1)) :
    GLw a w × GLw b w → ℂ := fn2 a b w (.gen p)

def OrbFub : Prop := ∀ (T X Y : Type) [Group T] [MulAction T X] [MulAction T Y] (C : Subgroup T) [C.Normal],
  (∀ x : X, MulAction.stabilizer T x ≤ C) → (∀ y : Y, MulAction.stabilizer T y ≤ C) → ∀ F : X → Y → ℂ,
  (∀ (t : T) x y, F (t • x) (t • y) = F x y) → (∀ x, {y | F x y ≠ 0}.Finite) → (∀ y, {x | F x y ≠ 0}.Finite) →
  {q : MulAction.orbitRel.Quotient T X | ∃ y, F (Quotient.out q) y ≠ 0}.Finite →
  ∑ᶠ q : MulAction.orbitRel.Quotient T X,
      (((MulAction.stabilizer T (Quotient.out q)).relIndex C : ℕ) : ℂ) * ∑ᶠ y, F (Quotient.out q) y =
    ∑ᶠ q : MulAction.orbitRel.Quotient T Y,
      (((MulAction.stabilizer T (Quotient.out q)).relIndex C : ℕ) : ℂ) * ∑ᶠ x, F x (Quotient.out q)

def TwSwap : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) →
  ∀ θ : G →* G, Continuous θ → (∀ x, θ (θ x) = x) → (∀ k ∈ K, θ k ∈ K) → ∀ δ : G, OrbFin θ K δ →
  ∀ f g : G → ℂ, IsHecke K f → IsHecke K g → IsHecke K (f ∘ θ) ∧ twOrb θ K δ (cv K f g) = twOrb θ K δ (cv K g (f ∘ θ))

def TwLin : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) →
  ∀ θ : G →* G, (∀ k ∈ K, θ k ∈ K) → ∀ δ : G, OrbFin θ K δ → ∀ (f g : G → ℂ) (c : ℂ), IsHecke K f → IsHecke K g →
  twOrb θ K δ (fun y => f y + c * g y) = twOrb θ K δ f + c * twOrb θ K δ g

def CvRing : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) →
  ∀ f g h : G → ℂ, IsHecke K f → IsHecke K g → IsHecke K h →
    cv K (cv K f g) h = cv K f (cv K g h) ∧ cv K f ((K : Set G).indicator 1) = f ∧ cv K ((K : Set G).indicator 1) f = f ∧
    ∀ c d : ℂ, (cv K f fun y => c * g y + d * h y) = fun y => c * cv K f g y + d * cv K f h y

def CvGelfand : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) →
  ∀ τ : G → G, (∀ x y, τ (x * y) = τ y * τ x) → (∀ x, τ (τ x) = x) → (∀ k ∈ K, τ k ∈ K) →
  (∀ x, ∃ k ∈ K, ∃ k' ∈ K, τ x = k * x * k') → ∀ f g : G → ℂ, IsHecke K f → IsHecke K g → cv K f g = cv K g f

def CvComm2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (f g : GLw a w × GLw b w → ℂ),
  IsHecke (K2 a b w) f → IsHecke (K2 a b w) g → cv (K2 a b w) f g = cv (K2 a b w) g f

def Th2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (w : Pl E), ¬ IsSplitAt w →
  Continuous (th2 a b w) ∧ (∀ x, th2 a b w (th2 a b w x) = x) ∧ (∀ k ∈ K2 a b w, th2 a b w k ∈ K2 a b w) ∧
  ∀ y : GLw a w × GLw b w, (nrmL a w y.1).val.charpoly.Separable → (nrmL b w y.2).val.charpoly.Separable →
    OrbFin (th2 a b w) (K2 a b w) y

def GenTw : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (w : Pl E), ¬ IsSplitAt w → ∀ p : Fin (a + 1) × Fin (b + 1),
  cv (K2 a b w) (gen2 a b w (Fin.last a, Fin.last b)) (gen2 a b w p ∘ th2 a b w) = gen2 a b w (p.1.rev, p.2.rev)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th
