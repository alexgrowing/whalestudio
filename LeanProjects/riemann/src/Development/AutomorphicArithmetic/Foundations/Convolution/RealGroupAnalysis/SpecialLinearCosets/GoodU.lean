import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I

abbrev SB (X : Type) [TopologicalSpace X] : Submodule ℂ (X → ℂ) := GroundTheory.LocalField.schwartzBruhat X

def ind {G : Type} [Group G] (U : Subgroup G) : G → ℂ := (U : Set G).indicator fun _ => 1

def Lgrp (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  ∀ N ∈ 𝓝 (1 : G), ∃ U : Subgroup G, IsOpen (U : Set G) ∧ IsCompact (U : Set G) ∧ (U : Set G) ⊆ N

def MC {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {c | ∃ (Λ : V →ₗ[ℂ] ℂ) (f : V), c = fun x => Λ (ρ x f)}

section Loc

variable {F : Type} [Field F] [NumberField F] (v : P F)

instance : MeasurableSpace (Kv v) := borel _
instance : BorelSpace (Kv v) := ⟨rfl⟩

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) (Kv v)

abbrev SL : Type := Matrix.SpecialLinearGroup (Fin 2) (Kv v)

abbrev GLv : Type := GL (Fin 2) (Kv v)

def ψl (x : Kv v) : ℂ := ((localAdelicChar F v x : Circle) : ℂ)

def μ2 : Measure (Fin 2 → Kv v) := localMeasurePi (localAdelicChar F v)

variable {v}

def cols (c c' : Fin 2 → Kv v) : M2 v := !![c 0, c' 0; c 1, c' 1]

def sw (X : M2 v) : M2 v := !![X 0 1, X 0 0; X 1 1, X 1 0]

def Pt (a : M2 v → ℂ) (X : M2 v) : ℂ :=
  ∫ c', a (cols (fun i => X i 1) c') * ψl v (X 0 0 * c' 1 - X 1 0 * c' 0) ∂(μ2 v)

def IM (b : M2 v → ℂ) : ℂ := ∫ p : (Fin 2 → Kv v) × (Fin 2 → Kv v), b (cols p.1 p.2) ∂((μ2 v).prod (μ2 v))

def BM (X Y : M2 v) : Kv v := X 0 1 * Y 1 0 + X 1 0 * Y 0 1 - X 0 0 * Y 1 1 - X 1 1 * Y 0 0

def dd (x : GLv v) : GLv v := dL 1 (Matrix.GeneralLinearGroup.det x)

structure InvI (I : SB (SL v) →ₗ[ℂ] ℂ) : Prop where
  right : ∀ (g : SL v) (a a' : SB (SL v)), (∀ m, a'.1 m = a.1 (m * g)) → I a' = I a
  conj : ∀ (x : GLv v) (a a' : SB (SL v)),
    (∀ m m' : SL v, m'.1 = (x⁻¹).val * m.1 * x.val → a'.1 m = a.1 m') → I a' = I a
  ne : ∀ (U : Subgroup (SL v)) (a : SB (SL v)), IsOpen (U : Set (SL v)) → a.1 = ind U → I a ≠ 0

variable (v)

def mat (θ : Kv v) (X : V4 F) : M2 v :=
  !![cp v (X 1), cp v (X 2) + cp v (X 3) * θ; cp v (X 2) - cp v (X 3) * θ, cp v (X 0)]

def away (X : V4 F) : V4 F := fun i => X i - sg v (cp v (X i))

def ten (θ : Kv v) (u : V4 F → ℂ) (b : M2 v → ℂ) : V4 F → ℂ := fun X => u (away v X) * b (mat v θ X)

def GoodU [IsTotallyReal F] (δ : F) (θ : Kv v) (u : V4 F → ℂ) : Prop :=
  ∀ b ∈ SB (M2 v), ∃ φ ∈ Fock δ, φ.1 = ten v θ u b

end Loc

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (θ : Kv v)

def sE (k : Kv v) : A E := D.mkE (sg v (k / 2)) (sg v (k / (2 * θ)))

def nbar (s : Kv v) : GL (Fin 2) (A E) := gl (nU (D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ))))))

structure Splt (J : GLv v →* GL (Fin 2) (A E)) : Prop where
  sq : θ ^ 2 = algebraMap F (Kv v) D.δ
  ne : θ ≠ 0
  val : ∀ x i j, (J x).val i j = (1 : Matrix (Fin 2) (Fin 2) (A E)) i j + sE D v θ (x.val i j - (1 : M2 v) i j)
  fin : ∀ x, ∃ k, J x = finGL E 2 k

variable [IsTotallyReal F] [IsTotallyComplex E] {D} (W : Weil D)

def Mod (u : V4 F → ℂ) : Prop :=
  GoodU v D.δ θ u ∧ ∀ j, IsJ v j → ∀ (g : SL v), ∀ a ∈ SB (M2 v), ∀ φ : S4 F, φ.1 = ten v θ u (Pt a) →
    (W.Om (j g) φ).1 = ten v θ u (Pt fun m => a (m * g.1))

end Ext

end UpperTheory.ConvolutionTheory.R2.I

end
