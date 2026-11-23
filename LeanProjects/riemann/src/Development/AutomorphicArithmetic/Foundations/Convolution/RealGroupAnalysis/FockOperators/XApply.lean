import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo

section Base

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def at1 {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (t : ℝ) : A F := TR.sInf F (Pi.single w t)

def cw {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (a : A F) : ℂ := ((TR.pInf F a w : ℝ) : ℂ)

def cc : ℂ := -(2 * Real.pi * Complex.I)

structure Ops where
  x : InfinitePlace F → Fin 4 → Module.End ℂ (S4 F)
  d : InfinitePlace F → Fin 4 → Module.End ℂ (S4 F)
  x_apply : ∀ w i φ v, (x w i φ).1 v = cw w (v i) * φ.1 v
  d_spec : ∀ w i φ v, HasDerivAt (fun t : ℝ => φ.1 (v + Pi.single i (at1 w t))) ((d w i φ).1 v) 0

variable {F}

def Vac (δ : F) : Submodule ℂ (S4 F) where
  carrier := {φ | ∀ v v', finPartPi v = finPartPi v' → φ.1 v * gauss δ v' = φ.1 v' * gauss δ v}
  add_mem' := fun {φ φ'} h h' v v' e => by
    change (φ.1 v + φ'.1 v) * _ = (φ.1 v' + φ'.1 v') * _
    rw [add_mul, add_mul, h v v' e, h' v v' e]
  zero_mem' := fun v v' _ => by
    change (0 : ℂ) * _ = 0 * _
    rw [zero_mul, zero_mul]
  smul_mem' := fun c φ h v v' e => by
    change (c * φ.1 v) * _ = (c * φ.1 v') * _
    rw [mul_assoc, mul_assoc, h v v' e]

omit [IsTotallyReal F] in

def Fix (δ : F) (Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)) : Submodule ℂ (S4 F) where
  carrier := {φ | ∀ a : V4 F, (∀ i, (a i).1 = 0 ∧ (a i).2 ∈ Λ) → ∀ v, φ.1 (v + a) = φ.1 v ∧ ψ (B4 δ a v) * φ.1 v = φ.1 v}
  add_mem' := fun {φ φ'} h h' a ha v => by
    refine ⟨?_, ?_⟩
    · change φ.1 (v + a) + φ'.1 (v + a) = φ.1 v + φ'.1 v
      rw [(h a ha v).1, (h' a ha v).1]
    · change _ * (φ.1 v + φ'.1 v) = φ.1 v + φ'.1 v
      rw [mul_add, (h a ha v).2, (h' a ha v).2]
  zero_mem' := fun a _ v => ⟨rfl, mul_zero _⟩
  smul_mem' := fun c φ h a ha v => by
    refine ⟨?_, ?_⟩
    · change c * φ.1 (v + a) = c * φ.1 v
      rw [(h a ha v).1]
    · change _ * (c * φ.1 v) = c * φ.1 v
      rw [mul_left_comm, (h a ha v).2]

omit [IsTotallyReal F] in

def FinOne (g : G1 F) : Prop := ∀ i j, (g i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2

variable (O : Ops F)

def Ops.Fk (N : Submodule ℂ (S4 F)) : ℕ → Submodule ℂ (S4 F)
  | 0 => N
  | m + 1 => Ops.Fk N m ⊔ ⨆ w, ⨆ i, (Ops.Fk N m).map (O.x w i)

def Ops.p (δ : F) (w : InfinitePlace F) : Fin 4 → Module.End ℂ (S4 F) :=
  ![(-cc) • O.x w 1, (-cc) • O.x w 0, (2 * cc) • O.x w 2, (-2 * cw w (rt δ) * cc) • O.x w 3]

def kap (δ : F) (w : InfinitePlace F) : Fin 4 → ℂ := ![1, 1, 2, -2 * cw w (rt δ)]

def Ops.e (δ : F) (w : InfinitePlace F) : Module.End ℂ (S4 F) :=
  cc • (O.x w 2 * O.x w 2 - cw w (rt δ) • (O.x w 3 * O.x w 3) - O.x w 1 * O.x w 0)

def Ops.f (δ : F) (w : InfinitePlace F) : Module.End ℂ (S4 F) :=
  (-cc⁻¹) • ((4 : ℂ)⁻¹ • (O.d w 2 * O.d w 2) - (4 * cw w (rt δ))⁻¹ • (O.d w 3 * O.d w 3) - O.d w 1 * O.d w 0)

def Ops.h (w : InfinitePlace F) : Module.End ℂ (S4 F) := (∑ i, O.x w i * O.d w i) + 2

end Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]

variable (F) in
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

def pl (τ : E →+* ℂ) : InfinitePlace F := InfinitePlace.mk (τ.comp (algebraMap F E))

variable (O : Ops F) (D : Dat F E)

def Ops.X (τ : E →+* ℂ) : Fin 2 → Fin 2 → Module.End ℂ (S4 F) :=
  ![![O.x (pl F τ) 1, O.x (pl F τ) 2 + τ D.θ • O.x (pl F τ) 3], ![O.x (pl F τ) 2 - τ D.θ • O.x (pl F τ) 3, O.x (pl F τ) 0]]

def Ops.DX (τ : E →+* ℂ) : Fin 2 → Fin 2 → Module.End ℂ (S4 F) :=
  ![![O.d (pl F τ) 1, (2 : ℂ)⁻¹ • (O.d (pl F τ) 2 + (τ D.θ)⁻¹ • O.d (pl F τ) 3)],
    ![(2 : ℂ)⁻¹ • (O.d (pl F τ) 2 - (τ D.θ)⁻¹ • O.d (pl F τ) 3), O.d (pl F τ) 0]]

def Ops.dE (τ : E →+* ℂ) (i j : Fin 2) : Module.End ℂ (S4 F) :=
  -(if i = j then 1 else 0) - ∑ b, O.X D τ j b * O.DX D τ i b

def Ops.dL (Y : Lie E 2) : Module.End ℂ (S4 F) := ∑ τ : E →+* ℂ, ∑ i, ∑ j, coord τ (Y i j) • O.dE D τ i j

variable {D} (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2)

def LieLift : Prop :=
  ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ Φ : Sm E 2, Φ.1 = lift W M f.1 φ → ∀ (Y : Lie E 2) h,
    (lie E 2 Y Φ).1 h = lift W M f.1 (O.dL D Y φ) h +
      ∑ τ : E →+* ℂ, coord τ (Y 0 0 + Y 1 1) * lift W M (TR.Eop (pl F τ) 1 1 f).1 φ h

def MoveE : Prop :=
  ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ w h, lift W M f.1 (O.e D.δ w φ) h = -lift W M (TR.Eop w 0 1 f).1 φ h

end UpperTheory.ConvolutionTheory.R2.Fo

end
