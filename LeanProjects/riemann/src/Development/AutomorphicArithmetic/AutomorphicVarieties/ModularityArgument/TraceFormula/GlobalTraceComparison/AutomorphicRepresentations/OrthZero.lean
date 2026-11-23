import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelG borelF borelA borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def kI (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Kinf E n →* GA E n := (infGL E n).comp Unitary.toUnits

def TypeF (K : Subgroup (GL (Fin n) (Af E))) (W : Submodule ℂ (Kinf E n → ℂ)) (f : GA E n → ℂ) : Prop :=
  (∀ u ∈ K, ∀ g, f (g * finGL E n u) = f g) ∧ ∀ g, (fun k : Kinf E n => f (g * kI E n k)) ∈ W

def LeftType (K : Subgroup (GL (Fin n) (Af E))) (W : Submodule ℂ (Kinf E n → ℂ)) (φ : H E n 0 → ℂ) : Prop :=
  (∀ u ∈ K, ∀ y : H E n 0, φ ((finGL E n u, 1) * y) = φ y) ∧ ∀ y : H E n 0, (fun k : Kinf E n => φ (((kI E n k)⁻¹, 1) * y)) ∈ W

def RInv {Γ : Type} [Group Γ] (W : Submodule ℂ (Γ → ℂ)) : Prop := ∀ f ∈ W, ∀ k, (fun x => f (x * k)) ∈ W

def cvF (μ : Measure (H E n 0)) (φ : H E n 0 → ℂ) (u : ℝ → ℂ) (f : GA E n → ℂ) (x : GA E n) : ℂ :=
  ∫ y, φ y * u (ldet y) * f (x * y.1) ∂μ

def Slab (D : Dom E n 0) (f : GA E n → ℂ) : Prop :=
  Continuous f ∧ (∀ γ g, f (ratGL E n γ * g) = f g) ∧ (∀ t g, f (splitCentre E n t * g) = f g) ∧
    ∀ u : ℝ → ℂ, Continuous u → HasCompactSupport u → MemLp (fun x : H E n 0 => f x.1 * u (ldet x)) 2 D.ν

def prW (D : Dom E n 0) (u : ℝ → ℂ) (a b : GA E n → ℂ) : ℂ := ∫ x, starRingEnd ℂ (a x.1) * b x.1 * u (ldet x) ∂D.ν

def InS (D : Dom E n 0) (π : CuspSub E n) (f : GA E n → ℂ) : Prop :=
  ∀ u : ℝ → ℂ, Continuous u → HasCompactSupport u → ∃ v ∈ piSp D π Unit,
    (v () : H E n 0 → ℂ) =ᵐ[D.ν] fun x => f x.1 * u (ldet x)

end Defs

def TensType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (μa : Measure (G n)) (μb : Measure (G 0)),
  μa.IsHaarMeasure → μb.IsHaarMeasure →
  ∀ (Ma : Mods E n) (Mb : Mods E 0) (κ : Type) (ka : Kers Ma) (kb : Kers Mb) va vb (R : ℝ) (ψ : Matrix κ κ (Hf E n 0 → ℂ))
    (U : Subgroup (Hf E n 0)), IsMults μa ka va R → IsMults μb kb vb R → IsFinM ψ → IsOpen (U : Set (Hf E n 0)) →
    (∀ x y, ∀ u ∈ U, ∀ h, ψ x y (u * h) = ψ x y h) → ∀ i j, IsTestH (tens ka kb ψ i j) ∧
      ∃ (K : Subgroup (GL (Fin n) (Af E))) (W : Submodule ℂ (Kinf E n → ℂ)), IsOpen (K : Set (GL (Fin n) (Af E))) ∧
        IsCompact (K : Set (GL (Fin n) (Af E))) ∧ FiniteDimensional ℂ W ∧ RInv W ∧ LeftType K W (tens ka kb ψ i j)

def DetZero : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  (∀ k : Kinf E n, logAbs (kI E n k).val.det = 0) ∧ ∀ K : Subgroup (GL (Fin n) (Af E)), IsCompact (K : Set (GL (Fin n) (Af E))) →
    ∀ k ∈ K, logAbs (finGL E n k).val.det = 0

def CvType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Dom E n 0) (K : Subgroup (GL (Fin n) (Af E)))
  (W : Submodule ℂ (Kinf E n → ℂ)) (φ : H E n 0 → ℂ) (u : ℝ → ℂ) (f : GA E n → ℂ), IsCompact (K : Set (GL (Fin n) (Af E))) →
    FiniteDimensional ℂ W → IsTestH φ → LeftType K W φ → Continuous u → Continuous f → TypeF K W (cvF D.μ φ u f)

def CvIn : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ ψ ∈ π.V, Slab D ψ.1 ∧ ∀ (φ : H E n 0 → ℂ) (u : ℝ → ℂ), IsTestH φ → Continuous u →
    Slab D (cvF D.μ φ u ψ.1) ∧ InS D π (cvF D.μ φ u ψ.1) ∧ InS D π ψ.1

def WtInd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (a b : GA E n → ℂ),
  Slab D a → Slab D b → ∀ u : ℝ → ℂ, Continuous u → HasCompactSupport u →
    Integrable (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) D.ν ∧
    (∀ w : ℝ → ℂ, Continuous w → HasCompactSupport w → ∫ s, w s = 1 → prW D u a b = (∫ s, u s) * prW D w a b) ∧
    ∀ g : GA E n, logAbs g.val.det = 0 → Slab D (fun x => a (x * g)) ∧ prW D u (fun x => a (x * g)) (fun x => b (x * g)) = prW D u a b

def OrthZero : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ f : GA E n → ℂ, Slab D f → InS D π f →
    (∀ ψ ∈ π.V, ∀ u : ℝ → ℂ, Continuous u → HasCompactSupport u → prW D u ψ.1 f = 0) → f = 0

def FormEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ D : Dom E n 0,
  ∃ (F : Submodule ℂ (GA E n → ℂ)) (B : F →ₗ⋆[ℂ] F →ₗ[ℂ] ℂ), (∀ f, f ∈ F ↔ Slab D f) ∧
    (∀ a b, starRingEnd ℂ (B a b) = B b a) ∧ (∀ a, a ≠ 0 → 0 < (B a a).re) ∧
    (∀ (a b : F) (u : ℝ → ℂ), Continuous u → HasCompactSupport u → prW D u a b = (∫ s, u s) * B a b) ∧
    ∀ g : GA E n, logAbs g.val.det = 0 → ∀ a : F, (fun x => a.1 (x * g)) ∈ F ∧
      ∀ a' b b' : F, (∀ x, a'.1 x = a.1 (x * g)) → (∀ x, b'.1 x = b.1 (x * g)) → B a' b' = B a b

def AbsType : Prop := ∀ (Γ F : Type) [Group Γ] [AddCommGroup F] [Module ℂ F] (R : Representation ℂ Γ F) (B : F →ₗ⋆[ℂ] F →ₗ[ℂ] ℂ)
  (W : Submodule ℂ (Γ → ℂ)) (V Y : Submodule ℂ F) (z : F), (∀ a b, starRingEnd ℂ (B a b) = B b a) → (∀ a, a ≠ 0 → 0 < (B a a).re) →
    (∀ k a b, B (R k a) (R k b) = B a b) → RInv W → (∀ k, ∀ v ∈ V, R k v ∈ V) →
    (∀ v ∈ V, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => R k v))) → FiniteDimensional ℂ Y →
    (∀ v ∈ V, (∀ l : F →ₗ[ℂ] ℂ, (fun k => l (R k v)) ∈ W) → v ∈ Y) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => R k z)) → (∀ l : F →ₗ[ℂ] ℂ, (fun k => l (R k z)) ∈ W) →
    ∃ y ∈ V, y ∈ Y ∧ ∀ v ∈ V, B v (z - y) = 0

def TypeIn : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ (K : Subgroup (GL (Fin n) (Af E))) (W : Submodule ℂ (Kinf E n → ℂ)), IsOpen (K : Set (GL (Fin n) (Af E))) →
    IsCompact (K : Set (GL (Fin n) (Af E))) → FiniteDimensional ℂ W → RInv W →
    ∀ f : GA E n → ℂ, Slab D f → InS D π f → TypeF K W f → ∃ ψ ∈ π.V, ψ.1 = f

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
