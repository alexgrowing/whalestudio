import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Crv

open AlgebraicGeometry CategoryTheory

variable {K : Type} [Field K] {X : Scheme.{0}}

structure CurveIn (C : ACurve K) (ζ : Spec (CommRingCat.of K) ⟶ X) where

  x : ∀ i : C.I, Spec (CommRingCat.of (C.v i).valuationSubring) ⟶ X
  gen : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ x i = ζ
  ae : ∀ U : X.Opens, centre ζ ∈ U → {i | centre (x i) ∉ U}.Finite

variable {C : ACurve K} {ζ : Spec (CommRingCat.of K) ⟶ X}

def CurveIn.lieLat (Y : CurveIn C ζ) {G : Over X} [GrpObj G] {V : Type} [AddCommGroup V] [Module K V]
    (M : LieModel G ζ V) : C.I → AddSubgroup V := fun i =>
  AddSubgroup.closure {e | ∃ v : epsAt (Y.x i) ⟶ G, IsTanAt G (Y.x i) v ∧
    (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap (C.v i).valuationSubring.subtype)) ≫ v.left}

def CurveIn.IsDeg (Y : CurveIn C ζ) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (Λ : Lat ξ Ω)
    (n : ℤ) : Prop :=
  ∃ (h₀ : genPt ξ ⤳ centre ζ) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (s₀ : Ω) (s : C.I → Ω) (r : C.I → K),
    Λ.IsGenAt ⟨centre ζ, h₀⟩ s₀ ∧ (∀ i, Λ.IsGenAt ⟨centre (Y.x i), h i⟩ (s i)) ∧
      (∀ i, r i ≠ 0 ∧ ValAt ξ ζ (s i / s₀) (r i)) ∧ {i | C.v i (r i) ≠ 1}.Finite ∧
      n = ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (r i))

def coordDeg (C : ACurve K) {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)] (w : (Σ k, ι k) → K)
    (a : B → ℤ) : ℤ :=
  ∑ k, a k * ∑ᶠ i, (C.w i : ℤ) * WithZero.log (Finset.univ.sup fun c : ι k => C.v i (w ⟨k, c⟩))

def lmuExp {T : Type} (j q : ℕ) (μ : T → ℕ → ℤ) : (Σ s : T ⊕ T, Fin (Sum.elim (fun _ => j) (fun _ => q) s)) → ℤ
  | ⟨Sum.inl τ, i⟩ => -μ τ (i.1 + 1)
  | ⟨Sum.inr τ, i⟩ => μ τ (j + q - i.1)

end GlobalTheory.CompanionTheory.Ar.Crv
