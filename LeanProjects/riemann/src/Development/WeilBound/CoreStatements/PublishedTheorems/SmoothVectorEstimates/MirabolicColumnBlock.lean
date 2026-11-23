import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

section Ring

variable {R : Type} [CommRing R] {a : ℕ}

def Mir (m : ℕ) (γ : GL (Fin a) R) : Prop :=
  ∀ i k : Fin a, (m ≤ (i : ℕ) ∨ m < (k : ℕ)) → γ.val i k = (1 : Matrix (Fin a) (Fin a) R) i k

def GlobalTheory (m : ℕ) (γ : GL (Fin a) R) : Prop :=
  ∀ i k : Fin a, (m ≤ (i : ℕ) ∨ m ≤ (k : ℕ)) → γ.val i k = (1 : Matrix (Fin a) (Fin a) R) i k

def lastE (k : ℕ) (y : UnipotentBlockColumnIndex a k k → R) : R := ∑ t, if (t.1.1 : ℕ) + 1 = k then y t else 0

end Ring

abbrev LieI (ι : Type) (a : ℕ) : Type := Fin a → Fin a → ι → ℂ

section Arch

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

open Classical in

def orb (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (v : X) (M : LieI ι a) : X :=
  if h : IsUnit (Matrix.of M) then ρ h.unit v else 0

def oneI (ι : Type) (a : ℕ) : LieI ι a := Matrix.of.symm 1

def SmV (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (v : X) : Prop :=
  ContDiffOn ℝ ∞ (orb ρ v) {M | IsUnit (Matrix.of M)}

def RapidFam {V : Type} [NormedAddCommGroup V] (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X))
    (𝒢 : Submodule ℂ (V → X)) : Prop :=
  ∀ G ∈ 𝒢, Continuous G ∧ (∀ N : ℕ, ∃ C : ℝ, ∀ y, (1 + ‖y‖) ^ N * ‖G y‖ ≤ C) ∧
    ∃ D : LieI ι a → V → X, (∀ Z, D Z ∈ 𝒢) ∧
      ∀ y, ∃ D' : LieI ι a →L[ℝ] X, (∀ Z, D' Z = D Z y) ∧ HasFDerivAt (orb ρ (G y)) D' (oneI ι a)

end Arch

def FT {V X : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [NormedAddCommGroup X]
    [NormedSpace ℂ X] (μ : Measure V) (β : V →L[ℝ] V →L[ℝ] ℝ) (F : V → X) (y : V) : X :=
  ∫ x, Complex.exp (-(β x y : ℝ) * Complex.I) • F x ∂μ

def PolyBd {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) : Prop :=
  ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (g : GL (Fin a) (ι → ℂ)) x, ‖ρ g x‖ ≤
    C * (1 + ‖(Matrix.of.symm g.val : LieI ι a)‖ + ‖(Matrix.of.symm g⁻¹.val : LieI ι a)‖) ^ N * ‖x‖

def ForIso (P : ∀ (ι : Type) [Fintype ι] (a : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X],
    (GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) → Prop) : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)), PolyBd ρ → P ι a X ρ

def ForV (P : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V], Measure V → Prop) : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure], P V μ

def S1 : Prop := ForIso fun ι _ a X _ _ ρ => ∀ 𝒮 : Submodule ℂ X,
  (∀ v ∈ 𝒮, ∃ D : LieI ι a →L[ℝ] X, HasFDerivAt (orb ρ v) D (oneI ι a) ∧ ∀ Z, D Z ∈ 𝒮) → ∀ v ∈ 𝒮, SmV ρ v

def S2 : Prop := ForIso fun ι _ a X _ _ ρ =>
  SmV ρ 0 ∧ (∀ v w, SmV ρ v → SmV ρ w → SmV ρ (v + w)) ∧ (∀ (c : ℂ) v, SmV ρ v → SmV ρ (c • v)) ∧
  (∀ g v, SmV ρ v → SmV ρ (ρ g v)) ∧
  (∀ T : X →L[ℂ] X, (∀ g x, T (ρ g x) = ρ g (T x)) → ∀ v, SmV ρ v → SmV ρ (T v)) ∧
  ∀ v, SmV ρ v → ∃ D : LieI ι a →L[ℝ] X, HasFDerivAt (orb ρ v) D (oneI ι a) ∧ ∀ Z, SmV ρ (D Z)

def S3 : Prop := ForIso fun ι _ a X _ _ ρ => ForV fun V _ _ _ μ =>
  ∀ (u : V → GL (Fin a) (ι → ℂ)) (L : V →L[ℝ] LieI ι a), (∀ y, (u y).val = 1 + Matrix.of (L y)) →
    (∀ y, (u y)⁻¹.val = 1 - Matrix.of (L y)) → ∀ 𝒢 : Submodule ℂ (V → X), RapidFam ρ 𝒢 →
    ∀ G ∈ 𝒢, Integrable (fun y => ρ (u y) (G y)) μ ∧ SmV ρ (∫ y, ρ (u y) (G y) ∂μ)

def S4 : Prop := ForV fun V _ _ _ μ => ∀ β : V →L[ℝ] V →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) →
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (F : V → X), ContDiff ℝ ∞ F →
    HasCompactSupport F → Continuous (FT μ β F) ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ y, (1 + ‖y‖) ^ N * ‖FT μ β F y‖ ≤ C

def S5 : Prop := ForV fun V _ _ _ μ => ∀ β : V →L[ℝ] V →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) →
  ∃ c : ℂ, c ≠ 0 ∧ ∀ f : V → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ ξ,
    ∫ y, Complex.exp ((β ξ y : ℝ) * Complex.I) * FT μ β f y ∂μ = c * f ξ

def S6 : Prop := ForIso fun ι _ a X _ _ ρ => ForV fun V _ _ _ μ =>
  ∀ β : V →L[ℝ] V →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) → ∀ (O : Set V) (σ τ : V → LieI ι a), IsOpen O →
    ContDiffOn ℝ ∞ σ O → ContDiffOn ℝ ∞ τ O → (∀ x ∈ O, Matrix.of (σ x) * Matrix.of (τ x) = 1) →
    ∃ 𝒢 : Submodule ℂ (V → X), RapidFam ρ 𝒢 ∧ ∀ (η : V → ℂ) (w : X), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ O → SmV ρ w → FT μ β (fun x => η x • orb ρ w (σ x)) ∈ 𝒢

def S8 : Prop := ∀ (ι : Type) [Fintype ι] (χ : AddChar (ι → ℂ) ℂ), Continuous χ → (∀ z, ‖χ z‖ = 1) →
  ∃ l : (ι → ℂ) →L[ℝ] ℝ, ∀ z, χ z = Complex.exp ((l z : ℝ) * Complex.I)

def S7 : Prop := ForIso fun ι _ a X _ _ ρ => ∀ m : ℕ, m + 1 < a → ∀ χ : AddChar (ι → ℂ) ℂ, Continuous χ →
  (∀ z, ‖χ z‖ = 1) → (∀ z, (∀ w, χ (z * w) = 1) → z = 0) → ∀ U ∈ 𝓝 (1 : GL (Fin a) (ι → ℂ)),
  ∃ (η : GL (Fin a) (ι → ℂ) → ℂ) (r : GL (Fin a) (ι → ℂ) → GL (Fin a) (ι → ℂ)), η 1 ≠ 0 ∧ r 1 = 1 ∧
    (∀ h, GlobalTheory (m + 1) h → η h ≠ 0 → Mir m (r h)) ∧ (∀ h, ∃ t : ℝ, 0 ≤ t ∧ η h = t) ∧
    (∃ C, IsCompact C ∧ C ⊆ U ∧ (∀ c ∈ C, GlobalTheory (m + 1) c) ∧ ∀ h, GlobalTheory (m + 1) h → η h ≠ 0 → ∃ c ∈ C, h = r h * c) ∧
    ∀ v, SmV ρ v → ∃ v', SmV ρ v' ∧
      ∀ Y : Submodule ℂ X, IsClosed (Y : Set X) → (∀ g, ∀ x ∈ Y, ρ g x ∈ Y) → v ∈ Y → v' ∈ Y ∧
        ∀ Λ : X →L[ℂ] ℂ, (∀ x ∈ Y, ∀ y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → ι → ℂ,
          Λ (ρ (blkU y) x) = χ (lastE (m + 1) y) * Λ x) → ∀ h, GlobalTheory (m + 1) h → Λ (ρ h v') = η h * Λ (ρ (r h) v)

def S9 : Prop := ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (a m : ℕ), m + 1 < a → ∀ χ : AddChar F ℂ, Continuous χ → (∃ x, χ x ≠ 1) →
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (Fin a) F) X) (U : Set (GL (Fin a) F)),
    U ∈ 𝓝 (1 : GL (Fin a) F) →
    ∃ (T : Finset (GL (Fin a) F)) (c η : GL (Fin a) F → ℂ) (r : GL (Fin a) F → GL (Fin a) F), η 1 ≠ 0 ∧ r 1 = 1 ∧
      (∀ h, GlobalTheory (m + 1) h → η h ≠ 0 → Mir m (r h)) ∧ (∀ h, ∃ t : ℝ, 0 ≤ t ∧ η h = t) ∧
      (∃ C, IsCompact C ∧ C ⊆ U ∧ (∀ c ∈ C, GlobalTheory (m + 1) c) ∧ ∀ h, GlobalTheory (m + 1) h → η h ≠ 0 → ∃ c ∈ C, h = r h * c) ∧
      ∀ v, (∀ u ∈ U, ρ u v = v) →
        ∀ Y : Submodule ℂ X, (∀ g, ∀ x ∈ Y, ρ g x ∈ Y) → v ∈ Y →
          ∀ Λ : X →ₗ[ℂ] ℂ, (∀ x ∈ Y, ∀ y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → F,
            Λ (ρ (blkU y) x) = χ (lastE (m + 1) y) * Λ x) →
            ∀ h, GlobalTheory (m + 1) h → Λ (ρ h (∑ t ∈ T, c t • ρ t v)) = η h * Λ (ρ (r h) v)

def MirabolicColumnBlock : Prop := ∀ (R : Type) [CommRing R] (a m : ℕ),
  (∀ γ : GL (Fin a) R, Mir m γ → ∃ (y : UnipotentBlockColumnIndex a m m → R) (h : GL (Fin a) R), GlobalTheory m h ∧ γ = blkU y * h) ∧
  (∀ γ : GL (Fin a) R, Mir 0 γ → γ = 1) ∧ Mir m (1 : GL (Fin a) R) ∧ GlobalTheory m (1 : GL (Fin a) R) ∧
  (∀ γ γ' : GL (Fin a) R, Mir m γ → Mir m γ' → Mir m (γ * γ')) ∧
  (∀ (k : ℕ) (y : UnipotentBlockColumnIndex a k k → R), k ≤ m → Mir m (blkU y)) ∧
  (∀ (k : ℕ) (γ : GL (Fin a) R), k ≤ m → Mir k γ → Mir m γ) ∧
  ∀ h : GL (Fin a) R, GlobalTheory m h → ∀ y : UnipotentBlockColumnIndex a m m → R, ∃ y' : UnipotentBlockColumnIndex a m m → R, h * blkU y = blkU y' * h ∧
    ∀ t, y' t = ∑ s, h.val t.1.1 s.1.1 * y s

end PositivityTheory.jumpWindows

end
