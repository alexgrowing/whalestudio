import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase

theorem det_genU (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) : (genU Ω r s).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [genU]
  · intro l k hlk
    have hlk' : l < k := hlk
    have h1 : ¬ k < l := not_lt.2 hlk'.le
    have h2 : l ≠ k := hlk'.ne
    simp [genU, h1, h2]

theorem det_map_mul_submatrix {Ω L : Type} [Field Ω] [Field L] (f : Ω →+* L) {n m r : ℕ} (hm : m = r) (h : m ≤ r)
    (A : Matrix (Fin n) (Fin r) Ω) (U : Matrix (Fin r) (Fin r) L) (hU : U.det = 1) (J : Fin m → Fin n) :
    ((A.map f * U).submatrix J (Fin.castLE h)).det = f ((A.submatrix J (Fin.castLE h)).det) := by
  subst hm
  have hc : (Fin.castLE h : Fin m → Fin m) = id := by
    funext i
    rfl
  rw [hc, RingHom.map_det]
  have : (A.map f * U).submatrix J id = (f.mapMatrix (A.submatrix J id)) * U := by
    ext a b
    simp [Matrix.mul_apply]
  rw [this, Matrix.det_mul, hU, mul_one]

variable {Ψ : Type} {p q : ℕ}

theorem full_of_noBlock (K₀ : Type) (t : StepIx Ψ p q)
    (h : ∀ r, blkF Ψ p q K₀ r ≠ some (.inr t)) : (t.2 : ℕ) + 1 = rk Ψ p q t.1 := by
  obtain ⟨s, i⟩ := t
  rcases s with τ | τ
  · have hi : (i : ℕ) < p := i.2
    by_contra hne
    have hne' : (i : ℕ) + 1 ≠ p := hne
    refine h (τ, ⟨i, by omega⟩) ?_
    have hp : IsProperStep (p + q) p (⟨i, by omega⟩ : Fin (p + q)) := ⟨hne', by
      show (i : ℕ) + 1 ≠ p + q
      omega⟩
    simp only [blkF, if_pos hp, stepOf]
    simp [hi]
    rfl
  · have hi : (i : ℕ) < q := i.2
    by_contra hne
    have hne' : (i : ℕ) + 1 ≠ q := hne
    refine h (τ, ⟨p + i, by omega⟩) ?_
    have hp : IsProperStep (p + q) p (⟨p + i, by omega⟩ : Fin (p + q)) := ⟨by
      show p + (i : ℕ) + 1 ≠ p
      omega, by
      show p + (i : ℕ) + 1 ≠ p + q
      omega⟩
    simp only [blkF, if_pos hp, stepOf]
    simp
    rfl

theorem basePart_yv : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type)
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), ∀ r,
    basePart (blkF Ψ p q K₀) (yv A x₀) r = algebraMap Ω (GenField Ω (rk Ψ p q)) (xb A x₀ r) := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ r
  obtain ⟨⟨k, hk⟩, i⟩ := r
  rcases k with k | t
  · rfl
  · exact det_map_mul_submatrix (algebraMap Ω (GenField Ω (rk Ψ p q))) (full_of_noBlock K₀ t hk) t.2.2 (A t.1)
      (genU Ω (rk Ψ p q) t.1) (det_genU Ω _ _) i

end GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase
