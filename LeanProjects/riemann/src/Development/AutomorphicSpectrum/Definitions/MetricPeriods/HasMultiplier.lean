import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenHost

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ptsOver (𝕜 : Type) [Field 𝕜] (P : Ideal (MRing ι)) : Set ((Σ k, ι k) → 𝕜) :=
  {z | (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ P, aeval z f = 0}

def algPts (p : ℕ) [Fact p.Prime] (P : Ideal (MRing ι)) : Set ((Σ k, ι k) → PadicAlgCl p) :=
  {z | z ∈ ptsOver (PadicAlgCl p) P ∧ ∀ q, IsAlgebraic ℚ (z q)}

def HasVal (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜) (w : 𝕜) : Prop :=
  ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + a k) ∧
    aeval y g = s * aeval y h ∧ aeval z h ≠ 0 ∧ aeval z g = w * aeval z h

def ValLe (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) {𝕜 : Type} [NormedField 𝕜] (z : (Σ k, ι k) → 𝕜) (r : ℝ) :
    Prop :=
  ∀ w, HasVal y a s z w → ‖w‖ ≤ r

def supMet {𝕜 : Type} [NormedField 𝕜] (a : K → ℤ) (z : (Σ k, ι k) → 𝕜) : ℝ :=
  ∏ k, ‖fun i : ι k => z ⟨k, i⟩‖ ^ a k

def IsFormOff (P : Ideal (MRing ι)) (u : MRing ι) : Prop :=
  (∃ d, IsMultiHomog u d) ∧ u ∉ P

def powH (A : HermLine ι) (q : ℕ) : HermLine ι where
  a := fun k => (q : ℤ) * A.a k
  h z := A.h z ^ q
  pos z hz := pow_pos (A.pos z hz) q
  smul c z hc := by
    rw [A.smul c z hc, mul_pow, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [mul_comm, zpow_mul, zpow_natCast]

def shiftH (A : HermLine ι) (t : ℝ) : HermLine ι where
  a := A.a
  h z := Real.exp t * A.h z
  pos z hz := mul_pos (Real.exp_pos t) (A.pos z hz)
  smul c z hc := by rw [A.smul c z hc]; ring

def normHt (II : IntersectionSystem) (P : Ideal (MRing ι)) (A : HermLine ι) (D : ℕ) : ℝ :=
  II K ι P (D + 1) (fun _ => A) / (((D : ℝ) + 1) * geomDeg P A D)

def embMean {F : Type} [Field F] [NumberField F] (t : (F →+* ℂ) → ℝ) : ℝ :=
  (∑ sg, t sg) / Fintype.card (F →+* ℂ)

structure IsModelOver (y : (Σ k, ι k) → Ω) (F : Type) [Field F] [Algebra F Ω] (D : ℕ) : Prop where
  one_le : 1 ≤ D
  arith : IsArithVar (mCoordIdeal y) (D + 1)
  bir : Birational y
  uniq : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z

structure IsNefH (P : Ideal (MRing ι)) (M : HermLine ι) : Prop where
  semipos : ∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P M
  conj : IsConjInvariantH M
  nef : NefOnFibres P M.a

structure IsGenH (P : Ideal (MRing ι)) (L : HermLine ι) (Λ : ℝ) : Prop where
  pos : 0 < Λ
  semipos : ∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P L
  conj : IsConjInvariantH L
  mono : ∃ a : K → ℕ, (L.a = fun k => (a k : ℤ)) ∧ ∀ z ∈ mcPts P, ∀ μ : (Σ k, ι k) →₀ ℕ,
    (∀ k, ∑ i, μ ⟨k, i⟩ = a k) → ‖∏ p, z p ^ μ p‖ ≤ Λ * L.h z

structure MultBound (y : (Σ k, ι k) → Ω) {F : Type} [Field F] [Algebra F Ω] (M L : HermLine ι) (θ : Ω)
    (u : MRing ι) (c : ℕ → ℝ) (t : (F →+* ℂ) → ℝ) : Prop where
  fin : ∀ (p : ℕ) [Fact p.Prime], ∀ z ∈ algPts p (mCoordIdeal y), aeval z u ≠ 0 →
    ∀ w, HasVal y (L.a - M.a) θ z w → ‖w‖ * supMet M.a z ≤ Real.exp (c p) * supMet L.a z
  arch : ∀ (sg : F →+* ℂ), ∀ z ∈ mcPts (mCoordIdeal y), LiesOver y sg z → aeval z u ≠ 0 →
    ∀ w, HasVal y (L.a - M.a) θ z w → ‖w‖ * M.h z ≤ Real.exp (t sg) * L.h z

def HasMultiplier (y : (Σ k, ι k) → Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω] (M L : HermLine ι)
    (B : ℝ) : Prop :=
  ∃ (θ : Ω) (u : MRing ι) (S : Finset ℕ) (c : ℕ → ℝ) (t : (F →+* ℂ) → ℝ),
    θ ≠ 0 ∧ IsFormOff (mCoordIdeal y) u ∧ (∀ p ∈ S, p.Prime) ∧ (∀ p, 0 ≤ c p) ∧ (∀ p, p ∉ S → c p = 0) ∧
    (∀ sg, t (NumberField.ComplexEmbedding.conjugate sg) = t sg) ∧ MultBound y M L θ u c t ∧
    ∑ p ∈ S, c p + embMean t ≤ B

end GlobalTheory.CompanionTheory.Ar.Small
