import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def pC (P : Ideal (MRing ι)) : Ideal (MRingOver ℂ ι) :=
  Ideal.span (map (Int.castRingHom ℂ) '' (P : Set (MRing ι)))

theorem mcPts_eq_pC (P : Ideal (MRing ι)) :
    mcPts P = {z | (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ pC P, eval z f = 0} := by
  ext z
  simp only [mcPts, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun f hf => ?_⟩
    have hle : pC P ≤ RingHom.ker (MvPolynomial.eval z) :=
      Ideal.span_le.2 (by rintro _ ⟨g, hg, rfl⟩; exact h2 g hg)
    exact RingHom.mem_ker.1 (hle hf)
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun f hf => h2 _ (Ideal.subset_span ⟨f, hf, rfl⟩)⟩

def PCRadicalStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → (pC P).IsRadical

def PCEquidimStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∀ Q ∈ (pC P).minimalPrimes,
      ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)

def PCContractStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∀ f : MRing ι, map (Int.castRingHom ℂ) f ∈ pC P → f ∈ P

def PCMinContractStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∀ Q ∈ (pC P).minimalPrimes, Q.comap (map (Int.castRingHom ℂ)) = P

def jacMinors {s : ℕ} (G : Fin s → MRing ι) (c : ℕ) : Set (MRing ι) :=
  {d | ∃ (a : Fin c → Fin s) (b : Fin c → Σ k, ι k),
    d = Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i)))}

def JacNotInPStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∃ (s : ℕ) (G : Fin s → MRing ι), (∀ i, ∃ a, IsMultiHomog (G i) a) ∧
      Ideal.span (Set.range G) = P ∧
      ¬ Ideal.span (jacMinors G (Fintype.card (Σ k, ι k) - (e + Fintype.card K))) ≤ P

end ReciprocityTheory.ChartRestriction.G.Geo
