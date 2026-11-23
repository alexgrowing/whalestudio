import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial NumberField MeasureTheory

section Lattice

variable {r : ℕ}

def chiHat (nm : (Fin r → ℝ) → ℝ) : ℝ :=
  Real.log (volume {t | nm t ≤ 1}).toReal

def latticePointLogCount (nm : (Fin r → ℝ) → ℝ) : ℝ :=
  Real.log (Nat.card {k : Fin r → ℤ // nm (fun i => (k i : ℝ)) ≤ 1})

def IsSubexpDominated {r : ℕ → ℕ} (nm nm' : ∀ d, (Fin (r d) → ℝ) → ℝ) : Prop :=
  ∀ ε > 0, ∃ C : ℝ, ∀ d t, nm d t ≤ C * Real.exp (ε * d) * nm' d t

end Lattice

section Sections

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] {r : ℕ}

def combPoly (b : Fin r → MvPolynomial ι K) (w : InfinitePlace K) (t : Fin r → ℝ) :
    MvPolynomial ι ℂ :=
  ∑ i, C (t i : ℂ) * map w.embedding (b i)

def arSupNorm (m : InfinitePlace K → ConeMetric ℂ ι) (I : Ideal (MvPolynomial ι K)) (d : ℕ)
    (b : Fin r → MvPolynomial ι K) (t : Fin r → ℝ) : ℝ :=
  ⨆ w : InfinitePlace K,
    supNorm (m w) (RingHom.id ℂ) (I.map (map w.embedding)) d (combPoly b w t)

def archimedeanL2Norm (m : InfinitePlace K → ConeMetric ℂ ι) (μ : InfinitePlace K → Measure (ι → ℂ))
    (d : ℕ) (b : Fin r → MvPolynomial ι K) (t : Fin r → ℝ) : ℝ :=
  Real.sqrt (∑ w : InfinitePlace K,
    (w.mult : ℝ) * l2Norm (m w) (RingHom.id ℂ) (μ w) d (combPoly b w t) ^ 2)

def BernsteinMarkov {r : ℕ → ℕ} (m : InfinitePlace K → ConeMetric ℂ ι)
    (I : Ideal (MvPolynomial ι K)) (μ : InfinitePlace K → Measure (ι → ℂ))
    (b : ∀ d, Fin (r d) → MvPolynomial ι K) : Prop :=
  IsSubexpDominated (fun d => arSupNorm m I d (b d)) (fun d => archimedeanL2Norm m μ d (b d))

end Sections

section ChowForm

variable {o : Type*} [CommRing o] {e n : ℕ}

def IsChowForm (σ : o →+* ℂ) (I : Ideal (MvPolynomial (Fin n) o)) (e δ : ℕ)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) : Prop :=
  IsMultihomog f δ ∧ Squarefree f ∧
    ∀ u : Fin (e + 1) → Fin n → ℂ,
      eval (fun p => u p.1 p.2) f = 0 ↔ ∃ z ∈ conePts σ I, ∀ j, ∑ i, u j i * z i = 0

end ChowForm

end ReciprocityTheory.ChartRestriction.G.Geo
