import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

def FourierInvSt : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (K : Type) [Field K] [Fintype (AddChar A K)],
    ((Fintype.card A : K) ≠ 0) → Fintype.card (AddChar A K) = Fintype.card A →
    ∀ φ : A → K, ∀ a,
      φ a = ∑ χ : AddChar A K, ((Fintype.card A : K)⁻¹ * ∑ b, φ b * χ (-b)) * χ a

def FourierCoeffIntSt : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (K : Type) [Field K] (O : Subring K) (φ : A → K),
    (∀ a, φ a ∈ O) → ∀ χ : AddChar A K, (∀ a, χ a ∈ O) →
      (Fintype.card A : K) * ((Fintype.card A : K)⁻¹ * ∑ b, φ b * χ (-b)) ∈ O ∨ (Fintype.card A : K) = 0

def mulN {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) : ℕ → Pt R 1 d
  | 0 => 0
  | n + 1 => G.add (mulN G n) (pt R d 0)

def NChainSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (n : ℕ) {ι : Type} [Fintype ι] (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (k : ℕ), P.IsHomogeneous k → ∀ f : PS R 1 d,
      constantCoeff (DpolyOf G.F u P (ev ![mulN G n] f)) = (n : R) ^ k * constantCoeff (DpolyOf G.F u P f)

end ReciprocityTheory.ChartRestriction.G.TB
