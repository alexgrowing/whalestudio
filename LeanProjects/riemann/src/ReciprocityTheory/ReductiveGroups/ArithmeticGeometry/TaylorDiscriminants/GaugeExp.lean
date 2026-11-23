import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

def expSecond (k : Type) [CommRing k] [Algebra ℚ k] {ι : Type} [Fintype ι] (c : ι → ι → k) (t : k) (N : ℕ)
    (Q : MvPolynomial ι k) : MvPolynomial ι k :=
  ∑ i ∈ Finset.range (N + 1), (t ^ i * algebraMap ℚ k (1 / (Nat.factorial i : ℚ))) • (secondOrder k c)^[i] Q

def GaugeExpSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (B : FB R d O) (h h' : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k h' →
    ∀ (w0 : O) (m : ℕ) {ι : Type} [Fintype ι] (u : ι → Fin d → k) (Q : MvPolynomial ι k) (f : PS k 1 d),
      B.nabVal k h' w0 m f u Q =
        B.nabVal k h w0 m f u (expSecond k (fun l l' =>
          dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) +
          dotProduct (u l') ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l))))
          ((m : k) * algebraMap ℚ k (1 / 2)) Q.totalDegree Q)

end ReciprocityTheory.ChartRestriction.G.TB
