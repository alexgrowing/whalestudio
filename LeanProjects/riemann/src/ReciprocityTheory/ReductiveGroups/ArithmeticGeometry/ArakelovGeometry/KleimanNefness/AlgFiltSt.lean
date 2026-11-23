import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def IsPrimeFilt (S : Type*) [CommRing S] {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] (𝓜 : (K → ℤ) → Submodule S M)
    {r : ℕ} (m : Fin r → M) (c : Fin r → K → ℤ) (𝔭 : Fin r → Ideal (MRingOver S ι)) : Prop :=
  (∀ j, m j ∈ 𝓜 (c j)) ∧
    (∀ j, (𝔭 j).IsPrime ∧ IsMultiHomogIdeal (𝔭 j) ∧ Module.annihilator (MRingOver S ι) M ≤ 𝔭 j) ∧
    (∀ j (p : MRingOver S ι), p • m j ∈ Submodule.span (MRingOver S ι) (m '' {l | l < j}) ↔ p ∈ 𝔭 j) ∧
    Submodule.span (MRingOver S ι) (Set.range m) = ⊤

def PrimeFiltStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → IsMGraded S ι 𝓜 →
    ∃ (r : ℕ) (m : Fin r → M) (c : Fin r → K → ℤ) (𝔭 : Fin r → Ideal (MRingOver S ι)),
      IsPrimeFilt S ι 𝓜 m c 𝔭

def PrimeFiltMultStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (r : ℕ) (m : Fin r → M) (c : Fin r → K → ℤ)
    (𝔭 : Fin r → Ideal (MRingOver S ι)) (𝔮 : Ideal (MRingOver S ι)) [𝔮.IsPrime],
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → IsMGraded S ι 𝓜 → IsPrimeFilt S ι 𝓜 m c 𝔭 →
    𝔮 ∈ (Module.annihilator (MRingOver S ι) M).minimalPrimes →
    ((Finset.univ.filter fun j => 𝔭 j = 𝔮).card : ℕ∞) =
      Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl M)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
