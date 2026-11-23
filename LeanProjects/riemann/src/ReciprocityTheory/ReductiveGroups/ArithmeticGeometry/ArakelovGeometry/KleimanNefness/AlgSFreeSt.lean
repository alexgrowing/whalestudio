import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def TheoremSFreeStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (d : K → ℤ),
    (∀ (c : K → ℤ) (n : ℕ),
      Module.Finite S (cechHc ι (fun c => quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n)) ∧
    (∀ (c : K → ℤ) (n : ℕ), 1 ≤ n → (∀ k, 0 ≤ c k + d k) →
      Subsingleton (cechHc ι (fun c => quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n)) ∧
    (∀ c : K → ℤ, (∀ k, 0 ≤ c k + d k) →
      ∀ z ∈ cechZc ι (fun c => quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c 0,
        ∃ m ∈ quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d), ∀ I, z I = LocalizedModule.mk m 1)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
