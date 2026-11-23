import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem spMap_base_mem_basicOpen {R T : Type} [CommRing R] [CommRing T] (χ : R →+* T) (a : R)
    (ha : IsUnit (χ a)) (t : Sp T) : (spMap χ).base t ∈ (PrimeSpectrum.basicOpen a : (Sp R).Opens) := by
  change a ∉ (PrimeSpectrum.comap χ t).asIdeal
  intro h
  exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ha)

theorem tube_of_universallyClosed : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0})
    (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [UniversallyClosed f] (W : X.Opens),
    IsPullback π f' f (spMap φ) → π ⁻¹ᵁ W = ⊤ → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T),
    IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → ρ ⁻¹ᵁ W = ⊤ := by
  intro R k _ _ φ X X' f f' π _ W H hW
  have hc : IsClosed (f.base '' (W : Set X)ᶜ) := f.isClosedMap _ W.isOpen.isClosed_compl
  let t : Sp k := ⟨⊥, Ideal.isPrime_bot⟩
  have hx : (spMap φ).base t ∈ (f.base '' (W : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, e⟩
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback H x t e
    exact hx (hW.ge (Set.mem_univ z))
  obtain ⟨_, ⟨a, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hc.isOpen_compl
  refine ⟨a, ?_, ?_⟩
  · intro h0
    apply ha
    change φ a ∈ (⊥ : Ideal k)
    exact h0
  · intro T _ χ hχ Z g ρ H'
    refine top_le_iff.1 fun z _ => ?_
    by_contra hz
    have hm := spMap_base_mem_basicOpen χ a hχ (g.base z)
    have e : f.base (ρ.base z) = (spMap χ).base (g.base z) := by
      have := congrArg (fun h : Z ⟶ Sp R => h.base z) H'.w
      simpa using this
    exact hle (e ▸ hm : f.base (ρ.base z) ∈ _) ⟨ρ.base z, hz, rfl⟩

end GlobalTheory
