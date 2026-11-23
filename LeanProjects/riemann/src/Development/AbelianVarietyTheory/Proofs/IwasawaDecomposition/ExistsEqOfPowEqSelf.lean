import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsGal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDict

open Polynomial in

theorem exists_eq_of_pow_eq_self {Ω L : Type} [Field Ω] [IsAlgClosed Ω] [Field L] (j : Ω →+* L) {N : ℕ}
    (hN : 2 ≤ N) {ζ : L} (hζ : ζ ^ N = ζ) : ∃ z, j z = ζ := by
  have hmon : (X ^ N - X : Polynomial Ω).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by omega : 1 < N))
  have hb : ζ ∈ ((X ^ N - X : Polynomial Ω).map j).roots := by
    rw [mem_roots (hmon.map j).ne_zero]
    simp [hζ]
  rw [Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨y, -, hy⟩ := hb
  exact ⟨y, hy⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem isFrob_iff_of_lifts (h : IsPlaceOver A w) {ι : Ω →ₐ[E] Kbar w} {g : GalLoc w} {σ : G E Ω}
    (hσ : σ ∈ Dec (F := E) A) (H : Lifts ι g σ) :
    IsFrob (F := E) A (normV w) σ ↔
      ∀ (ζ : Kbar w) (m : ℕ), 0 < m → ζ ^ normV w ^ m = ζ → g ζ = ζ ^ normV w := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  rw [GlobalTheory.FrobTeich.isFrob_iff_teichmuller E Ω A w h σ]
  constructor
  · rintro ⟨-, hT⟩ ζ m hm hζ
    obtain ⟨z, rfl⟩ := exists_eq_of_pow_eq_self (ι : Ω →+* Kbar w)
      (Nat.one_lt_pow hm.ne' (one_lt_normV w)) hζ
    have hz : z ^ normV w ^ m = z := (ι : Ω →+* Kbar w).injective (by rw [map_pow]; exact hζ)
    change g (ι z) = ι z ^ normV w
    rw [H z, hT z m hm hz, map_pow]
  · intro hT
    refine ⟨hσ, fun z m hm hz => (ι : Ω →+* Kbar w).injective ?_⟩
    change ι (σ z) = ι (z ^ normV w)
    rw [← H z, map_pow]
    exact hT _ m hm (by rw [← map_pow, hz])

end GlobalTheory.WeilDict
