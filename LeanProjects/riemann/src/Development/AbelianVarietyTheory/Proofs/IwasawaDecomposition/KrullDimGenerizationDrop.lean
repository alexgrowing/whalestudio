import Mathlib
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem ringKrullDim_stalk_nonpos_of_specializes_of_ne (X : Scheme.{0}) (q η : X) (hsp : η ⤳ q)
    (hne : η ≠ q) (hq : ringKrullDim (X.presheaf.stalk q) ≤ 1) :
    ringKrullDim (X.presheaf.stalk η) ≤ 0 := by
  obtain ⟨U, hU, hqU, -⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show q ∈ (⊤ : X.Opens) from trivial)
  have hU : IsAffineOpen U := hU
  have hηU : η ∈ U := hsp.mem_open U.isOpen hqU
  let qU : U := ⟨q, hqU⟩
  let ηU : U := ⟨η, hηU⟩
  let algQ : Algebra Γ(X, U) (X.presheaf.stalk q) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf qU
  let algη : Algebra Γ(X, U) (X.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ηU
  have hlq : IsLocalization.AtPrime (X.presheaf.stalk q) (hU.primeIdealOf qU).asIdeal :=
    hU.isLocalization_stalk qU
  have hlη : IsLocalization.AtPrime (X.presheaf.stalk η) (hU.primeIdealOf ηU).asIdeal :=
    hU.isLocalization_stalk ηU
  set Pq := hU.primeIdealOf qU
  set Pη := hU.primeIdealOf ηU
  have hfq : hU.fromSpec Pq = q := hU.fromSpec_primeIdealOf qU
  have hfη : hU.fromSpec Pη = η := hU.fromSpec_primeIdealOf ηU
  have emb := hU.fromSpec.isOpenEmbedding
  have hle : Pη ≤ Pq := by
    rw [PrimeSpectrum.le_iff_specializes]
    exact emb.isInducing.specializes_iff.mp (by rw [hfη, hfq]; exact hsp)
  have hne' : Pη ≠ Pq := fun h => hne (by rw [← hfη, ← hfq, h])
  have hlt : Pη.asIdeal < Pq.asIdeal := lt_of_le_of_ne hle (fun h => hne' (PrimeSpectrum.ext h))
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Pq.asIdeal (X.presheaf.stalk q)] at hq
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Pη.asIdeal (X.presheaf.stalk η)]
  have hq' : Pq.asIdeal.height ≤ 1 := by exact_mod_cast hq
  have : Pq.asIdeal.FiniteHeight :=
    Pq.asIdeal.finiteHeight_iff.mpr (Or.inr (ne_top_of_le_ne_top ENat.one_ne_top hq'))
  have h1 : Pη.asIdeal.height < 1 :=
    (Ideal.height_strict_mono_of_isPrime_of_isPrime hlt).trans_le hq'
  rw [ENat.lt_one_iff_eq_zero] at h1
  rw [h1]
  rfl

end GlobalTheory
