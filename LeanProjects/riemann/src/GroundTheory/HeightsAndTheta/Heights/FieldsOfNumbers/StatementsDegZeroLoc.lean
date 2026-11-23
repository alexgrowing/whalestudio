import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivPushForwardLocal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

section Loc

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

def degZeroLoc (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F))) :
    Subalgebra F (FractionRing (MRing ι F ⧸ P)) :=
  Algebra.adjoin F {x | ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧ IsMultiHomog g b ∧
    g ∉ P ∧ (∀ W ∈ 𝒲, g ∉ W) ∧
    x = algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)}

theorem div_mem_degZeroLoc (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F)))
    {b : K → ℕ} {f g : MRing ι F} (hf : IsMultiHomog f b) (hg : IsMultiHomog g b) (hgP : g ∉ P)
    (hg𝒲 : ∀ W ∈ 𝒲, g ∉ W) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈ degZeroLoc P 𝒲 :=
  Algebra.subset_adjoin ⟨b, f, g, hf, hg, hgP, hg𝒲, rfl⟩

end Loc

section Fibre

variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}

def fibrePrimes (P' : Ideal (MRing ι' F)) (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    Set (Ideal (MRing ι' F)) :=
  {W' | IsMultiProjPrime W' ∧ P' ≤ W' ∧ contractPrime j W' = W}

theorem map_degZeroLoc_le (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    (degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P') ≤
      degZeroLoc P' (fibrePrimes j P' W) := by
  unfold degZeroLoc
  rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rintro _ ⟨x, ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩, rfl⟩
  apply Algebra.subset_adjoin
  refine ⟨Function.extend j b 0, rename (blockIncl j ι') f, rename (blockIncl j ι') g,
    isMultiHomog_rename j ι' hf, isMultiHomog_rename j ι' hg, hgP, ?_, ?_⟩
  · rintro W' ⟨-, -, hc⟩ hgW'
    apply hgW W (Set.mem_singleton W)
    rw [← hc]
    exact hgW'
  · rw [map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]

def degZeroLocContract (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    degZeroLoc (contractPrime j P') {W} →ₐ[F] degZeroLoc P' (fibrePrimes j P' W) :=
  ((contractFracMap j P').comp (degZeroLoc (contractPrime j P') {W}).val).codRestrict _
    (fun x => map_degZeroLoc_le j P' W (Subalgebra.mem_map.mpr ⟨x, x.2, rfl⟩))

instance degZeroLoc.algebraContract (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    Algebra (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) :=
  (degZeroLocContract j P' W).toRingHom.toAlgebra

theorem degZeroLoc.algebraMap_contract_coe (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) (x : degZeroLoc (contractPrime j P') {W}) :
    ((algebraMap (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) x :
      degZeroLoc P' (fibrePrimes j P' W)) : FractionRing (MRing ι' F ⧸ P')) =
      contractFracMap j P' x :=
  rfl

end Fibre

section Example

end Example

end

end GroundTheory.Heights₂.Heights.FieldNumbers
