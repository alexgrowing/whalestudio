import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem degZeroLoc_anti {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) [P.IsPrime] {𝒲₁ 𝒲₂ : Set (Ideal (MRing ι F))} (h𝒲 : 𝒲₁ ⊆ 𝒲₂) :
    degZeroLoc P 𝒲₂ ≤ degZeroLoc P 𝒲₁ := by
  unfold degZeroLoc
  apply Algebra.adjoin_mono
  rintro _ ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩
  exact ⟨b, f, g, hf, hg, hgP, fun W hW => hgW W (h𝒲 hW), rfl⟩

section Fibre

variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}

theorem exists_fibreLift (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) (α : degZeroLoc (contractPrime j P') {W}) :
    ∃ β : (W' : Ideal (MRing ι' F)) → degZeroLoc P' {W'},
      ∀ W' ∈ fibrePrimes j P' W,
        (β W' : FractionRing (MRing ι' F ⧸ P')) = contractFracMap j P' (α : _) := by
  classical
  refine ⟨fun W' => if hm : contractFracMap j P' (α : _) ∈ degZeroLoc P' {W'} then ⟨_, hm⟩ else 0,
    fun W' hW' => ?_⟩
  have hm : contractFracMap j P' (α : _) ∈ degZeroLoc P' {W'} :=
    degZeroLoc_anti P' (Set.singleton_subset_iff.mpr hW')
      (map_degZeroLoc_le j P' W (Subalgebra.mem_map.mpr ⟨_, α.2, rfl⟩))
  simp only [dif_pos hm]

theorem exists_relDegFn :
    ∃ d : Ideal (MRing ι' F) → ℕ, ∀ W' (hW' : IsMultiProjPrime W'),
      haveI := hW'.isPrime
      d W' = relDeg j W' := by
  classical
  exact ⟨fun W' => if hp : W'.IsPrime then haveI := hp; relDeg j W' else 0,
    fun W' hW' => dif_pos hW'.isPrime⟩

end Fibre

open Classical in
set_option synthInstance.maxHeartbeats 400000 in

def SemilocalLengthSum.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a h : MRing (fun k => ι' (j k)) F), IsMultiHomog a c → IsMultiHomog h c →
    a ∉ contractPrime j P' →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W → h ∉ W →
    ∀ d : Ideal (MRing ι' F) → ℕ,
      (∀ W' (hW' : IsMultiProjPrime W'), contractPrime j W' = W →
        haveI := hW'.isPrime
        d W' = relDeg j W') →
      haveI := hP'.isPrime
      ∀ α : degZeroLoc (contractPrime j P') {W},
        (α : FractionRing (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P')) =
            algebraMap (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') a) /
              algebraMap (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') h) →
      ∀ β : (W' : Ideal (MRing ι' F)) → degZeroLoc P' {W'},
        (∀ W' ∈ fibrePrimes j P' W,
          (β W' : FractionRing (MRing ι' F ⧸ P')) = contractFracMap j P' (α : _)) →
        ∃ hfin : (fibrePrimes j P' W).Finite,
          Module.length (degZeroLoc (contractPrime j P') {W})
              (degZeroLoc P' (fibrePrimes j P' W) ⧸
                LinearMap.range (LinearMap.lsmul (degZeroLoc (contractPrime j P') {W})
                  (degZeroLoc P' (fibrePrimes j P' W)) α)) =
            ∑ W' ∈ hfin.toFinset with rename (blockIncl j ι') a ∈ W',
              Ring.ord (degZeroLoc P' {W'}) (β W') * (d W' : ℕ∞)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
