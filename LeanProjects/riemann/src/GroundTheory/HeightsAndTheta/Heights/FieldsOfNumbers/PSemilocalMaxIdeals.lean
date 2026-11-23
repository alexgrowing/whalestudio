import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalMaxIdeals
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreRelDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreNonempty
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocUnits
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocSeparate
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocLocalize
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalResidueLength
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u

set_option synthInstance.maxHeartbeats 400000 in

theorem SemilocalMaxIdeals.proof (h1 : FibreFinite.Statement.{u}) (h2 : FibreRelDim.Statement.{u})
    (h3 : FibreNonempty.Statement.{u}) (h4 : DegZeroLocUnits.Statement.{u})
    (h5 : DegZeroLocSeparate.Statement.{u}) (h6 : DegZeroLocLocalize.Statement.{u})
    (h7 : SemilocalResidueLength.Statement.{u}) : SemilocalMaxIdeals.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W hW hWn hPW
  have := hP'.isPrime
  have hfin := h1 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  have h𝒲 : ∀ W' ∈ fibrePrimes j P' W, IsMultiProjPrime W' ∧ P' ≤ W' :=
    fun W' hW' => ⟨hW'.1, hW'.2.1⟩

  have hanti : ∀ W₁ ∈ fibrePrimes j P' W, ∀ W₂ ∈ fibrePrimes j P' W, W₁ ≤ W₂ → W₁ = W₂ := by
    intro W₁ h₁ W₂ h₂ hle
    by_contra hne
    have := h₁.1.isPrime
    have := h₂.1.isPrime
    obtain ⟨f, hf₂, hf₁⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
    have hd := ringKrullDim_add_one_le hle hf₁ hf₂
    obtain ⟨D₁, -, hD₁⟩ := exists_ringKrullDim_eq
      (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal h₁.1.multiHomog T hq) h₁.1.relevant
    obtain ⟨D₂, -, hD₂⟩ := exists_ringKrullDim_eq
      (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal h₂.1.multiHomog T hq) h₂.1.relevant
    have e₁ := h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW W₁ h₁
    have e₂ := h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW W₂ h₂
    rw [relDim_eq_int hD₁, natCast_withBot_withTop] at e₁
    rw [relDim_eq_int hD₂, natCast_withBot_withTop] at e₂
    rw [hD₁, hD₂] at hd
    have e₁' : (D₁ : ℤ) - Fintype.card K' = n := by exact_mod_cast e₁
    have e₂' : (D₂ : ℤ) - Fintype.card K' = n := by exact_mod_cast e₂
    have hd' : D₂ + 1 ≤ D₁ := by exact_mod_cast hd
    omega

  choose 𝔪 h𝔪 hlen using h7 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  let : Fintype (fibrePrimes j P' W) := hfin.fintype
  have hprime : ∀ W' : fibrePrimes j P' W, (𝔪 W'.1 W'.2).IsPrime := by
    intro W'
    refine ⟨fun htop => (h𝔪 W'.1 W'.2 1).mp (htop ▸ Submodule.mem_top)
      ⟨1, Subalgebra.one_mem _, by simp⟩, fun {x y} hxy => ?_⟩
    by_contra hc
    rw [not_or, h𝔪, h𝔪, not_not, not_not] at hc
    obtain ⟨⟨a, ha, hxa⟩, ⟨b, hb, hyb⟩⟩ := hc
    exact (h𝔪 W'.1 W'.2 _).mp hxy ⟨a * b, Subalgebra.mul_mem _ ha hb, by
      rw [Subalgebra.coe_mul, mul_mul_mul_comm, hxa, hyb, one_mul]⟩

  have hsep : ∀ W₁ W₂ : fibrePrimes j P' W, W₁ ≠ W₂ → ¬ 𝔪 W₁.1 W₁.2 ≤ 𝔪 W₂.1 W₂.2 := by
    intro W₁ W₂ hne hle
    obtain ⟨x, hx, hx₁, hx₂⟩ := h5 F K' ι' P' hP' _ hfin h𝒲 W₁.1 W₁.2 W₂.1 W₂.2
      (fun h => hne (Subtype.ext (hanti _ W₁.2 _ W₂.2 h)))
    exact (h𝔪 W₂.1 W₂.2 ⟨x, hx⟩).mp (hle ((h𝔪 W₁.1 W₁.2 ⟨x, hx⟩).mpr hx₁)) hx₂

  have hne := h3 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  have hcov : ∀ M : Ideal (degZeroLoc P' (fibrePrimes j P' W)), M.IsMaximal →
      ∃ W' : fibrePrimes j P' W, M = 𝔪 W'.1 W'.2 := by
    intro M hM
    let 𝔫 : fibrePrimes j P' W → Ideal (degZeroLoc P' (fibrePrimes j P' W)) := fun W' => 𝔪 W'.1 W'.2
    have hsub : (M : Set (degZeroLoc P' (fibrePrimes j P' W))) ⊆
        ⋃ W' ∈ ((Finset.univ : Finset (fibrePrimes j P' W)) : Set (fibrePrimes j P' W)),
          ((𝔫 W' : Ideal (degZeroLoc P' (fibrePrimes j P' W))) : Set _) := by
      intro x hx
      have hnu : ¬ IsUnit x := fun hu => hM.ne_top (M.eq_top_of_isUnit_mem hx hu)
      have : ¬ ∀ W' ∈ fibrePrimes j P' W, ∃ y ∈ degZeroLoc P' {W'},
          (x : FractionRing (MRing ι' F ⧸ P')) * y = 1 := by
        rw [← h4 F K' ι' P' hP' _ hne h𝒲 x x.2]
        rintro ⟨y, hy, hxy⟩
        exact hnu (IsUnit.of_mul_eq_one ⟨y, hy⟩ (Subtype.ext hxy))
      push Not at this
      obtain ⟨W', hW', hx'⟩ := this
      refine Set.mem_iUnion₂.mpr ⟨⟨W', hW'⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      exact (h𝔪 W' hW' x).mpr (fun ⟨y, hy, hxy⟩ => hx' y hy hxy)
    obtain ⟨W', -, hle⟩ := (Ideal.subset_union_prime (f := 𝔫) ⟨hne.some, hne.some_mem⟩
      ⟨hne.some, hne.some_mem⟩ (fun W' _ _ _ => hprime W')).mp hsub
    exact ⟨W', hM.eq_of_le (hprime W').ne_top hle⟩
  have hmax : ∀ W' : fibrePrimes j P' W, (𝔪 W'.1 W'.2).IsMaximal := by
    intro W'
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (hprime W').ne_top
    obtain ⟨W'', rfl⟩ := hcov M hM
    by_cases h : W' = W''
    · subst h
      exact hM
    · exact absurd hle (hsep W' W'' h)
  refine ⟨fun W' => 𝔪 W'.1 W'.2, hmax, fun W₁ W₂ he => ?_, hcov, fun W' => ⟨?_, hlen W'.1 W'.2⟩⟩
  · by_contra h
    exact hsep W₁ W₂ h (le_of_eq he)

  let := degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)
  refine (isLocalization_iff _ _).mpr ⟨fun s => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · have hs := s.2
    rw [Ideal.mem_primeCompl_iff, h𝔪, not_not] at hs
    obtain ⟨t, ht, hst⟩ := hs
    exact IsUnit.of_mul_eq_one ⟨t, ht⟩ (Subtype.ext hst)
  · obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hzs⟩ := h6 F K' ι' P' hP' _ hfin h𝒲 W'.1 W'.2 z z.2
    refine ⟨(⟨b, hb⟩, ⟨⟨s, hs⟩, ?_⟩), Subtype.ext hzs⟩
    rw [Ideal.mem_primeCompl_iff, h𝔪, not_not]
    exact ⟨t, ht, hst⟩
  · refine ⟨1, ?_⟩
    have h' := congrArg Subtype.val hxy
    have hxy' : x = y := Subtype.ext h'
    rw [hxy']

end

end GroundTheory.Heights₂.Heights.FieldNumbers
