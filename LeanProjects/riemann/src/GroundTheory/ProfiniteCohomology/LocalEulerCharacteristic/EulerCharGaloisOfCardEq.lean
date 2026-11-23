import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainSimple
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCoind
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Devissage
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

section Main

attribute [-instance] ULift.module

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem eulerChar_galois_of_card_eq (n : ℕ) : ∀ (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M]
    [Finite M], Nat.card M = n → (Nat.card M : K) ≠ 0 →
      eulerChar M = (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ)⁻¹ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ hn hM
  have hPdvd : ∀ m n : ℕ, m ∣ n → (n : K) ≠ 0 → (m : K) ≠ 0 := by
    rintro m n ⟨c, rfl⟩ hn hm
    apply hn
    rw [Nat.cast_mul, hm, zero_mul]
  rcases subsingleton_or_nontrivial M with hsub | hnt
  ·
    have h1 : Nat.card M = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨0⟩⟩
    rw [eulerChar_eq_one_of_subsingleton, h1, Nat.cast_one,
      card_quotient_span_eq_one_of_isUnit isUnit_one, Nat.cast_one, inv_one]
  by_cases hs : ∀ N : Submodule (ULift.{0} ℤ) M, (∀ g, N ≤ N.comap (M.ρ g)) → N = ⊥ ∨ N = ⊤
  · exact eulerChar_of_forall_eq_bot_or_eq_top M hM hs

  push Not at hs
  obtain ⟨N, hN, hbot, htop⟩ := hs
  let i := Rep.subtype M N hN
  have hi : Function.Injective i.hom := Submodule.injective_subtype N
  have hS := cokerShortComplex_shortExact i hi
  have : IsDiscreteRep (cokerShortComplex i).X₁ := isDiscreteRep_subrepresentation M N hN
  have : IsDiscreteRep (cokerShortComplex i).X₂ := inferInstanceAs (IsDiscreteRep M)
  have : Finite (cokerShortComplex i).X₂ := inferInstanceAs (Finite M)
  have : IsDiscreteRep (cokerShortComplex i).X₃ :=
    isDiscreteRep_quotient M (LinearMap.range i.hom.toLinearMap) (range_hom_le_comap i)
  have hG := hasFiniteCohomology_galois_top K Ksep
  have hχ := eulerChar_shortExact hPdvd hG hS hM

  have hrange : LinearMap.range i.hom.toLinearMap = N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hX₁ : Nat.card (cokerShortComplex i).X₁ = Nat.card N := rfl
  have hX₃ : Nat.card (cokerShortComplex i).X₃ = Nat.card (M ⧸ LinearMap.range i.hom.toLinearMap) := rfl
  have hcardM : Nat.card M = Nat.card (cokerShortComplex i).X₁ * Nat.card (cokerShortComplex i).X₃ := by
    rw [hX₁, hX₃, Submodule.card_eq_card_quotient_mul_card (LinearMap.range i.hom.toLinearMap),
      Nat.card_congr (LinearEquiv.ofInjective i.hom.toLinearMap hi).toEquiv.symm]
  have : Finite (cokerShortComplex i).X₁ := Finite.of_injective _ hi
  have : Finite (cokerShortComplex i).X₃ :=
    Finite.of_surjective _ (Submodule.mkQ_surjective (LinearMap.range i.hom.toLinearMap))
  have h1 : 1 < Nat.card (cokerShortComplex i).X₁ := by
    rw [hX₁]
    obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have : Nontrivial N := ⟨⟨⟨x, hxN⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have h3 : 1 < Nat.card (cokerShortComplex i).X₃ := by
    rw [hX₃, hrange]
    have : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.2 htop
    have : Finite (M ⧸ N) := Finite.of_surjective _ (Submodule.mkQ_surjective N)
    exact Finite.one_lt_card
  have hpos1 : 0 < Nat.card (cokerShortComplex i).X₁ := by omega
  have hpos3 : 0 < Nat.card (cokerShortComplex i).X₃ := by omega
  have hlt1 : Nat.card (cokerShortComplex i).X₁ < n := by
    rw [← hn, hcardM]
    exact lt_mul_of_one_lt_right hpos1 h3
  have hlt3 : Nat.card (cokerShortComplex i).X₃ < n := by
    rw [← hn, hcardM]
    exact lt_mul_of_one_lt_left hpos3 h1
  have hP1 : (Nat.card (cokerShortComplex i).X₁ : K) ≠ 0 :=
    hPdvd _ _ ⟨_, hcardM⟩ hM
  have hP3 : (Nat.card (cokerShortComplex i).X₃ : K) ≠ 0 :=
    hPdvd _ _ ⟨_, hcardM.trans (mul_comm _ _)⟩ hM
  change eulerChar (cokerShortComplex i).X₂ = _
  rw [hχ, ih _ hlt1 _ rfl hP1, ih _ hlt3 _ rfl hP3]
  rw [hcardM, card_quotient_span_natCast_mul hP1 hP3]
  push_cast
  rw [mul_inv]

theorem eulerChar_galois (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M] [Finite M]
    (hM : (Nat.card M : K) ≠ 0) :
    eulerChar M = (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ)⁻¹ :=
  eulerChar_galois_of_card_eq _ M rfl hM

theorem card_cohomology_mul_div_eq (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M] [Finite M]
    (hM : (Nat.card M : K) ≠ 0) :
    (Nat.card (cohomology M 0) : ℚ) * Nat.card (cohomology M 2) / Nat.card (cohomology M 1) =
      (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ)⁻¹ := by
  rw [← eulerChar_eq, eulerChar_galois M hM]

end Main

end GroundTheory.ProfCoh
