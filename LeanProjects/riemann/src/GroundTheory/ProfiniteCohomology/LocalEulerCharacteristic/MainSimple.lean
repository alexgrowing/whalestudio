import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainGalois
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCount
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCoind
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Coprime
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Vanishing
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing
import GroundTheory.ProfiniteCohomology.LocalClassFormationAlt
import GroundTheory.ProfiniteCohomology.PoincareDuality
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

section Fixed

variable {k G : Type*} [CommRing k] [Group G]

def fixedSubmodule (M : Rep k G) (W : Subgroup G) : Submodule k M where
  carrier := {m | ∀ g ∈ W, M.ρ g m = m}
  add_mem' {a b} ha hb g hg := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, ha g hg, hb g hg]
  zero_mem' g _ := map_zero _
  smul_mem' c m hm g hg := by
    simp only [Set.mem_ofPred_eq] at hm ⊢
    rw [map_smul, hm g hg]

theorem fixedSubmodule_le_comap (M : Rep k G) (W : Subgroup G) [hW : W.Normal] (g : G) :
    fixedSubmodule M W ≤ (fixedSubmodule M W).comap (M.ρ g) := by
  intro m hm w hw
  have h := hm (g⁻¹ * w * g) (by simpa using hW.conj_mem w hw g⁻¹)
  have e : w * g = g * (g⁻¹ * w * g) := by group
  change M.ρ w (M.ρ g m) = M.ρ g m
  calc M.ρ w (M.ρ g m) = M.ρ (w * g) m := by rw [map_mul]; rfl
    _ = M.ρ (g * (g⁻¹ * w * g)) m := by rw [e]
    _ = M.ρ g (M.ρ (g⁻¹ * w * g) m) := by rw [map_mul]; rfl
    _ = M.ρ g m := by rw [h]

end Fixed

section Simple

attribute [-instance] ULift.module

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem eulerChar_of_forall_eq_bot_or_eq_top (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M]
    [Finite M] [Nontrivial M] (hM : (Nat.card M : K) ≠ 0)
    (hsimple : ∀ N : Submodule (ULift.{0} ℤ) M, (∀ g, N ≤ N.comap (M.ρ g)) → N = ⊥ ∨ N = ⊤) :
    eulerChar M = (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ)⁻¹ := by

  obtain ⟨l, hlp, hldvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := M)).ne'
  have := Fact.mk hlp
  have : NeZero l := ⟨hlp.ne_zero⟩
  have hlK : (l : K) ≠ 0 := by
    obtain ⟨c, hc⟩ := hldvd
    intro h
    apply hM
    rw [hc, Nat.cast_mul, h, zero_mul]
  have hPdvd : ∀ m n : ℕ, m ∣ n → (n : K) ≠ 0 → (m : K) ≠ 0 := by
    rintro m n ⟨c, rfl⟩ hn hm
    apply hn
    rw [Nat.cast_mul, hm, zero_mul]
  have hPmul : ∀ m n : ℕ, (m : K) ≠ 0 → (n : K) ≠ 0 → ((m * n : ℕ) : K) ≠ 0 := by
    intro m n hm hn
    rw [Nat.cast_mul]
    exact mul_ne_zero hm hn

  have hMl : ∀ m : M, l • m = 0 := by
    let N : Submodule (ULift.{0} ℤ) M := LinearMap.ker (l • LinearMap.id)
    have hN : ∀ g, N ≤ N.comap (M.ρ g) := fun g m hm => by
      simp only [N, LinearMap.mem_ker, Submodule.mem_comap, LinearMap.smul_apply,
        LinearMap.id_apply] at hm ⊢
      rw [← map_nsmul, hm, map_zero]
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' l hldvd
    have hxN : x ∈ N := by
      simp only [N, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      rw [← hx]
      exact addOrderOf_nsmul_eq_zero x
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [addOrderOf_zero] at hx
      exact hlp.one_lt.ne hx
    rcases hsimple N hN with h | h
    · rw [h] at hxN
      exact absurd ((Submodule.mem_bot _).1 hxN) hx0
    · intro m
      have : m ∈ N := h ▸ Submodule.mem_top
      simpa [N] using this
  obtain ⟨d, hd⟩ := exists_card_eq_prime_pow_of_nsmul hMl
  have hG := hasFiniteCohomology_galois_top K Ksep

  let := algebraicValuativeRel K Ksep
  let := algebraicTopology K Ksep
  have := algebraicTopology_isValuativeTopology K Ksep
  have := algebraicValuativeRel_valuativeExtension K Ksep

  obtain ⟨V, hVM, hVμ⟩ : ∃ V : OpenNormalSubgroup Gal(Ksep/K),
      (∀ g ∈ (V : Subgroup Gal(Ksep/K)), ∀ m : M, M.ρ g m = m) ∧
        ∀ σ ∈ (V : Subgroup Gal(Ksep/K)), ∀ ζ : Ksep, ζ ^ l = 1 → σ ζ = ζ := by
    have hdisc := (isDiscreteRep_iff_forall_exists_openNormalSubgroup M).1 inferInstance
    choose U hU using hdisc
    obtain ⟨V, hV⟩ := OpenNormalSubgroup.exists_le_of_finite
      (fun o : Option M => o.elim (rootsOfUnityFixingNormal (K := K) (Ksep := Ksep) l) U)
    refine ⟨V, fun g hg m => ?_, fun σ hσ ζ hζ => ?_⟩
    · exact (Representation.mem_invariants _ _).1 (hU m) ⟨g, hV (some m) hg⟩
    · exact apply_eq_of_mem_rootsOfUnityFixing (hV none hσ) hζ
  have hμV : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)) := fun ζ hζ =>
    (mem_fixedField_iff _ _).2 fun σ hσ => hVμ σ hσ ζ hζ
  set L : IntermediateField K Ksep := fixedField (V : Subgroup Gal(Ksep/K)) with hL
  by_cases hlq : l = ringChar 𝓀[K]
  ·
    have hlE : ∀ E : IntermediateField K Ksep, (l : E) ≠ 0 := fun E h =>
      hlK ((algebraMap K E).injective (by rw [map_natCast, map_zero]; exact h))

    obtain ⟨m0, hm0, hm0fix⟩ := exists_ne_zero_forall_mem_eq M hMl
      (preimageOpen V (lowerRamificationGroup K L 1)) (V : Subgroup Gal(Ksep/K)) hVM (fun g hg => by
        obtain ⟨n, hn⟩ := isPGroup_lowerRamificationGroup_one K L ⟨restrictFixed V g, hg⟩
        refine ⟨n, ?_⟩
        rw [mem_V_iff_restrictFixed_eq_one, map_pow, hlq]
        exact congrArg Subtype.val hn)
    have h1fix : ∀ g ∈ (preimageOpen V (lowerRamificationGroup K L 1) : Subgroup Gal(Ksep/K)),
        ∀ m : M, M.ρ g m = m := by
      have htop := (hsimple _ (fixedSubmodule_le_comap M _)).resolve_left (fun h => hm0 (by
        have : m0 ∈ fixedSubmodule M (preimageOpen V (lowerRamificationGroup K L 1)) := hm0fix
        rw [h] at this
        exact (Submodule.mem_bot _).1 this))
      intro g hg m
      have : m ∈ fixedSubmodule M _ := htop ▸ Submodule.mem_top
      exact this g hg

    obtain ⟨nE, hnE⟩ := exists_card_quotient_eq_pow (E := fixedField (preimageOpen V
      (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) : Subgroup Gal(Ksep/K)))
      (p := l) (hlE _)
    have hX := eulerChar_coprime
      (U := preimageOpen V (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])))
      (V := preimageOpen V (lowerRamificationGroup K L 1)) hlK
      (preimageOpen_le_preimageOpen (lowerRamificationGroup_one_le_coprimeQuotientPreimage (K := K) (L := L)))
      (by
        rw [relIndex_preimageOpen, hlq]
        exact coprime_card_coprimeQuotientPreimage_quotient_lowerRamificationGroup_one (K := K) (L := L))
      (fun ζ hζ => pow_eq_one_mem_fixedField_preimageOpen hVμ
        (fun ζ' hζ' => pow_eq_one_mem_fixedField_lowerRamificationGroup_one (K := K) (L := L)
          (by rw [← hlq]; exact hζ')) hζ)
      (Rep.res ((preimageOpen V (coprimeQuotientPreimage (lowerRamificationGroup K L 0)
        (ringChar 𝓀[K])) : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) hMl
      (fun g hg m => h1fix g hg m) hnE

    have : IsCyclic (Gal(L/K) ⧸ coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) :=
      isCyclic_quotient_coprimeQuotientPreimage_lowerRamificationGroup (K := K) (L := L)
    have : IsCyclic (Gal(Ksep/K) ⧸ ((preimageOpen V (coprimeQuotientPreimage
        (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))) :=
      isCyclic_quotient_preimageOpen _
    obtain ⟨a, ha⟩ := exists_card_quotient_coprimeQuotientPreimage_lowerRamificationGroup_eq_pow
      (K := K) (L := L)
    have hcard : Nat.card (Gal(Ksep/K) ⧸ ((preimageOpen V (coprimeQuotientPreimage
        (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) : OpenSubgroup Gal(Ksep/K)) :
          Subgroup Gal(Ksep/K))) = l ^ a := by
      rw [card_quotient_preimageOpen, ha, hlq]
    have hC := eulerChar_res_eq_pow (P := fun m => (m : K) ≠ 0) hPdvd hPmul hG _ hcard M hM hMl

    have hfin : Module.finrank K (fixedField ((preimageOpen V (coprimeQuotientPreimage
        (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) : OpenSubgroup Gal(Ksep/K)) :
          Subgroup Gal(Ksep/K))) = l ^ a := by
      rw [← index_openSubgroup, Subgroup.index, hcard]
    obtain ⟨nK, hnK⟩ := exists_card_quotient_eq_pow (E := K) (p := l) hlK
    have hext := card_quotient_span_natCast_finiteExtension (K := K) (L := fixedField
      ((preimageOpen V (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) :
        OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))) l
    rw [hnE, hnK, hfin, ← pow_mul] at hext
    have hnE' : nE = nK * l ^ a := Nat.pow_right_injective hlp.two_le hext

    have hpos := eulerChar_pos hG M hM
    have key : eulerChar M ^ (l ^ a) = (((Nat.card M : ℚ) ^ nK)⁻¹) ^ (l ^ a) := by
      rw [← hC, hX, hnE', pow_mul, inv_pow]
    have hχ := (pow_left_inj₀ hpos.le (by positivity) (pow_ne_zero a hlp.ne_zero)).1 key
    rw [hχ, hd, card_quotient_span_natCast_pow hlK, hnK]
    push_cast
    ring
  ·
    have hl𝓀 : (l : 𝓀[K]) ≠ 0 := by
      rw [Ne, ringChar.spec]
      intro h
      exact hlq ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime 𝓀[K] _) hlp).1 h).symm
    have hRHS : Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) = 1 :=
      card_quotient_span_natCast_eq_one (by rw [hd, Nat.cast_pow]; exact pow_ne_zero _ hl𝓀)
    rw [hRHS, Nat.cast_one, inv_one]
    have hBle : coprimeRelPreimage (lowerRamificationGroup K L 0) (lowerRamificationGroup K L 1) l ≤
        lowerRamificationGroup K L 0 :=
      coprimeRelPreimage_le _ _ l
    by_cases hB : fixedSubmodule M (preimageOpen V (coprimeRelPreimage (lowerRamificationGroup K L 0)
        (lowerRamificationGroup K L 1) l)) = ⊥
    ·
      have hsub : ∀ i ≤ 2, Subsingleton (cohomology M i) := fun i hi =>
        subsingleton_cohomology_of_inertia hlp hl𝓀 (V := V.toOpenSubgroup) (le_preimageOpen _) hμV
          (fun g hg x hx hx1 => valuation_sub_lt_one_of_mem_preimageOpen hBle hg hx hx1)
          (by
            rw [relIndex_V_preimageOpen]
            exact coprime_card_coprimeRelPreimage_lowerRamificationGroup (K := K) (L := L) hlp hlq)
          M hMl hVM (fun m hm => by
            have : m ∈ fixedSubmodule M (preimageOpen V (coprimeRelPreimage
                (lowerRamificationGroup K L 0) (lowerRamificationGroup K L 1) l)) := hm
            rw [hB] at this
            exact (Submodule.mem_bot _).1 this) hi
      have h0 := hsub 0 (by norm_num)
      have h1 := hsub 1 (by norm_num)
      have h2 := hsub 2 le_rfl
      rw [eulerChar_eq, Nat.card_of_subsingleton (0 : cohomology M 0),
        Nat.card_of_subsingleton (0 : cohomology M 1), Nat.card_of_subsingleton (0 : cohomology M 2)]
      norm_num
    ·
      have hBfix : ∀ g ∈ (preimageOpen V (coprimeRelPreimage (lowerRamificationGroup K L 0)
          (lowerRamificationGroup K L 1) l) : Subgroup Gal(Ksep/K)), ∀ m : M, M.ρ g m = m := by
        have htop := (hsimple _ (fixedSubmodule_le_comap M _)).resolve_left hB
        intro g hg m
        have : m ∈ fixedSubmodule M _ := htop ▸ Submodule.mem_top
        exact this g hg
      obtain ⟨m0, hm0, hm0fix⟩ := exists_ne_zero_forall_mem_eq M hMl
        (preimageOpen V (primaryQuotientPreimage (lowerRamificationGroup K L 0) l))
        (preimageOpen V (coprimeRelPreimage (lowerRamificationGroup K L 0)
          (lowerRamificationGroup K L 1) l)) hBfix (fun g hg => by
          obtain ⟨n, hn⟩ := isPGroup_primaryQuotientPreimage_quotient_lowerRamificationGroup
            (K := K) (L := L) hlp (QuotientGroup.mk ⟨restrictFixed V g, hg⟩)
          refine ⟨n, ?_⟩
          rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hn
          rw [mem_preimageOpen, map_pow]
          simpa using hn)
      have hAfix : ∀ g ∈ (preimageOpen V (primaryQuotientPreimage (lowerRamificationGroup K L 0) l) :
          Subgroup Gal(Ksep/K)), ∀ m : M, M.ρ g m = m := by
        have htop := (hsimple _ (fixedSubmodule_le_comap M _)).resolve_left (fun h => hm0 (by
          have : m0 ∈ fixedSubmodule M (preimageOpen V
            (primaryQuotientPreimage (lowerRamificationGroup K L 0) l)) := hm0fix
          rw [h] at this
          exact (Submodule.mem_bot _).1 this))
        intro g hg m
        have : m ∈ fixedSubmodule M _ := htop ▸ Submodule.mem_top
        exact this g hg
      have hX := eulerChar_coprime (U := ⊤)
        (V := preimageOpen V (primaryQuotientPreimage (lowerRamificationGroup K L 0) l)) hlK le_top
        (by
          rw [show ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) = ⊤ from rfl,
            Subgroup.relIndex_top_right, index_preimageOpen]
          exact coprime_card_quotient_primaryQuotientPreimage_lowerRamificationGroup (K := K) (L := L) hlp)
        (fun ζ hζ => pow_eq_one_mem_fixedField_preimageOpen hVμ
          (fun ζ' hζ' => pow_eq_one_mem_fixedField_primaryQuotientPreimage (K := K) (L := L) hlp hlq hζ') hζ)
        (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) hMl
        (fun g hg m => hAfix g hg m) (n := 0)
        (by
          rw [pow_zero]
          exact card_quotient_span_natCast_eq_one (natCast_residueField_fixedField_ne_zero hl𝓀 ⊤))
      have hres : eulerChar (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) =
          eulerChar M := by
        simp only [eulerChar]
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [← Nat.card_eq_of_bijective _ (bijective_cohomologyRes_top M q)]
      rw [← hres, hX, pow_zero, inv_one]

end Simple

end GroundTheory.ProfCoh
