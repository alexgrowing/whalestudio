import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoOfIsIntegrallyClosedOfIsRegularLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdealTransformOfForallSmulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularOfEtalePuncturedOfDepthPosDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegerOfMaximalIdealPowSmulIsIntegerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgOfSaturatedIdealPowerIntoImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationOfInjectiveCokernelKilledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoOfRegularQuotientNoSocleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulMemOfForallExistsStatement
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem exists_finite_depth_two_hull_of_etale_off_closed_point : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S → ∀ (A : Type) [CommRing A] [Algebra S A] [Module.Finite S A], ReciprocityTheory.CA.ModDepthGE S A 1 → (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra S A'), Module.Finite S A' ∧ ∃ ι : A →ₐ[S] A', Function.Injective ι ∧ ReciprocityTheory.CA.ModDepthGE S A' 2 ∧ (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A')) ∧ ∃ k : ℕ, ∀ x ∈ maximalIdeal S ^ k, ∀ y : A', x • y ∈ ι.range := by
  intro S _ _ hdim A _ _ _ hdep het
  obtain ⟨hSd, hSic⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing S
  have htf : ∀ s : S, s ≠ 0 → IsSMulRegular A s := GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos_domain' S A hdep het
  let K := FractionRing S
  let j : A →ₐ[S] K ⊗[S] A := Algebra.TensorProduct.includeRight
  have hj : ∀ a, j a = TensorProduct.mk S K A 1 a := fun a => rfl
  haveI : IsLocalizedModule (nonZeroDivisors S) (TensorProduct.mk S K A 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).mpr (TensorProduct.isBaseChange S A K)
  have hjinj : Function.Injective j := by
    intro a b hab
    rw [hj, hj] at hab
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors S) hab
    exact htf c (nonZeroDivisors.coe_ne_zero c) hc

  have hVtf : ∀ s : S, s ≠ 0 → ∀ v w : K ⊗[S] A, s • v = s • w → v = w := by
    intro s hs v w h
    rw [← algebraMap_smul K s v, ← algebraMap_smul K s w] at h
    have hs' : algebraMap S K s ≠ 0 := by
      rw [ne_eq, ← map_zero (algebraMap S K)]
      exact fun e => hs (IsFractionRing.injective S K e)
    exact smul_right_injective _ hs' h
  let B := idealTransform S (maximalIdeal S) A
  have hjB : ∀ a, j a ∈ B := fun a => ⟨0, fun b _ => ⟨b • a, by simp [j]⟩⟩
  let ι : A →ₐ[S] B := j.codRestrict B hjB
  have hιinj : Function.Injective ι := fun a b h => hjinj (congrArg Subtype.val h)
  have hrange : ∀ y : B, y ∈ ι.range ↔ (y : K ⊗[S] A) ∈ j.range := by
    intro y
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, ha⟩; exact ⟨a, Subtype.ext ha⟩

  have hfg : (Subalgebra.toSubmodule B).FG := by
    refine GlobalTheory.T.fg_of_ideal_pow_smul_mem_range_tensor S (maximalIdeal S) (GlobalTheory.T.isInteger_of_maximalIdeal_pow_smul_isInteger' S hdim) A _ fun z hz => ?_
    obtain ⟨k, hk⟩ := hz
    exact ⟨k, fun a ha => by obtain ⟨b, hb⟩ := hk a ha; exact ⟨b, hb⟩⟩
  haveI hfin : Module.Finite S B := Module.Finite.iff_fg.mpr hfg

  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ a ∈ maximalIdeal S ^ k, ∀ y : B, a • y ∈ ι.range.toSubmodule := by
    refine GlobalTheory.T.exists_pow_smul_mem_of_forall_exists' S (maximalIdeal S) B _ fun y => ?_
    obtain ⟨k, hk⟩ := y.2
    exact ⟨k, fun a ha => (hrange _).2 (hk a ha)⟩
  refine ⟨B, inferInstance, inferInstance, hfin, ι, hιinj, ?_, ?_, k, hk⟩
  ·
    obtain ⟨q, -, hq0, hqm⟩ := exists_isPrime_ne_bot_lt_maximalIdeal_of_two_le_ringKrullDim S hdim
    have hm0 : maximalIdeal S ≠ ⊥ := (bot_le.trans_lt hqm).ne'
    obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm0
    haveI : Nontrivial A := by
      obtain ⟨rs, -, -, hreg⟩ := hdep
      by_contra hA
      rw [not_nontrivial_iff_subsingleton] at hA
      exact hreg.2 (Subsingleton.elim _ _)
    haveI : Nontrivial B := nontrivial_of_ne (ι 0) (ι 1) (hιinj.ne zero_ne_one)
    have hxreg : IsSMulRegular B x := fun u v h =>
      Subtype.ext (hVtf x hx0 _ _ (congrArg Subtype.val h))
    refine GlobalTheory.T.modDepthGE_two_of_regular_quotient_no_socle S B x hxm hxreg fun u hu => ?_
    let w : K ⊗[S] A := (algebraMap S K x)⁻¹ • (u : K ⊗[S] A)
    have hxw : x • w = u := by
      simp only [w, ← algebraMap_smul K x, smul_smul]
      rw [mul_inv_cancel₀, one_smul]
      rw [ne_eq, ← map_zero (algebraMap S K)]
      exact fun e => hx0 (IsFractionRing.injective S K e)
    have hwB : w ∈ B := by
      refine mem_idealTransform_of_forall_smul_mem w fun a ha => ?_
      obtain ⟨v, -, hv⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp (hu a ha)
      have : a • w = v := by
        apply hVtf x hx0
        rw [smul_comm, hxw]
        exact (congrArg Subtype.val hv).symm
      rw [this]; exact v.2
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨⟨w, hwB⟩, Submodule.mem_top, Subtype.ext hxw⟩
  · intro p _ hp
    have hnot : ¬ maximalIdeal S ^ k ≤ p := fun h =>
      hp ((maximalIdeal.isMaximal S).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.IsPrime.le_of_pow_le h)).symm
    obtain ⟨s, hs, hsp⟩ := Set.not_subset.mp hnot
    exact GlobalTheory.T.etale_localization_of_injective_cokernel_killed S A B ι hιinj p s hsp (hk s hs) (het p hp)

end GlobalTheory
