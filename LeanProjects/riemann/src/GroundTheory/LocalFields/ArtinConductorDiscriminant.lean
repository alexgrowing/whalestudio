import Mathlib
import GroundTheory.LocalFields.ArtinConductorAbelian

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Module Representation

section Bot

theorem ne_bot_of_nontrivial_aut {F E : Type*} [Field F] [Field E] [Algebra F E]
    (M : IntermediateField F E) [FiniteDimensional F M] [IsGalois F M]
    (hM : Nontrivial (M ≃ₐ[F] M)) : M ≠ ⊥ := by
  rintro rfl
  have h1 : Nat.card ((⊥ : IntermediateField F E) ≃ₐ[F] (⊥ : IntermediateField F E)) = 1 := by
    rw [IsGalois.card_aut_eq_finrank, IntermediateField.finrank_bot]
  have := Finite.one_lt_card_iff_nontrivial.mpr hM
  omega

end Bot

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Jump

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isGreatest_artinConductor_charRep_sub_one (ψ : (L ≃ₐ[K] L) →* ℂˣ) (hψ : ψ ≠ 1) :
    IsGreatest {v : ℝ | ¬ upperRamificationGroup K L v ≤ ψ.ker}
      ((artinConductor (charRep ψ) : ℝ) - 1) := by
  by_cases h0 : lowerRamificationGroup K L 0 ≤ ψ.ker
  · have hf : artinConductor (charRep ψ) = 0 := by
      rw [artinConductor_eq_zero_iff]
      intro σ hσ
      have h1 : ψ σ = 1 := h0 hσ
      ext
      simp [h1]
    rw [hf, Rat.cast_zero, zero_sub]
    refine ⟨?_, fun v hv ↦ ?_⟩
    · show ¬ upperRamificationGroup K L (-1) ≤ ψ.ker
      rw [upperRamificationGroup_of_nonpos (by norm_num), lowerRamificationGroupReal_eq_top le_rfl]
      intro htop
      apply hψ
      refine MonoidHom.ext fun σ ↦ ?_
      rw [MonoidHom.one_apply]
      exact htop (Subgroup.mem_top σ)
    · by_contra hlt
      rw [not_le] at hlt
      apply hv
      refine le_trans ?_ h0
      show lowerRamificationGroup K L ⌈herbrandPsi K L v⌉ ≤ _
      apply lowerRamificationGroup_antitone
      have : -1 < herbrandPsi K L v := by
        rw [← herbrandPsi_of_nonpos (K := K) (L := L) (show (-1 : ℝ) ≤ 0 by norm_num)]
        exact herbrandPsi_strictMono hlt
      exact Int.le_ceil_iff.mpr (by push_cast; linarith)
  · obtain ⟨j, hj, hj1⟩ := exists_lowerRamificationGroup_jump ψ h0
    rw [artinConductor_charRep_eq_one_add_herbrandPhi ψ hj hj1, add_sub_cancel_left]
    refine ⟨?_, fun v hv ↦ ?_⟩
    · show ¬ upperRamificationGroup K L _ ≤ ψ.ker
      rw [upperRamificationGroup_herbrandPhi_natCast]
      exact hj
    · by_contra hlt
      rw [not_le] at hlt
      exact hv ((upperRamificationGroup_le_of_herbrandPhi_lt hlt).trans hj1)

theorem exists_nat_swanConductor_eq_of_artinConductor_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (L ≃ₐ[K] L) V) {n : ℕ}
    (hn : artinConductor ρ = n) : ∃ k : ℕ, swanConductor ρ = k := by
  have h := artinConductor_eq_codim_add_swanConductor ρ
  have hs := swanConductor_nonneg ρ
  rw [hn] at h
  set c := finrank ℂ V -
    finrank ℂ (Representation.invariants (ρ.comp (lowerRamificationGroup K L 0).subtype))
  have hc : c ≤ n := by exact_mod_cast (show (c : ℚ) ≤ n by linarith)
  refine ⟨n - c, ?_⟩
  rw [Nat.cast_sub hc]
  linarith

end Jump

section Match

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {M : Type*} [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M] [FiniteDimensional K M]

theorem upperRamificationGroup_le_ker_comp_iff (r : (L ≃ₐ[K] L) →* (M ≃ₐ[K] M))
    (hr : ∀ v, (upperRamificationGroup K L v).map r = upperRamificationGroup K M v)
    (ψ : (M ≃ₐ[K] M) →* ℂˣ) (hψ : Function.Injective ψ) (v : ℝ) :
    upperRamificationGroup K L v ≤ (ψ.comp r).ker ↔ upperRamificationGroup K M v = ⊥ := by
  have hker : (ψ.comp r).ker = r.ker := by
    ext σ
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact ⟨fun h ↦ hψ (h.trans ψ.map_one.symm), fun h ↦ by rw [h, map_one]⟩
  rw [hker, ← hr v, Subgroup.map_eq_bot_iff]

theorem isGreatest_artinConductor_charRep_comp_sub_one (r : (L ≃ₐ[K] L) →* (M ≃ₐ[K] M))
    (hr : ∀ v, (upperRamificationGroup K L v).map r = upperRamificationGroup K M v)
    (ψ : (M ≃ₐ[K] M) →* ℂˣ) (hψ : Function.Injective ψ) (hM : Nontrivial (M ≃ₐ[K] M)) :
    IsGreatest {v : ℝ | upperRamificationGroup K M v ≠ ⊥}
      ((artinConductor (charRep (ψ.comp r)) : ℝ) - 1) := by
  have hne : ψ.comp r ≠ 1 := by
    intro h1
    have htop : upperRamificationGroup K M (-1) = ⊥ := by
      rw [← upperRamificationGroup_le_ker_comp_iff r hr ψ hψ, h1, MonoidHom.ker_one]
      exact le_top
    rw [upperRamificationGroup_of_nonpos (by norm_num), lowerRamificationGroupReal_eq_top le_rfl]
      at htop
    exact (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup (M ≃ₐ[K] M))).mp
      (Subgroup.topEquiv.symm.nontrivial) htop
  have h := isGreatest_artinConductor_charRep_sub_one (ψ.comp r) hne
  have hset : {v : ℝ | ¬ upperRamificationGroup K L v ≤ (ψ.comp r).ker} =
      {v : ℝ | upperRamificationGroup K M v ≠ ⊥} := by
    ext v
    simp only [Set.mem_ofPred_eq, upperRamificationGroup_le_ker_comp_iff r hr ψ hψ]
  rwa [hset] at h

end Match

section Conductor

variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]

theorem artinConductor_charRep_comp_restrictAut_eq_conductor {L M : IntermediateField K Ω}
    [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K M] [IsAbelianGalois K M]
    (h : M ≤ L) (ψ : (M ≃ₐ[K] M) →* ℂˣ) (hψ : Function.Injective ψ) :
    artinConductor (charRep (ψ.comp (restrictAut h))) = conductor M := by
  have hr := map_upperRamificationGroup_restrictAut (K := K) (Ω := Ω) h
  rcases subsingleton_or_nontrivial (M ≃ₐ[K] M) with hM | hM
  · have hbot : ∀ v, upperRamificationGroup K M v = ⊥ := fun v ↦ Subsingleton.elim _ _
    have hc : conductor M = 0 := by
      have := (upperRamificationGroup_natCast_eq_bot_iff M 0).mp (hbot _)
      omega
    have hf : artinConductor (charRep (ψ.comp (restrictAut h))) = 0 := by
      rw [artinConductor_eq_zero_iff]
      intro σ _
      have h1 : restrictAut h σ = 1 := Subsingleton.elim _ _
      ext
      simp [h1]
    rw [hc, hf, Nat.cast_zero]
  · have h1 := isGreatest_artinConductor_charRep_comp_sub_one (restrictAut h) hr ψ hψ hM
    have h2 := isGreatest_conductor_sub_one M (ne_bot_of_nontrivial_aut M hM)
    have h3 := h1.unique h2
    have h4 : ((artinConductor (charRep (ψ.comp (restrictAut h))) : ℚ) : ℝ) =
        ((conductor M : ℚ) : ℝ) := by
      rw [Rat.cast_natCast]
      linarith
    exact Rat.cast_injective h4

theorem artinConductor_charRep_eq_conductor (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] (ψ : (L ≃ₐ[K] L) →* ℂˣ) (hψ : Function.Injective ψ) :
    artinConductor (charRep ψ) = conductor L := by
  have h := artinConductor_charRep_comp_restrictAut_eq_conductor (le_refl L) ψ hψ
  have hid : restrictAut (le_refl L) = MonoidHom.id (L ≃ₐ[K] L) := by
    ext σ x
    rw [restrictAut_apply]
    rfl
  rwa [hid, MonoidHom.comp_id] at h

end Conductor

section Dual

variable {G : Type*} [Group G]

theorem addChar_apply_ne_zero (χ : AddChar (Additive G) ℂ) (a : Additive G) : χ a ≠ 0 := by
  intro h
  have := χ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

def monoidHomEquivAddChar : (G →* ℂˣ) ≃ AddChar (Additive G) ℂ where
  toFun ψ :=
    { toFun := fun a ↦ (ψ a.toMul : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b ↦ by simp }
  invFun χ :=
    { toFun := fun g ↦ Units.mk0 (χ (Additive.ofMul g)) (addChar_apply_ne_zero χ _)
      map_one' := Units.ext (by simp)
      map_mul' := fun g h ↦ Units.ext (by simp [AddChar.map_add_eq_mul]) }
  left_inv ψ := by
    ext g
    simp
  right_inv χ := by
    ext a
    simp

end Dual

section Abelian

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsAbelianGalois K L]

end Abelian

section Monomial

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

theorem exists_nat_charArtinConductor_inducedFun (M : IntermediateField K L)
    (ψ : (L ≃ₐ[M] L) →* ℂˣ) :
    ∃ n : ℕ, charArtinConductor K L (inducedFun fun h ↦ (ψ h : ℂ)) = n := by
  obtain ⟨m, hm⟩ := exists_nat_artinConductor_charRep_eq ψ
  refine ⟨residueDegree K M * differentExponent K M + residueDegree K M * m, ?_⟩
  have h1 : (fun h ↦ (ψ h : ℂ)) = (charRep ψ).character :=
    funext fun h ↦ (character_charRep ψ h).symm
  rw [h1, charArtinConductor_inducedFun, ← artinConductor_eq_charArtinConductor, hm,
    character_charRep, map_one, Units.val_one]
  push_cast
  ring

end Monomial

end GroundTheory.LocalField
