import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesPrincipalAnyFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOfSmallStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelArtin

theorem exists_socle (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C]
    (hm : IsLocalRing.maximalIdeal C ≠ ⊥) :
    ∃ e : C, e ≠ 0 ∧ e ∈ IsLocalRing.maximalIdeal C ∧ ∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0 := by
  set m := IsLocalRing.maximalIdeal C
  have hnil : IsNilpotent m := (isArtinianRing_iff_isNilpotent_maximalIdeal C).mp inferInstance
  have hex : ∃ k, m ^ k = ⊥ := by
    obtain ⟨k, hk⟩ := hnil
    exact ⟨k, by rw [hk]; rfl⟩
  classical
  let k := Nat.find hex
  have hk : m ^ k = ⊥ := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    have : m ^ k = ⊤ := by rw [h0, pow_zero, Ideal.one_eq_top]
    rw [this] at hk
    exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top (top_le_iff.mp (hk ▸ bot_le))
  have hk1 : k ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hk
    exact hm hk
  have hprev : m ^ (k - 1) ≠ ⊥ := Nat.find_min hex (by omega)
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hprev
  refine ⟨e, he0, ?_, ?_⟩
  · exact Ideal.pow_le_self (by omega) he
  · intro a ha
    have : a * e ∈ m ^ k := by
      have hk' : k = (k - 1) + 1 := by omega
      rw [hk', pow_succ']
      exact Ideal.mul_mem_mul ha he
    rw [hk] at this
    simpa using this

theorem main : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F
  suffices H : ∀ (N : ℕ) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C],
      Module.length C C = N → ∀ (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)),
      c.Principal → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f by
    intro C _ _ _ β c hc
    obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp (Module.length_ne_top (R := C) (M := C))
    exact H N C hN.symm β c hc
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro C _ _ _ hN β c hc
  by_cases hm : IsLocalRing.maximalIdeal C = ⊥
  · letI : Field C := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm).toField
    exact GlobalTheory.T.siegel_family_classifies_principal_any_field g n hg hn hodd F C β c hc
  obtain ⟨e, he0, hem, hann⟩ := exists_socle C hm
  set I : Ideal C := Ideal.span {e}
  have hIt : I ≠ ⊤ := by
    intro h
    have : I ≤ IsLocalRing.maximalIdeal C := (Ideal.span_singleton_le_iff_mem _).mpr hem
    rw [h] at this
    exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top (top_le_iff.mp this)
  haveI : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIt
  haveI : IsLocalRing (C ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

  have hlenQ : Module.length C (C ⧸ I) = Module.length (C ⧸ I) (C ⧸ I) :=
    Module.length_eq_of_surjective (R := C ⧸ I) (S := C) (M := C ⧸ I) Ideal.Quotient.mk_surjective
  have hsum : Module.length C C = Module.length C I + Module.length C (C ⧸ I) :=
    Module.length_eq_add_of_exact I.subtype I.mkQ I.injective_subtype I.mkQ_surjective
      (LinearMap.exact_subtype_mkQ I)
  haveI : Nontrivial I := ⟨⟨⟨e, Ideal.subset_span rfl⟩, 0, fun h => he0 (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.length C I := Module.length_pos
  rw [hN, hlenQ] at hsum
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (show Module.length C I ≠ ⊤ from fun h => by
    rw [h, top_add] at hsum; exact ENat.natCast_ne_top _ hsum)
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (show Module.length (C ⧸ I) (C ⧸ I) ≠ ⊤ from fun h => by
    rw [h, add_top] at hsum; exact ENat.natCast_ne_top _ hsum)
  rw [← hb, ← hM] at hsum
  rw [← hb] at hpos
  have hb0 : 0 < b := by exact_mod_cast hpos
  have hNM : N = b + M := by exact_mod_cast hsum
  have hlt : M < N := by omega
  refine GlobalTheory.T.exists_siegPB_lift_of_quotient_lift g n hg hn hodd F C e hem hann β c hc ?_
  intro c₀ hpb
  have hcomm : spMap (Ideal.Quotient.mk I) ≫ spMap β = spMap ((Ideal.Quotient.mk I).comp β) := by
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hc₀ : c₀.Principal :=
    (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) (Sp C) (Sp (C ⧸ I)) (spMap β)
      (spMap ((Ideal.Quotient.mk I).comp β)) (spMap (Ideal.Quotient.mk I)) c hcomm).2 c₀ hpb hc
  exact ih M hlt (C ⧸ I) hM.symm _ c₀ hc₀

end GlobalTheory.SiegelArtin
