import Mathlib
import GroundTheory.TateCohomology.PGroupCohTrivialInt
import GroundTheory.TateCohomology.Annihilation
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

section Helpers

universe u

variable {k H : Type u} [CommRing k] [Group H] {A B : Rep.{u} k H}

theorem hom_nsmul_apply (f : A ⟶ B) (n : ℕ) (x : A) : f.hom (n • x) = n • f.hom x :=
  map_nsmul f.hom.toLinearMap n x

theorem hom_zero_apply (f : A ⟶ B) : f.hom 0 = 0 :=
  map_zero f.hom.toLinearMap

end Helpers

variable {G : Type} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]

theorem isZero_tateCohomology_of_nsmul_injective {H : Type} [Group H] [Fintype H]
    (hH : IsPGroup p H) (A : Rep ℤ H) (n : ℤ)
    (hinj : Function.Injective fun x : tateCohomology A n => p • x) :
    IsZero (tateCohomology A n) := by
  obtain ⟨m, hm⟩ := hH.exists_card_eq
  have hcard : Fintype.card H = p ^ m := by rw [← Nat.card_eq_fintype_card, hm]
  have key : ∀ (j : ℕ) (x : tateCohomology A n), p ^ j • x = 0 → x = 0 := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      apply ih
      apply hinj
      change p • (p ^ j • x) = p • 0
      rw [smul_zero, ← mul_smul, ← pow_succ']
      exact hx
  have : Subsingleton (tateCohomology A n) :=
    ⟨fun x y => by
      rw [key m x (hcard ▸ card_smul_tateCohomology A n x),
        key m y (hcard ▸ card_smul_tateCohomology A n y)]⟩
  exact ModuleCat.isZero_of_subsingleton _

theorem tateAcyclic_of_shortExact_of_comp_eq_nsmul {H : Type} [Group H] [Fintype H]
    (hH : IsPGroup p H) {S : ShortComplex (Rep ℤ H)} (hS : S.ShortExact) (e : S.X₂ ≅ S.X₁)
    (hf : S.f ≫ e.hom = p • 𝟙 S.X₁) (h₃ : TateAcyclic S.X₃) : TateAcyclic S.X₁ := by
  intro n
  have hmono : Mono ((tateCohomologyFunctor n).map S.f) := by
    have h : Mono ((tateCohomologyFunctor (n - 1 + 1)).map S.f) :=
      (TateCohomology.exact₁ hS (n - 1)).mono_g ((h₃ (n - 1)).eq_of_src _ _)
    rwa [sub_add_cancel] at h
  have : (tateCohomologyFunctor (R := ℤ) (G := H) n).Additive := by
    unfold tateCohomologyFunctor; infer_instance
  have hmono' : Mono ((tateCohomologyFunctor n).map (p • 𝟙 S.X₁)) := by
    rw [← hf, Functor.map_comp]
    infer_instance
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id] at hmono'
  have hinj := (ModuleCat.mono_iff_injective _).1 hmono'
  refine isZero_tateCohomology_of_nsmul_injective hH S.X₁ n fun a b hab => hinj ?_
  simpa using hab

theorem tateAcyclic_cohTrivial_of_isZero_of_isZero_of_noTorsion (hG : IsPGroup p G)
    (A : Rep ℤ G) (hA : ∀ x : A, p • x = 0 → x = 0) (q : ℤ)
    (h₁ : IsZero (tateCohomology A q)) (h₂ : IsZero (tateCohomology A (q + 1))) :
    TateAcyclic A ∧ CohTrivial A := by
  let f : A ⟶ A := p • 𝟙 A
  have hf : Function.Injective f.hom := fun a b hab => by
    have h : p • (a - b) = 0 := by
      rw [smul_sub, sub_eq_zero]
      simpa [f, nsmul_id_hom_apply] using hab
    exact sub_eq_zero.mp (hA _ h)
  have : Mono f := (Rep.mono_iff_injective f).2 hf
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
      mono_f := inferInstanceAs (Mono f)
      epi_g := coequalizer.π_epi }
  have hC : IsZero (tateCohomology S.X₃ q) :=
    (TateCohomology.exact₃ hS q).isZero_X₂ (h₁.eq_of_src _ _) (h₂.eq_of_tgt _ _)
  have hCt : ∀ y : S.X₃, p • y = 0 := by
    have hsurj : Function.Surjective (cokernel.π f).hom :=
      (Rep.epi_iff_surjective _).1 coequalizer.π_epi
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    have h0 := congrArg (fun φ : A ⟶ cokernel f => φ.hom x) (cokernel.condition f)
    simp only [Rep.hom_comp, Rep.zero_hom] at h0
    rw [← hom_nsmul_apply, ← nsmul_id_hom_apply]
    exact h0
  obtain ⟨tC, cC⟩ := tateAcyclic_cohTrivial_of_isZero_of_nsmul_eq_zero hG S.X₃ hCt q hC
  have hf0 : S.f ≫ (Iso.refl S.X₁).hom = p • 𝟙 S.X₁ := Category.comp_id _
  have t := tateAcyclic_of_shortExact_of_comp_eq_nsmul hG hS (Iso.refl S.X₁) hf0 tC
  refine ⟨t, ?_⟩
  intro H _
  have hS' : (S.map (resFunctor H.subtype)).ShortExact := (shortExact_res H.subtype).2 hS
  have h₃ : TateAcyclic (S.map (resFunctor H.subtype)).X₃ := by
    rw [ShortComplex.map_X₃]; exact cC H
  have hf' : (S.map (resFunctor H.subtype)).f ≫ (Iso.refl (S.map (resFunctor H.subtype)).X₁).hom =
      p • 𝟙 (S.map (resFunctor H.subtype)).X₁ := by
    show (resFunctor H.subtype).map (p • 𝟙 A) ≫ 𝟙 _ = _
    rw [Category.comp_id, Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  have c := tateAcyclic_of_shortExact_of_comp_eq_nsmul (hG.to_subgroup H) hS'
    (Iso.refl (S.map (resFunctor H.subtype)).X₁) hf' h₃
  rw [ShortComplex.map_X₁] at c
  exact c

theorem tateAcyclic_cohTrivial_of_isZero_of_isZero (hG : IsPGroup p G) (A : Rep ℤ G) (q : ℤ)
    (h₁ : IsZero (tateCohomology A q)) (h₂ : IsZero (tateCohomology A (q + 1))) :
    TateAcyclic A ∧ CohTrivial A := by
  let π : Rep.free ℤ G A.V ⟶ A := Rep.freeLift ℤ G A fun a => a
  have hπ : Function.Surjective π.hom := fun a =>
    ⟨Finsupp.single a (MonoidAlgebra.single 1 1), by
      have hmod : A.hV2 = AddCommGroup.toIntModule A.V := Subsingleton.elim _ _
      simp only [π]
      simp
      rw [hmod]
      exact one_zsmul a⟩
  have : Epi π := (Rep.epi_iff_surjective π).2 hπ
  let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π)
      mono_f := equalizer.ι_mono
      epi_g := inferInstanceAs (Epi π) }
  have hfree : ∀ x : Rep.free ℤ G A.V, p • x = 0 → x = 0 := fun x hx =>
    (smul_eq_zero.mp hx).resolve_left (Fact.out : p.Prime).ne_zero
  have hK : ∀ x : S.X₁, p • x = 0 → x = 0 := by
    have hinj : Function.Injective (kernel.ι π).hom :=
      (Rep.mono_iff_injective _).1 equalizer.ι_mono
    intro x hx
    apply hinj
    rw [hom_zero_apply]
    apply hfree
    rw [← hom_nsmul_apply, hx, hom_zero_apply]
  have h2 : TateAcyclic S.X₂ := tateAcyclic_free A.V
  have k₁ : IsZero (tateCohomology S.X₁ (q + 1)) :=
    h₁.of_iso (@asIso _ _ _ _ (TateCohomology.δ hS q) (isIso_δ_of_tateAcyclic hS h2 q)).symm
  have k₂ : IsZero (tateCohomology S.X₁ (q + 1 + 1)) :=
    h₂.of_iso (@asIso _ _ _ _ (TateCohomology.δ hS (q + 1))
      (isIso_δ_of_tateAcyclic hS h2 (q + 1))).symm
  obtain ⟨tK, cK⟩ :=
    tateAcyclic_cohTrivial_of_isZero_of_isZero_of_noTorsion hG S.X₁ hK (q + 1) k₁ k₂
  have t3 := TateAcyclic.of_shortExact_X₁ hS h2 tK
  have c2 : CohTrivial S.X₂ := cohTrivial_free A.V
  have c3 := CohTrivial.of_shortExact_X₁ hS c2 cK
  exact ⟨t3, c3⟩

theorem cohTrivial_of_isZero_of_isZero (hG : IsPGroup p G) (A : Rep ℤ G) (q : ℤ)
    (h₁ : IsZero (tateCohomology A q)) (h₂ : IsZero (tateCohomology A (q + 1))) :
    CohTrivial A :=
  (tateAcyclic_cohTrivial_of_isZero_of_isZero hG A q h₁ h₂).2

end GroundTheory.GroupCoh
