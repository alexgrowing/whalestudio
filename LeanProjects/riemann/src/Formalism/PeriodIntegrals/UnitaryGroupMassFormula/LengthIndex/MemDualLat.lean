import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LengthIndex.LenAtEqZero

noncomputable section

namespace PI.Dv.ProjAW

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {K : Type} [Field K] [NumberField K]

lemma ext_lat {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (g : L →ₗ[𝓞 K] K) :
    ∃ φ : V →ₗ[K] K, ∀ a : L, φ a = g a := by
  let S := nonZeroDivisors (𝓞 K)
  have hV : IsLocalizedModule S (LinearMap.id : V →ₗ[𝓞 K] V) := isLocalizedModule_id S V K
  have hK : IsLocalizedModule S (LinearMap.id : K →ₗ[𝓞 K] K) := isLocalizedModule_id S K K
  haveI : IsLocalizedModule S L.subtype :=
    { map_units := fun x => hV.map_units x
      surj := by
        intro y
        have hy : y ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
        induction hy using Submodule.span_induction with
        | mem x hx => exact ⟨(⟨x, hx⟩, 1), by simp⟩
        | zero => exact ⟨(0, 1), by simp⟩
        | add x y _ _ hx hy =>
          obtain ⟨⟨a, s⟩, ha⟩ := hx
          obtain ⟨⟨b, t⟩, hb⟩ := hy
          refine ⟨(t • a + s • b, s * t), ?_⟩
          simp only [Submonoid.smul_def, Submonoid.coe_mul, Submodule.subtype_apply,
            Submodule.coe_add, Submodule.coe_smul] at ha hb ⊢
          rw [← ha, ← hb]
          module
        | smul c x _ hx =>
          obtain ⟨⟨a, s⟩, ha⟩ := hx
          obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj S c
          have key : (q : 𝓞 K) • (c • x) = p • x := by
            rw [← algebraMap_smul K (q : 𝓞 K) (c • x), smul_smul, mul_comm]
            simp only at hpq
            rw [hpq, algebraMap_smul]
          refine ⟨(p • a, q * s), ?_⟩
          simp only [Submonoid.smul_def, Submonoid.coe_mul, Submodule.subtype_apply,
            Submodule.coe_smul] at ha ⊢
          rw [mul_comm, mul_smul, key, smul_comm, ha]
      exists_of_eq := fun {x₁ x₂} h => ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩ }
  refine ⟨(IsLocalizedModule.lift S L.subtype g (fun x => hK.map_units x)).extendScalarsOfIsLocalization
    S K, fun a => ?_⟩
  rw [LinearMap.extendScalarsOfIsLocalization_apply']
  exact IsLocalizedModule.lift_apply S L.subtype g _ a

variable [StarRing K] (A : HLat K)

lemma mem_dualLat {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (M : Submodule (𝓞 K) V) (f : Module.Dual K V) :
    f ∈ Formalism.HN.dualLat M ↔ ∀ x ∈ M, f x ∈ Set.range (algebraMap (𝓞 K) K) := Iff.rfl

lemma dual_part (hG : A.Good) {e : Module.End K A.V} (he : e * e = e) {n : ℕ} (hn0 : 0 < n)
    (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • e x ∈ A.L) (ψ : Module.Dual K A.V) (hψ : ψ ∘ₗ e = ψ) :
    ψ ∈ Formalism.HN.dualLat (cutE A e A.L) ↔ ∃ φ ∈ A.dualL, ψ = φ ∘ₗ e := by
  constructor
  · intro h
    rw [mem_dualLat] at h
    let Q := imgE A (1 - e) A.L
    haveI : Module.IsTorsionFree (𝓞 K) A.V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K A.V
    haveI : Module.IsTorsionFree (𝓞 K) Q :=
      Function.Injective.moduleIsTorsionFree (Q.subtype) Subtype.val_injective (fun _ _ => rfl)
    haveI : Module.Finite (𝓞 K) Q := Module.Finite.iff_fg.mpr (fg_img A hG (1 - e))
    haveI : Module.FinitePresentation (𝓞 K) Q := Module.finitePresentation_of_finite _ _
    haveI : Module.Projective (𝓞 K) Q := Module.Flat.projective_of_finitePresentation
    let g : A.L →ₗ[𝓞 K] Q := ((1 - e).restrictScalars (𝓞 K)).submoduleMap A.L
    obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id
      (LinearMap.submoduleMap_surjective _ _)
    have hgs : ∀ q : Q, (1 - e) (s q : A.V) = q := fun q => by
      have h1 := LinearMap.congr_fun hs q
      have h2 := congrArg Subtype.val h1
      exact h2
    let r : A.L →ₗ[𝓞 K] A.V := A.L.subtype - A.L.subtype ∘ₗ s ∘ₗ g
    have hr_apply : ∀ a : A.L, r a = (a : A.V) - (s (g a) : A.V) := fun a => rfl
    have hr : ∀ a : A.L, r a ∈ cutE A e A.L := by
      intro a
      refine (mem_cutE A e A.L _).2 ⟨?_, ?_⟩
      · rw [hr_apply]; exact A.L.sub_mem a.2 (s (g a)).2
      · refine ⟨r a, ?_⟩
        have h0 : (1 - e) (r a) = 0 := by
          rw [hr_apply, map_sub, hgs]
          change (1 - e) (a : A.V) - (1 - e) (a : A.V) = 0
          exact sub_self _
        have h3 : e (r a) = r a - (1 - e) (r a) := by simp
        rw [h3, h0, sub_zero]
    obtain ⟨φ, hφ⟩ := ext_lat A.L hG.2.2 ((ψ.restrictScalars (𝓞 K)) ∘ₗ r)
    have hagree : ∀ y ∈ cutE A e A.L, φ y = ψ y := by
      intro y hy
      have hy' := (mem_cutE A e A.L y).1 hy
      have hg0 : g ⟨y, hy'.1⟩ = 0 := by
        apply Subtype.ext
        change (1 - e) y = 0
        rw [LinearMap.sub_apply, Module.End.one_apply, idem_of A he hy'.2, sub_self]
      have hry : r ⟨y, hy'.1⟩ = y := by
        rw [hr_apply, hg0, map_zero]; simp
      rw [hφ ⟨y, hy'.1⟩, LinearMap.comp_apply, hry]
      rfl
    refine ⟨φ, ?_, ?_⟩
    · intro a ha
      rw [hφ ⟨a, ha⟩]
      exact h _ (hr _)
    · have hnK : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn0.ne'
      have hcomp : φ ∘ₗ e = ψ ∘ₗ e := by
        refine LinearMap.ext_on hG.2.2 ?_
        intro a ha
        have hmem : ((n : ℕ) : 𝓞 K) • e a ∈ cutE A e A.L :=
          part1 A hn (e a) ((mem_imgE A e A.L _).2 ⟨a, ha, rfl⟩)
        have h1 := hagree _ hmem
        rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
          Nat.cast_smul_eq_nsmul (𝓞 K), Nat.cast_smul_eq_nsmul (𝓞 K),
          ← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K, smul_eq_mul, smul_eq_mul] at h1
        simp only [LinearMap.comp_apply]
        exact mul_left_cancel₀ hnK h1
      refine LinearMap.ext fun x => ?_
      have h1 : ψ (e x) = ψ x := LinearMap.congr_fun hψ x
      have h2 : φ (e x) = ψ (e x) := LinearMap.congr_fun hcomp x
      simp only [LinearMap.comp_apply]
      rw [h2, h1]
  · rintro ⟨φ, hφ, rfl⟩
    rw [mem_dualLat]
    intro m hm
    obtain ⟨hmL, hmr⟩ := (mem_cutE A e A.L m).1 hm
    simp only [LinearMap.comp_apply]
    rw [idem_of A he hmr]
    exact hφ m hmL

end PI.Dv.ProjAW
