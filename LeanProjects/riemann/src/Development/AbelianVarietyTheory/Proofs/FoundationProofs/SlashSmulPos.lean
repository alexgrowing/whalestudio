import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlSqSubMemOldformsGamma1Statement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlSemisimpleOnLOldSpaceStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.UlSemisimple

theorem toGL_det (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    (toGL g : Matrix (Fin 2) (Fin 2) ℝ).det = (g.det : ℝ) := by
  unfold toGL
  rw [dif_neg hg]
  simp only [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two]
  simp [Matrix.det_fin_two]

theorem slash_smul_pos (k : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det) (c : ℂ) (f : ℍ → ℂ) :
    (c • f) ∣[k] toGL g = c • (f ∣[k] toGL g) := by
  rw [ModularForm.smul_slash]
  congr 1
  simp only [UpperHalfPlane.σ]
  rw [if_pos (by rw [Matrix.GeneralLinearGroup.val_det_apply, toGL_det g hg.ne']; exact_mod_cast hg)]
  rfl

def ulLin (k : ℤ) (l : ℕ) (hl : 0 < l) : Module.End ℂ (ℍ → ℂ) where
  toFun := UlF k l
  map_add' f g := by simp only [UlF, hkF, SlashAction.add_slash, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [UlF, hkF, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => slash_smul_pos k _ ?_ c f
    simp [ulFam, Matrix.det_fin_two]
    exact_mod_cast hl

theorem ulLin_apply (k : ℤ) (l : ℕ) (hl : 0 < l) (F : ℍ → ℂ) : ulLin k l hl F = UlF k l F := rfl

def ChiLaw (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (F : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → F ∣[k] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • F

def oldSp (N l : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (hl : 0 < l) : Submodule ℂ (ℍ → ℂ) where
  carrier := {F | ∃ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) k, ChiLaw N k χ ⇑f₁ ∧ ChiLaw N k χ ⇑f₂ ∧
    F = ⇑f₁ + ⇑f₂ ∣[k] toGL (dg l 1)}
  add_mem' := by
    rintro F G ⟨f₁, f₂, h₁, h₂, rfl⟩ ⟨g₁, g₂, h₁', h₂', rfl⟩
    refine ⟨f₁ + g₁, f₂ + g₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
    · rw [CuspForm.coe_add, SlashAction.add_slash, h₁ γ hγ, h₁' γ hγ, smul_add]
    · rw [CuspForm.coe_add, SlashAction.add_slash, h₂ γ hγ, h₂' γ hγ, smul_add]
    · rw [CuspForm.coe_add, CuspForm.coe_add, SlashAction.add_slash]; abel
  zero_mem' := ⟨0, 0, fun γ _ => by simp, fun γ _ => by simp, by simp⟩
  smul_mem' := by
    rintro c F ⟨f₁, f₂, h₁, h₂, rfl⟩
    have hd : 0 < (dg (l : ℤ) 1).det := by simp [dg, Matrix.det_fin_two]; exact_mod_cast hl
    refine ⟨c • f₁, c • f₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
    · rw [CuspForm.coe_smul, ModularForm.SL_smul_slash, h₁ γ hγ, smul_comm]
    · rw [CuspForm.coe_smul, ModularForm.SL_smul_slash, h₂ γ hγ, smul_comm]
    · rw [CuspForm.coe_smul, CuspForm.coe_smul, slash_smul_pos k _ hd, smul_add]

theorem aeval_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (U : Module.End ℂ M) (O : Submodule ℂ M)
    (hU : ∀ x ∈ O, U x ∈ O) (p : ℂ[X]) (x : M) (hx : x ∈ O) : aeval U p x ∈ O := by
  have hpow : ∀ m : ℕ, ∀ y ∈ O, (U ^ m) y ∈ O := by
    intro m
    induction m with
    | zero => intro y hy; simpa using hy
    | succ m ih => intro y hy; rw [pow_succ', Module.End.mul_apply]; exact hU _ (ih y hy)
  rw [aeval_eq_sum_range, LinearMap.sum_apply]
  exact O.sum_mem fun i _ => by rw [LinearMap.smul_apply]; exact O.smul_mem _ (hpow i x hx)

end GlobalTheory.HeckeFamilyMatrices.UlSemisimple

open GlobalTheory.HeckeFamilyMatrices.UlSemisimple in

theorem GlobalTheory.HeckeFamilyMatrices.ul_semisimple : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (α : ℂ), α ^ 2 ≠ χ l * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ χ l * (l : ℂ) ^ (k - 2) →
  ∀ f : CuspForm (Lev N l) (k : ℤ), (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 (N * l) → ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f) →
  ∀ n : ℕ, (fun F => UlF (k : ℤ) l F - α • F)^[n] ⇑f = 0 → UlF (k : ℤ) l ⇑f = α • ⇑f := by
  intro N l k hN hl hlN hk χ α hα1 hα2 f hf n hn
  have hl0 : 0 < l := hl.pos
  set U := ulLin (k : ℤ) l hl0 with hUdef
  set O := oldSp N l (k : ℤ) χ hl0 with hOdef
  have hUO : ∀ F ∈ O, U F ∈ O := by
    rintro F ⟨f₁, f₂, h₁, h₂, rfl⟩
    obtain ⟨g₁, g₂, hg₁, hg₂, he⟩ := (GlobalTheory.T.heckeUl_semisimple_on_lOldSpace N l k hN hl hlN hk χ α hα1 f₁ f₂ h₁ h₂).1
    exact ⟨g₁, g₂, hg₁, hg₂, he⟩
  set c : ℂ := χ l * (l : ℂ) ^ (k - 2) with hc
  have hcop : IsCoprime ((X - C α) ^ n) (X ^ 2 - C c) := by
    apply IsCoprime.pow_left
    rw [(irreducible_X_sub_C α).coprime_iff_not_dvd, dvd_iff_isRoot, IsRoot.def]
    simpa [sub_eq_zero] using hα2
  obtain ⟨A, B, hAB⟩ := hcop
  have key : aeval U A (aeval U ((X - C α) ^ n) ⇑f) + aeval U B (aeval U (X ^ 2 - C c) ⇑f) = ⇑f := by
    have := congrArg (fun p => aeval U p ⇑f) hAB
    simpa only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.one_apply] using this
  have h1 : aeval U ((X - C α) ^ n) ⇑f = 0 := by
    rw [map_pow, map_sub, aeval_X, aeval_C, Module.End.pow_apply]
    convert hn using 2
    funext F
    simp [hUdef, ulLin_apply, Module.algebraMap_end_apply]
  have h2 : aeval U (X ^ 2 - C c) ⇑f ∈ O := by
    obtain ⟨f₁, f₂, h₁, h₂, he⟩ := GlobalTheory.T.hecke_Ul_sq_sub_mem_oldforms_Gamma1 N l k hN hl hlN hk χ f hf
    refine ⟨f₁, f₂, h₁, h₂, ?_⟩
    rw [← he, map_sub, aeval_C, map_pow, aeval_X, LinearMap.sub_apply, Module.algebraMap_end_apply,
      pow_two, Module.End.mul_apply]
    rfl
  have hfO : ⇑f ∈ O := by
    rw [← key, h1, map_zero, zero_add]
    exact aeval_mem U O hUO B _ h2
  obtain ⟨f₁, f₂, h₁, h₂, he⟩ := hfO
  have hss := (GlobalTheory.T.heckeUl_semisimple_on_lOldSpace N l k hN hl hlN hk χ α hα1 f₁ f₂ h₁ h₂).2 n
  rw [he] at hn ⊢
  exact hss hn

end
