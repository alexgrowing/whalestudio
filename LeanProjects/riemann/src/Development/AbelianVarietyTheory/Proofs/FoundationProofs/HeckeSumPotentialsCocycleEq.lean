import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DehomogeniseBinaryPolyHomogeneousEquivSlashStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.DictHk

theorem mat_mul {Γ : Subgroup SL(2, ℤ)} (a b : Γ) :
    GlobalTheory.HeckeFamilyMatrices.mat ((a * b : Γ) : SL(2, ℤ)) = GlobalTheory.HeckeFamilyMatrices.mat a * GlobalTheory.HeckeFamilyMatrices.mat b := rfl

theorem mat_mul_inv {Γ : Subgroup SL(2, ℤ)} (a : Γ) :
    GlobalTheory.HeckeFamilyMatrices.mat a * GlobalTheory.HeckeFamilyMatrices.mat ((a⁻¹ : Γ) : SL(2, ℤ)) = 1 := by
  rw [← mat_mul, mul_inv_cancel]; rfl

theorem mat_one {Γ : Subgroup SL(2, ℤ)} : GlobalTheory.HeckeFamilyMatrices.mat ((1 : Γ) : SL(2, ℤ)) = 1 := rfl

theorem cancel_right {Γ : Subgroup SL(2, ℤ)} {A B : Matrix (Fin 2) (Fin 2) ℤ} (a : Γ)
    (h : A * GlobalTheory.HeckeFamilyMatrices.mat a = B * GlobalTheory.HeckeFamilyMatrices.mat a) : A = B := by
  have := congrArg (· * GlobalTheory.HeckeFamilyMatrices.mat ((a⁻¹ : Γ) : SL(2, ℤ))) h
  simpa only [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one] using this

theorem det_pos {Γ : Subgroup SL(2, ℤ)} {α : Matrix (Fin 2) (Fin 2) ℤ} {ι : Type}
    {δ : ι → Matrix (Fin 2) (Fin 2) ℤ} (hα : 0 < α.det) (hδ : GlobalTheory.HeckeFamilyMatrices.IsDCReps Γ α δ) (i : ι) :
    0 < (δ i).det := by
  obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
  rw [h, det_mul, det_mul]
  simpa using hα

theorem exists_perm {Γ : Subgroup SL(2, ℤ)} {α : Matrix (Fin 2) (Fin 2) ℤ} {ι : Type} [Fintype ι]
    {δ : ι → Matrix (Fin 2) (Fin 2) ℤ} (hδ : GlobalTheory.HeckeFamilyMatrices.IsDCReps Γ α δ) (γ : Γ) :
    ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat γ' * δ (π i) := by
  classical
  have hf : ∀ i, ∃ j, ∃ γ' : Γ, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat γ' * δ j := by
    intro i
    obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
    obtain ⟨j, ⟨γ', h'⟩, -⟩ := hδ.2 γ₁ (γ₂ * γ)
    refine ⟨j, γ', ?_⟩
    rw [h, ← h', mat_mul, Matrix.mul_assoc]
  choose f g hfg using hf
  have hinj : Function.Injective f := by
    intro i i' hii
    obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
    obtain ⟨k, -, hk⟩ := hδ.2 γ₁ γ₂
    have e1 : i = k := hk i ⟨1, by rw [mat_one, Matrix.one_mul, h]⟩
    have e2 : i' = k := by
      refine hk i' ⟨g i * (g i')⁻¹, ?_⟩
      rw [← h]
      apply cancel_right γ
      rw [hfg i, Matrix.mul_assoc, hfg i', ← hii, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel_right]
    rw [e1, e2]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => ⟨g i, hfg i⟩⟩

theorem incr {N l w : ℕ} {ι : Type} [Fintype ι] {δ : ι → Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : ∀ i, 0 < (δ i).det) {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w (Gam N l))
    (γ : GlobalTheory.HeckeFamilyMatrices.Lev N l) (π : Equiv.Perm ι) (g : ι → GlobalTheory.HeckeFamilyMatrices.Lev N l)
    (hg : ∀ i, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i)) (z : ℂ) (hz : z ∈ Hs) :
    slP (GlobalTheory.HeckeFamilyMatrices.mat γ) ((∑ i, opP ℂ (δ i) F) (mob (ofSL γ) z)) - (∑ i, opP ℂ (δ i) F) z =
      ∑ i, slP (δ (π i)) (slP (GlobalTheory.HeckeFamilyMatrices.mat (g i)) (F (mob (ofSL (g i)) Complex.I)) - F Complex.I) := by
  obtain ⟨hmem, hmul, -, -, hSL, htoGQ⟩ := GlobalTheory.KZ.mob_laws
  obtain ⟨hslmul, -⟩ := GlobalTheory.KZ.polySlash_laws ℂ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have h1 : ∀ a : GlobalTheory.HeckeFamilyMatrices.Lev N l, 0 < (GlobalTheory.HeckeFamilyMatrices.mat a).det := fun a => by simp
  simp only [Finset.sum_apply, map_sum]
  rw [← Equiv.sum_comp π (fun i => opP ℂ (δ i) F z), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨p, hp⟩ := hF.2 (g i) (g i).2
  have hz' := hmem (toGQ (δ (π i))) z hz
  rw [hp _ hI, ← hp _ hz']
  simp only [opP, LinearMap.coe_mk, AddHom.coe_mk, map_sub]
  rw [sub_left_inj]
  have hL : mob (toGQ (δ i)) (mob (ofSL γ) z) = mob (toGQ (δ i * GlobalTheory.HeckeFamilyMatrices.mat γ)) z := by
    rw [htoGQ _ _ (hdet i) (h1 γ), hSL, hmul _ _ _ hz]
  have hR : mob (ofSL (g i)) (mob (toGQ (δ (π i))) z) =
      mob (toGQ (GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i))) z := by
    rw [htoGQ _ _ (h1 (g i)) (hdet (π i)), hSL, hmul _ _ _ hz]
  have hs1 := hslmul (δ i) (GlobalTheory.HeckeFamilyMatrices.mat γ) (F (mob (toGQ (δ i * GlobalTheory.HeckeFamilyMatrices.mat γ)) z))
  have hs2 := hslmul (GlobalTheory.HeckeFamilyMatrices.mat (g i)) (δ (π i)) (F (mob (toGQ (GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i))) z))
  rw [hL, hR, ← hs1, ← hs2, hg i]

theorem dict_hk : ∀ (N l w : ℕ) (α : Matrix (Fin 2) (Fin 2) ℤ) (ι : Type) [Fintype ι]
    (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < N → 0 < l → 0 < α.det →
    GlobalTheory.HeckeFamilyMatrices.IsDCReps (GlobalTheory.HeckeFamilyMatrices.Lev N l) α δ → ∀ F ∈ Pot ℂ w (Gam N l),
    (∑ i, opP ℂ (δ i) F) ∈ Pot ℂ w (Gam N l) ∧
      cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (∑ i, opP ℂ (δ i) F) =
        GlobalTheory.HeckeFamilyMatrices.hk (GlobalTheory.HeckeFamilyMatrices.Lev N l) w δ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  intro N l w α ι _ δ _ _ hα hδ F hF
  have hdet := det_pos hα hδ
  obtain ⟨-, -, hslhom, -⟩ := GlobalTheory.KZ.polySlash_laws ℂ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  refine ⟨⟨fun z => ?_, fun γ hγ => ?_⟩, ?_⟩
  · simp only [Finset.sum_apply]
    exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => hslhom _ w _ (hF.1 _)
  · obtain ⟨π, hπ⟩ := exists_perm hδ (⟨γ, hγ⟩ : GlobalTheory.HeckeFamilyMatrices.Lev N l)
    choose g hg using hπ
    exact ⟨_, fun z hz => incr hdet hF ⟨γ, hγ⟩ π g hg z hz⟩
  · funext γ
    have hex := exists_perm hδ γ
    simp only [GlobalTheory.HeckeFamilyMatrices.hk, LinearMap.pi_apply, dif_pos hex, LinearMap.sum_apply, Finset.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
    rw [cocP, incr hdet hF γ hex.choose (fun i => (hex.choose_spec i).choose)
      (fun i => (hex.choose_spec i).choose_spec) _ hI, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(GlobalTheory.T.dehomogeniseBinaryPoly_homogeneous_equiv_slash w).1 _ _ ((hslhom _ w _ (hF.1 _)).sub (hF.1 _))]
    rfl

end GlobalTheory.KZ.DictHk
