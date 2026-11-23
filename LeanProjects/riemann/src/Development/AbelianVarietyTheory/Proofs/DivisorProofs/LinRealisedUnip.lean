import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.MixedModel

variable {F : Type} [Field F] [NumberField F]

def LinRealised (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ),
    (∀ φ ∈ schA F κ, S φ ∈ schA F κ) ∧ (∀ φ ∈ schA F κ, ∃ φ' ∈ schA F κ, S φ' = φ) ∧
    (∀ l ∈ (adeleClass F).adm κ, ∃ l' ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ, l' φ = l (S φ)) ∧
    ∀ w, ∀ φ ∈ schA F κ, S (schr ψ w φ) = schr ψ (act g w) (S φ)

theorem linRealised_one (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    LinRealised ψ (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  ⟨LinearMap.id, fun φ h => h, fun φ h => ⟨φ, h, rfl⟩, fun l hl => ⟨l, hl, fun _ _ => rfl⟩,
    fun w φ _ => by rw [act_one]; rfl⟩

theorem LinRealised.mul {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ] {g h : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    (hg : LinRealised ψ g) (hh : LinRealised ψ h) : LinRealised ψ (g * h) := by
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := hg
  obtain ⟨T, hT, hTs, hTa, hTi⟩ := hh
  refine ⟨S ∘ₗ T, fun φ hφ => hS _ (hT φ hφ), fun φ hφ => ?_, fun l hl => ?_, fun w φ hφ => ?_⟩
  · obtain ⟨φ₁, h₁, rfl⟩ := hSs φ hφ
    obtain ⟨φ₂, h₂, rfl⟩ := hTs φ₁ h₁
    exact ⟨φ₂, h₂, rfl⟩
  · obtain ⟨l₁, hl₁, e₁⟩ := hSa l hl
    obtain ⟨l₂, hl₂, e₂⟩ := hTa l₁ hl₁
    exact ⟨l₂, hl₂, fun φ hφ => (e₂ φ hφ).trans (e₁ _ (hT φ hφ))⟩
  · simp only [LinearMap.comp_apply]
    rw [hTi w φ hφ, hSi _ _ (hT φ hφ), act_mul]

open scoped Classical in
open GlobalTheory.AdelicSvNLevi in
theorem linRealised_levi (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F)
    (hA : IsUnit A.det) : LinRealised ψ (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ) := by
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  let Am : Matrix κ κ (AdeleRing (𝓞 F) F) := A.map (algebraMap F (AdeleRing (𝓞 F) F))
  let Aim : Matrix κ κ (AdeleRing (𝓞 F) F) := A⁻¹.map (algebraMap F (AdeleRing (𝓞 F) F))
  have e1 : Am * Aim = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : Aim * Am = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨compM A⁻¹, comp_mem A⁻¹ A h2 h1, fun φ hφ => ⟨compM A φ, comp_mem A A⁻¹ h1 h2 φ hφ, ?_⟩,
    fun l hl => ⟨l ∘ₗ compM A⁻¹, fun g hg => ?_, fun _ _ => rfl⟩, fun w φ _ => funext fun x => ?_⟩
  · funext x
    change φ (Am *ᵥ (Aim *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A⁻¹ A h2 h1).continuous,
      hg.2.comp_homeomorph (finHomeo A⁻¹ A h2 h1)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A⁻¹ A h2 h1)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A⁻¹ A h2 h1, hT]
    rfl
  · rw [act_levi, Matrix.transpose_map]
    change ψ ((Aim *ᵥ x) ⬝ᵥ w.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)) * φ (Aim *ᵥ x + w.1) =
      ψ (x ⬝ᵥ (Aimᵀ *ᵥ w.2) + ⅟(2 : AdeleRing (𝓞 F) F) * ((Am *ᵥ w.1) ⬝ᵥ (Aimᵀ *ᵥ w.2))) *
        φ (Aim *ᵥ (x + Am *ᵥ w.1))
    rw [dot_transpose, dot_transpose, Matrix.mulVec_add, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]

open GlobalTheory.AdelicSvNQuad in
theorem linRealised_unip (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    (C : Matrix κ κ F) (hC : Cᵀ = C) : LinRealised ψ (Matrix.fromBlocks 1 0 (-C) 1) := by
  let A : Matrix κ κ (AF F) := C.map (algebraMap F (AF F))
  have hA : Aᵀ = A := by rw [← Matrix.transpose_map, hC]
  refine ⟨mulQ ψ (⅟2) A, mulQ_mem ψ hψ _ A, fun φ hφ => ⟨mulQ ψ (⅟2) (-A) φ, mulQ_mem ψ hψ _ _ φ hφ, ?_⟩,
    fun l hl => ⟨l ∘ₗ mulQ ψ (⅟2) A, fun g hg => ?_, fun _ _ => rfl⟩, fun w φ _ => funext fun x => ?_⟩
  · funext x
    rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, add_neg_cancel,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨g', hg', M, hM⟩ := mulQ_pureA ψ hψ (⅟2) A hg
    obtain ⟨T, hT⟩ := hl g' hg'
    exact ⟨T.comp M, fun f => (congrArg l (hM f)).trans (hT (M f))⟩
  · rw [act_unip, mulQ_apply]
    simp only [schr]
    rw [mulQ_apply, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_add A hA]

open GlobalTheory.AdelicSvN.Weyl MeasureTheory GroundTheory.Global GroundTheory.Automorphic.GJMatrix in
theorem linRealised_weyl (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    LinRealised ψ (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) := by
  have hk : ∀ φ ∈ schA F κ, adelicFourierPi F φ ∈ schA F κ := fun φ hφ => by
    rw [schA_eq] at hφ ⊢
    exact adelicFourierPi_mem_schwartzBruhatPi hφ
  have hinv : ∀ φ ∈ schA F κ, adelicFourierPi F (adelicFourierPi F φ) = fun x => φ (-x) := fun φ hφ => by
    rw [schA_eq] at hφ
    exact adelicFourierPi_adelicFourierPi hφ
  obtain ⟨T, hT⟩ := LinearMap.exists_extend (fourierLin (F := F) (κ := κ))
  have hT' : ∀ φ ∈ schA F κ, T φ = adelicFourierPi F φ := fun φ hφ => LinearMap.congr_fun hT ⟨φ, hφ⟩
  refine ⟨T, fun φ hφ => by rw [hT' φ hφ]; exact hk φ hφ, fun φ hφ => ⟨_, hk _ (hk _ (hk _ hφ)), ?_⟩,
    fun l hl => ?_, fun w φ hφ => ?_⟩
  · rw [hT' _ (hk _ (hk _ (hk _ hφ))), hinv _ (hk _ (hk _ hφ)), hinv _ hφ]
    simp only [neg_neg]
  · refine ⟨l ∘ₗ T, fun g hg => ?_, fun φ hφ => rfl⟩
    obtain ⟨U, hU⟩ := hl (finiteFourierPi F g) ((mem_SB_iff _).2 (finiteFourierPi_mem ((mem_SB_iff g).1 hg)))
    refine ⟨U.comp (mixedFourierPiSchwartz F), fun f => ?_⟩
    rw [LinearMap.comp_apply, hT' _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), ContinuousLinearMap.comp_apply, ← hU,
      pureA_eq, pureA_eq, adelicFourierPi_schwartzBruhatTensorPi]
  · rw [hT' _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ w φ hφ), hT' φ hφ, act_weyl, fourier_schr hψ]

theorem lin_realised : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F), g ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) →
  ∃ S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ),
    (∀ φ ∈ schA F κ, S φ ∈ schA F κ) ∧ (∀ φ ∈ schA F κ, ∃ φ' ∈ schA F κ, S φ' = φ) ∧
    (∀ l ∈ (adeleClass F).adm κ, ∃ l' ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ, l' φ = l (S φ)) ∧
    ∀ w, ∀ φ ∈ schA F κ, S (schr ψ w φ) = schr ψ (GlobalTheory.AdelicSvN.act g w) (S φ) := by
  intro F _ _ ψ hψ κ _ _ g hg
  suffices h : LinRealised ψ g from h
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    rcases hg with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | rfl
    · exact linRealised_levi ψ A hA
    · exact linRealised_unip ψ hψ C hC
    · exact linRealised_weyl ψ hψ
  | one => exact linRealised_one ψ
  | mul g h _ _ hg hh => exact hg.mul hh

end GlobalTheory.MixedModel
