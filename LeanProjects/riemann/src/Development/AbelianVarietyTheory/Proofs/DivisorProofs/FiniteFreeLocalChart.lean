import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox

noncomputable section
namespace GlobalTheory.SplitUnique
open GlobalTheory.WeilSchUnique

theorem splitting_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ), (∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) → JB.det ≠ 0 →
    ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
      (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (GlobalTheory.WeilM.dbl (incM F JB))) κ)
      (omd omd₁ : UG (cA σ) (GlobalTheory.WeilM.dbl (incM F JB)) →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → IsContOn (adeleClass F) omd →
    IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd₁ → IsContOn (adeleClass F) omd₁ →
    ∀ l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ, (∃ φ ∈ schA F κ, l φ ≠ 0) →
    (∀ (p : UG (cA σ) (GlobalTheory.WeilM.dbl (incM F JB))) (t : GL (Fin b) (AE F E)),
      (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * t.1 → ∀ φ ∈ schA F κ, l (omd p φ) = l (omd₁ p φ)) →
    ∀ p, ∀ φ ∈ schA F κ, omd p φ = omd₁ p φ := by
  intro F E _ _ _ _ _ σ hσ a b JA JB ε hJ hdet ψ hψ κ _ dd omd omd₁ hS hC hS₁ hC₁ l ⟨φ₀, hφ₀, hl0⟩ hl
  have inv_mul : ∀ (p : UG (cA σ) (GlobalTheory.WeilM.dbl (incM F JB))) φ, omd p (omd p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨φz, hφz, hφz0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ
  have key : ∀ p, ∃ c : ℂ, ∀ φ ∈ schA F κ, omd₁ p φ = c • omd p φ := fun p => by
    obtain ⟨c, hc⟩ := scalar_of_commute ψ hψ (omd p⁻¹ * omd₁ p)
      (fun l hl => by
        rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
        exact hS₁.adm p _ (hS.adm p⁻¹ l hl))
      (fun w φ hφ => by
        obtain ⟨w', rfl⟩ := dd.e.surjective w
        have e1 : schr ψ (dd.e w') = dd.rho ψ w' := rfl
        rw [e1, Module.End.mul_apply, Module.End.mul_apply]
        calc omd p⁻¹ (omd₁ p (dd.rho ψ w' φ))
            = omd p⁻¹ (dd.rho ψ (actB (cA σ) p w') (omd₁ p φ)) := by rw [hS₁.impl p w' φ hφ]
          _ = dd.rho ψ (actB (cA σ) p⁻¹ (actB (cA σ) p w')) (omd p⁻¹ (omd₁ p φ)) :=
              hS.impl _ _ _ (hS₁.pres p φ hφ)
          _ = _ := by rw [actB_inv_actB])
    refine ⟨c, fun φ hφ => ?_⟩
    have := congrArg (omd p) (hc φ hφ)
    rwa [Module.End.mul_apply, inv_mul, map_smul] at this
  choose cf hcf using key
  have hsp : ∀ p, ∀ φ ∈ schA F κ, omd p φ ∈ schA F κ := fun p φ hφ => hS.pres p φ hφ
  have huniq : ∀ p (c : ℂ), (∀ φ ∈ schA F κ, omd₁ p φ = c • omd p φ) → c = cf p := fun p c hc => by
    have h1 := hc _ (hsp p⁻¹ φz hφz)
    rw [hcf p _ (hsp p⁻¹ φz hφz), inv_mul] at h1
    have h2 := congrFun h1 0
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact (mul_right_cancel₀ hφz0 h2).symm
  have hmul : ∀ p q, cf (p * q) = cf p * cf q := fun p q => (huniq (p * q) _ fun φ hφ => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcf q φ hφ, map_smul,
      hcf p _ (hsp q φ hφ), smul_smul, mul_comm]).symm
  have hone : cf 1 = 1 := (huniq 1 1 fun φ _ => by simp).symm
  let cM : UG (cA σ) (GlobalTheory.WeilM.dbl (incM F JB)) →* ℂ := { toFun := cf, map_one' := hone, map_mul' := hmul }
  let c := cM.toHomUnits
  have hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cf p := fun p => rfl
  have hcont_cf : Continuous cf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hφ := hsp p₀⁻¹ φz hφz
    have hf := hC _ (evalZero_mem_adelicSchwartzAdmittedForms κ) _ hφ
    have hf₁ := hC₁ _ (evalZero_mem_adelicSchwartzAdmittedForms κ) _ hφ
    simp only [LinearMap.proj_apply] at hf hf₁
    have h0 : omd p₀ (omd p₀⁻¹ φz) 0 ≠ 0 := by rw [inv_mul]; exact hφz0
    refine (hf₁.continuousAt.div hf.continuousAt h0).congr ?_
    filter_upwards [hf.continuousAt.eventually_ne h0] with p hp
    show omd₁ p _ 0 / omd p _ 0 = cf p
    rw [hcf p _ hφ]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hcont : Continuous c := by
    refine Units.continuous_iff.2 ⟨hcont_cf, ?_⟩
    have : (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_cf.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero
  have hP : ∀ (p : UG (cA σ) (GlobalTheory.WeilM.dbl (incM F JB))) (t : GL (Fin b) (AE F E)),
      ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * t.1 →
        c p = 1 := fun p t hpt => by
    have hφ := hsp p⁻¹ φ₀ hφ₀
    have e1 := hl p t hpt _ hφ
    rw [hcf p _ hφ, inv_mul, map_smul, smul_eq_mul] at e1
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    exact mul_right_cancel₀ hl0 (by rw [one_mul]; exact e1.symm)
  have hc1 := GlobalTheory.SiegelChar.eq_one_of_siegel F E σ hσ b JB ε hJ hdet c hcont hP
  have hcf1 : ∀ p, cf p = 1 := fun p => by
    rw [← hcv, hc1]; rfl
  intro p φ hφ
  rw [hcf p φ hφ, hcf1 p, one_smul]

end GlobalTheory.SplitUnique
