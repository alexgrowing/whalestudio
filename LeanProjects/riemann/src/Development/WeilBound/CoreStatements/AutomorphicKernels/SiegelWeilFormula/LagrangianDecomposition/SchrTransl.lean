import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzPointValuesAdmittedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTensorLeftFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F : Type} [Field F] [NumberField F]

theorem schr_char {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] (ψ : AddChar (AF F) ℂ) (v : κ'' → AF F)
    (Ψ : (κ' ⊕ κ'' → AF F) → ℂ) :
    schr ψ ((0 : κ' ⊕ κ'' → AF F), Sum.elim (0 : κ' → AF F) v) Ψ = fun z => ψ ((z ∘ Sum.inr) ⬝ᵥ v) * Ψ z := by
  funext z
  have hz : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := (Sum.elim_comp_inl_inr z).symm
  simp only [schr, zero_dotProduct, mul_zero, add_zero]
  congr 2
  conv_lhs => rw [hz]
  rw [sumElim_dotProduct_sumElim]
  simp

theorem schr_transl {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (u : κ → AF F) (φ : (κ → AF F) → ℂ) (z : κ → AF F) :
    schr ψ (u, 0) φ z = φ (z + u) := by
  simp [schr]

theorem box_transl {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] (ψ : AddChar (AF F) ℂ) (u : κ'' → AF F)
    (φ' : (κ' → AF F) → ℂ) (φ'' : (κ'' → AF F) → ℂ) :
    boxFun φ' (schr ψ (u, 0) φ'') = schr ψ (Sum.elim (0 : κ' → AF F) u, 0) (boxFun φ' φ'') := by
  funext x
  rw [schr_transl]
  simp only [boxFun]
  rw [schr_transl]
  congr 2
  funext i
  simp

theorem opBox_of (hP : PartCharInv) (hS : SliceFacts) : OpBox := by
  intro F _ _ ψ hψ κ' κ'' _ _ W _ _ B dd G _ act om hsp hw x hfix φ₀ hφ₀ h0
  have hcomm : ∀ w : W, (dd.e w).1 ∘ Sum.inl = 0 → (dd.e w).2 ∘ Sum.inl = 0 →
      ∀ Φ ∈ schA F (κ' ⊕ κ''), om x (schr ψ (dd.e w) Φ) = schr ψ (dd.e w) (om x Φ) := by
    intro w h1 h2 Φ hΦ
    have := hsp.impl x w Φ hΦ
    simpa only [Darboux.rho, hfix w h1 h2] using this
  have hvan : ∀ Δ ∈ schA F (κ' ⊕ κ''), (∀ a : κ' → AF F, Δ (a ⊕ᵥ 0) = 0) →
      ∀ a : κ' → AF F, om x Δ (a ⊕ᵥ 0) = 0 := by
    intro Δ hΔ hz a
    have hl := hsp.adm x _ ((GlobalTheory.T.adelicSchwartz_pointValues_admitted F ψ hψ (κ' ⊕ κ'')).1 (a ⊕ᵥ 0))
    have key := hP F ψ hψ κ' κ'' _ hl ?_ Δ hΔ hz
    · simpa using key
    · intro y Ψ hΨ
      obtain ⟨w, hw'⟩ := hw 0 y
      have e0 : ((0 : κ' → AF F) ⊕ᵥ (0 : κ'' → AF F)) = 0 := Sum.elim_zero_zero
      have hw0 : dd.e w = ((0 : κ' ⊕ κ'' → AF F), Sum.elim (0 : κ' → AF F) y) := by
        rw [hw', e0]
      have hrho : (fun z : κ' ⊕ κ'' → AF F => ψ ((z ∘ Sum.inr) ⬝ᵥ y) * Ψ z) = schr ψ (dd.e w) Ψ := by
        rw [hw0, schr_char]
      have h1 : (dd.e w).1 ∘ Sum.inl = 0 := by rw [hw0]; rfl
      have h2 : (dd.e w).2 ∘ Sum.inl = 0 := by rw [hw0]; rfl
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply]
      rw [hrho, hcomm w h1 h2 Ψ hΨ, hw0, schr_char]
      simp
  refine ⟨?_, ?_⟩
  · intro Ψ hΨ
    have hs : slice0 κ' κ'' Ψ ∈ schA F κ' := (hS F κ' κ'').1 Ψ hΨ
    have hB := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ' κ'' _ hs φ₀ hφ₀
    have hD := hvan (Ψ - boxFun (slice0 κ' κ'' Ψ) φ₀) (Submodule.sub_mem _ hΨ hB) (by
      intro a
      simp [slice0, boxFun, h0])
    funext a
    have := hD a
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at this
    simpa [slice0] using this
  · intro φ' hφ' φ'' hφ''
    funext z
    obtain ⟨w, hw'⟩ := hw (z ∘ Sum.inr) 0
    have e0 : ((0 : κ' → AF F) ⊕ᵥ (0 : κ'' → AF F)) = 0 := Sum.elim_zero_zero
    have hw0 : dd.e w = (Sum.elim (0 : κ' → AF F) (z ∘ Sum.inr), (0 : κ' ⊕ κ'' → AF F)) := by
      rw [hw', e0]
    have h1 : (dd.e w).1 ∘ Sum.inl = 0 := by rw [hw0]; rfl
    have h2 : (dd.e w).2 ∘ Sum.inl = 0 := by rw [hw0]; rfl
    have hzs : z = (z ∘ Sum.inl ⊕ᵥ 0) + Sum.elim (0 : κ' → AF F) (z ∘ Sum.inr) := by
      funext i
      cases i <;> simp
    have hbox := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ' κ'' _ hφ' φ'' hφ''
    set η := schr ψ (z ∘ Sum.inr, 0) φ'' with hη
    have hηm : η ∈ schA F κ'' := (GlobalTheory.T.adelicSchwartz_pointValues_admitted F ψ hψ κ'').2.2.1 _ φ'' hφ''
    have hη0 : η 0 = φ'' (z ∘ Sum.inr) := by
      rw [hη, schr_transl, zero_add]
    have hL : om x (boxFun φ' φ'') z = om x (boxFun φ' η) (z ∘ Sum.inl ⊕ᵥ 0) := by
      rw [hη, box_transl, ← hw0, hcomm w h1 h2 _ hbox, hw0, schr_transl, ← hzs]
    have hB1 := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ' κ'' _ hφ' η hηm
    have hB2 := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ' κ'' _ hφ' φ₀ hφ₀
    have hD := hvan (boxFun φ' η - η 0 • boxFun φ' φ₀)
      (Submodule.sub_mem _ hB1 (Submodule.smul_mem _ _ hB2)) (by
        intro a
        simp [boxFun, h0]
        ring)
      (z ∘ Sum.inl)
    rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, sub_eq_zero, smul_eq_mul] at hD
    rw [hL, hD, hη0]
    simp [boxFun, slice0, mul_comm]

end PositivityTheory.SiegelWeilFormula.Ald

end
