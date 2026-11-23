import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankInvariantFormTransportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankFormLinearExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankInSpanSmallFProductsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallFConjProductMemFullRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInvariantFunctionalDetPowerStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open GlobalTheory.SplitFlip

theorem GlobalTheory.FullRankCoinv.form_diag_right_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n < d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ Bf : GlobalTheory.FullRankCoinv.fullRk k n d →ₗ[ℂ] GlobalTheory.FullRankCoinv.fullRk k n d →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d), Ψ₁'.1 = GlobalTheory.FullRankCoinv.lact ν g Ψ₁.1 →
        Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.FullRankCoinv.fullRk k n d,
        Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) →
      (∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d,
        (∀ (Y₁ Y₂ : Matrix (Fin n) (Fin d) k), Ψ₁.1 Y₁ ≠ 0 → Ψ₂.1 Y₂ ≠ 0 → ∀ a : GL (Fin n) k, Y₁ ≠ a.1 * Y₂) →
        Bf Ψ₁ Ψ₂ = 0) →
      ∀ (g : GL (Fin n) k) (Ψ₁ Ψ₂ Ψ₂' : GlobalTheory.FullRankCoinv.fullRk k n d), Ψ₂'.1 = GlobalTheory.FullRankCoinv.lact ν g Ψ₂.1 →
        Bf Ψ₁ Ψ₂' = Bf Ψ₁ Ψ₂ := by
  intro k _ _ _ _ n d ν hnd hsm hun Bf hA hM hS g Ψ₁ Ψ₂ Ψ₂' hΨ
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  let F : (Matrix (Fin n) (Fin d) k → ℂ) → Matrix (Fin n) (Fin d) k → ℂ :=
    fun Ψ Y => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y
  have hlin : ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Ψ' ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ c : ℂ,
      F (c • Ψ + Ψ') = c • F Ψ + F Ψ' := by
    intro Ψ hΨ Ψ' hΨ' c
    funext Y
    have i1 := (GlobalTheory.FullRankCoinv.integrable_fibre n d ν hsm Ψ hΨ Y).const_mul c
    have i2 := GlobalTheory.FullRankCoinv.integrable_fibre n d ν hsm Ψ' hΨ' Y
    simp only [F, smallF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul, ← integral_add i1 i2]
    congr 1; funext x; ring
  have hloc := GlobalTheory.T.fullRank_invariant_form_transport k n d ν hnd.le hsm Bf hA hS
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.fullRank_form_linear_extension k n d F Bf hlin hloc
  have hrt : ∀ (h : GL (Fin d) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ), Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d →
      (fun Y => Ψ (Y * h.1)) ∈ GlobalTheory.FullRankCoinv.fullRk k n d := by
    intro h Ψ hΨ
    refine ⟨?_, fun Y hY => hΨ.2 _ ?_⟩
    · have h1 : (fun X => Ψ (X * h.1)) ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) := by
        simpa using comp_mul_mem_SB (1 : GL (Fin n) k) h hΨ.1
      exact h1
    · rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit)]
  have hΛM : ∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
      (m : ℂ) * Λ (fun Y => φ (Y * h.1)) = Λ φ := by
    intro h
    obtain ⟨m, hm, hmB⟩ := hM h
    refine ⟨m, hm, fun φ hφ => ?_⟩
    have hsp := GlobalTheory.T.fullRank_in_span_smallF_products k n d ν hnd.le hsm φ hφ
    clear hφ
    induction hsp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨A, hA', B, hB', rfl⟩ := hx
      have e1 := hmB ⟨A, hA'⟩ ⟨_, hrt h A hA'⟩ ⟨B, hB'⟩ ⟨_, hrt h B hB'⟩ rfl rfl
      rw [hΛ, hΛ] at e1
      rw [← e1]
      congr 2
      funext Y
      simp only [F, smallF, Matrix.mul_assoc]
    | zero =>
      show (m : ℂ) * Λ 0 = Λ 0
      simp
    | add x y _ _ hx hy =>
      change (m : ℂ) * Λ ((fun Y => x (Y * h.1)) + (fun Y => y (Y * h.1))) = Λ (x + y)
      rw [map_add, map_add, mul_add, hx, hy]
    | smul c x _ hx =>
      change (m : ℂ) * Λ (c • (fun Y => x (Y * h.1))) = Λ (c • x)
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm, hx]
  have hL := GlobalTheory.T.quasi_invariant_functional_det_power k n d hnd Λ hΛM
  have hprod := GlobalTheory.T.smallF_conj_product_mem_fullRank k n d ν hnd.le hsm Ψ₁.1 Ψ₁.2 Ψ₂.1 Ψ₂.2
  rw [hΛ, hΛ, hΨ, ← hL g _ hprod, ← smul_eq_mul, ← map_smul]
  congr 1
  funext Y
  have hF := smallF_mul_left (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁.1 (invT g⁻¹) Y
  have hv : (invT g⁻¹).val = (g.1)ᵀ := by rw [invT_val, inv_inv]
  have hdet : gdet (invT g⁻¹) = gdet g := by rw [gdet_invT, show gdet g⁻¹ = (gdet g)⁻¹ from map_inv _ _, inv_inv]
  rw [hv, hdet, Fintype.card_fin] at hF
  have hν1 : (ν (gdet g) : ℂ) * (starRingEnd ℂ) (ν (gdet g) : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hun]; simp
  have ha : (starRingEnd ℂ) (apow (gdet g) ((d : ℂ) / 2)) = apow (gdet g) ((d : ℂ) / 2) := by
    have h0 : (0 : ℝ) ≤ (GlobalTheory.SplitWeil.nabs k (gdet g) : ℝ) := NNReal.coe_nonneg _
    rw [apow, show ((d : ℂ) / 2) = (((d : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow h0,
      Complex.conj_ofReal]
  have haa : apow (gdet g) ((d : ℂ) / 2) * apow (gdet g) ((d : ℂ) / 2) = apow (gdet g) (d : ℂ) := by
    rw [← apow_add]; congr 1; ring
  simp only [F, GlobalTheory.FullRankCoinv.lact, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← hF, ha, ← haa]
  linear_combination (apow (gdet g) ((d : ℂ) / 2) * apow (gdet g) ((d : ℂ) / 2) *
    smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁.1 ((g.1)ᵀ * Y) * (starRingEnd ℂ) (Ψ₂.1 ((g.1)ᵀ * Y))) * hν1
