import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlLatCongMove

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FrameDepth

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem conj_mem_glLatCong {Λ Λ' : Submodule 𝒪[k] (D → k)} {u : kˣ} (G : GL D k)
    (hG : ∀ x, x ᵥ* G.val ∈ Λ' ↔ x ∈ Λ) {g : GL D k} (hg : g ∈ glLatCong u Λ') :
    G * g * G⁻¹ ∈ glLatCong u Λ := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [← hG, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← vecMul_vecMul, hg.1, hG]
  · have h1 := hg.2 _ ((hG x).2 hx)
    rw [mem_smul_lat] at h1 ⊢
    rw [← hG]
    convert h1 using 1
    rw [Units.smul_def, Units.smul_def, smul_vecMul, vecMul_vecMul, vecMul_vecMul, sub_mul, mul_sub,
      ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, mul_one, one_mul]

theorem vecMul_diagGL_mem (b c d : D → kˣ) (h : ∀ j, d j = b j * c j) (x : D → k) :
    x ᵥ* (diagGL c).val ∈ diagLat d ↔ x ∈ diagLat b := by
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (c j : k) := zero_lt_iff.2 (by simp)
  rw [diagGL_val, vecMul_diagonal, map_mul, h, Units.val_mul, map_mul]
  exact mul_le_mul_iff_left₀ h0

theorem mem_glLatCong_of_smul {Λ : Submodule 𝒪[k] (D → k)} {u v : kˣ} {g : GL D k}
    (hg : g ∈ glLatCong u (v • Λ)) : g ∈ glLatCong u Λ := by
  have hm : ∀ x, v • x ∈ v • Λ ↔ x ∈ Λ := fun x => by rw [mem_smul_lat, inv_smul_smul]
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [← hm, ← hm x, ← hg.1 (v • x), Units.smul_def v x, smul_vecMul, ← Units.smul_def v (x ᵥ* g.val)]
  · have h1 := hg.2 _ ((hm x).2 hx)
    rw [mem_smul_lat, mem_smul_lat] at h1
    rw [mem_smul_lat]
    convert h1 using 1
    rw [smul_comm v⁻¹, Units.smul_def v, smul_vecMul, ← Units.smul_def v, inv_smul_smul]

theorem invT_mem_of_dual {u : kˣ} {c : D → kˣ} {g : GL D k} (hg : g ∈ glLatCong u (dualLat (diagLat c))) :
    invT g ∈ glLatCong u (diagLat c) ∧ gdet (invT g) ∈ unitCong u := by
  rw [dualLat_diagLat] at hg
  have h1 := GlobalTheory.FunObj.GivenAdm.invT_mem_glLatCong (conj_mem_glLatCong (Λ := stdLat k D)
    (diagGL fun j => (c j)⁻¹) (vecMul_diagGL_mem 1 _ _ (by simp)) hg)
  have h2 : invT (diagGL fun j => (c j)⁻¹) = diagGL c := by
    rw [← _root_.inv_inj]
    refine Units.ext ?_
    rw [invT_inv_val, diagGL_val, diagonal_transpose]
    symm
    refine Units.inv_eq_of_mul_eq_one_right ?_
    simp [diagGL_val]
  rw [map_mul, map_mul, map_inv, h2] at h1
  constructor
  · have h3 := conj_mem_glLatCong (Λ := diagLat c) (diagGL c)⁻¹ (fun x => by
      rw [stdLat, ← vecMul_diagGL_mem 1 c c (by simp), vecMul_vecMul, Units.inv_mul, vecMul_one]) h1
    simpa [mul_assoc] using h3
  · have h3 := GlobalTheory.FunObj.GivenAdm.gdet_mem_unitCong h1
    rwa [gdet_mul, gdet_mul, show gdet (diagGL c)⁻¹ = (gdet (diagGL c))⁻¹ from map_inv _ _,
      mul_inv_cancel_comm] at h3

theorem HasDepth.mul_glLatCong {A : Type*} {ϖ : kˣ} {e : ℕ} {Λ : Submodule 𝒪[k] (D → k)}
    {Ψ : Matrix A D k → ℂ} (h : HasDepth ϖ e Λ Ψ) {g : GL D k} (hg : g ∈ glLatCong (ϖ ^ e) Λ)
    (Y : Matrix A D k) : Ψ (Y * g.val) = Ψ Y := by
  have hr : ∀ (M : Matrix D D k) i, (Y * M).row i = Y.row i ᵥ* M := fun M i => by
    funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]
  by_cases hY : Y ∈ matLat A Λ
  · rw [show Y * g.val = Y + Y * (g.val - 1) by rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]]
    exact h.2 _ _ fun i => by rw [hr]; exact hg.2 _ (hY i)
  · rw [h.1 _ hY, h.1 _ fun H => hY fun i => (hg.1 _).1 (by rw [← hr]; exact H i)]

theorem hasDepth_phiA (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype D] [DecidableEq D] (μ : Measure (GL A' k)) [hμ : μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ)
    (ϖ : kˣ) (e : ℕ) (c : D → kˣ) (Ψ : Matrix A' D k → ℂ) (hϖ : IsUnif ϖ) (he : 1 ≤ e) (hν : CondLE ϖ e ν)
    (hΨ : HasDepth ϖ e (diagLat c) Ψ) :
    HasDepth ϖ e (latA ϖ e (diagLat c)) (phiA μ σ ν ϖ e (diagLat c) Ψ) := by
  have hlt : valuation k ((ϖ ^ e : kˣ) : k) < 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_lt_one₀ zero_le' (hϖ ▸ uniformizer_lt_one) (by omega)
  have key : ∀ X Z : Matrix A D k, IsPrimFrame (latA ϖ e (diagLat c)) X →
      Z ∈ matLat A (ϖ ^ e • latA ϖ e (diagLat c)) → ∃ κ ∈ glLatCong (ϖ ^ e) (latA ϖ e (diagLat c)),
        X + Z = X * κ.val := by
    rw [latA, dualLat_diagLat, smul_diagLat]
    exact GlobalTheory.PrimFrameMove.exists_glLatCong_move k A D _ _ hlt
  have prim : ∀ X Z : Matrix A D k, IsPrimFrame (latA ϖ e (diagLat c)) X →
      Z ∈ matLat A (ϖ ^ e • latA ϖ e (diagLat c)) → IsPrimFrame (latA ϖ e (diagLat c)) (X + Z) := by
    intro X Z hX hZ
    obtain ⟨κ, hκ, h⟩ := key X Z hX hZ
    rw [h]
    exact GlobalTheory.SplitFlip.Model.isPrimFrame_mul hX κ hκ.1
  refine ⟨fun X hX => if_neg fun h => hX h.2.1, fun X Z hZ => ?_⟩
  by_cases hX : IsPrimFrame (latA ϖ e (diagLat c)) X
  · unfold phiA
    rw [if_pos hX, if_pos (prim X Z hX hZ)]
    obtain ⟨κ, hκ, h⟩ := key X Z hX hZ
    obtain ⟨h1, h2⟩ := invT_mem_of_dual (mem_glLatCong_of_smul hκ)
    obtain ⟨g, rfl⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).1 hX.1
    have h3 : X0 k σ * (invT g).val * κ.val = X0 k σ * (invT (g * invT κ)).val := by
      rw [map_mul, invT_invT, Units.val_mul, Matrix.mul_assoc]
    have hf := @splitTheta_fFun_frameFirstBlock_mul k _ _ _ _ A A' D _ _ _ _ _ _ _ _ μ hμ σ ν Ψ
    rw [h, h3, hf, hf, gdet_mul, map_mul, apow_mul, hν _ h2, apow_of_valuation_eq_one h2.1,
      mul_one, mul_one]
    congr 1
    simp only [smallF, Units.val_mul, ← Matrix.mul_assoc, HasDepth.mul_glLatCong hΨ h1]
  · have hX' : ¬ IsPrimFrame (latA ϖ e (diagLat c)) (X + Z) := fun h => hX (by
      simpa using prim _ (-Z) h (neg_mem hZ))
    unfold phiA
    rw [if_neg hX, if_neg hX']

end GlobalTheory.FrameDepth
