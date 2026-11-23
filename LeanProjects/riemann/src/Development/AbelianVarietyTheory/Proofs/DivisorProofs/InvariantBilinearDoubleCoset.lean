import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenIntegrabilityFullRankOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentInvariantFunctionalTwoDim
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BoxTransport

open GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.RankCoinv.Decomp GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_sum_box_of_support {n d : ℕ} {ϖ : kˣ} (hϖ : IsUnif ϖ) (Φ : fullRk k n d)
    (U : Set (Matrix (Fin n) (Fin d) k)) (hU : ∀ X, Φ.1 X ≠ 0 → X ∈ U) :
    ∃ m₁ : ℕ, ∀ m ≥ m₁, ∃ (s : Finset (Matrix (Fin n) (Fin d) k)) (b : Matrix (Fin n) (Fin d) k → fullRk k n d),
      (∀ c ∈ s, (b c).1 = boxFn ϖ c (fun _ => m) ∧ c ∈ U) ∧ Φ = ∑ c ∈ s, Φ.1 c • b c := by
  classical
  obtain ⟨m₁, hm₁⟩ := exists_sum_boxFn k (Fin n) (Fin d) ϖ hϖ Φ.1 Φ.2.1
  refine ⟨m₁, fun m hm => ?_⟩
  obtain ⟨s, hs, hconst⟩ := hm₁ m hm
  have hmem : ∀ c ∈ s, Φ.1 c ≠ 0 → boxFn ϖ c (fun _ => m) ∈ fullRk k n d := by
    intro c hcs hc
    refine ⟨boxFn_mem_SB ϖ c _, fun Y hY => ?_⟩
    by_cases hYb : Y ∈ box ϖ c (fun _ => m)
    · exact absurd (Φ.2.2 Y hY) (by rw [hconst c hcs Y hYb]; exact hc)
    · exact Set.indicator_of_notMem hYb _
  let s' := s.filter (fun c => Φ.1 c ≠ 0)
  let b : Matrix (Fin n) (Fin d) k → fullRk k n d := fun c =>
    if h : c ∈ s ∧ Φ.1 c ≠ 0 then ⟨boxFn ϖ c (fun _ => m), hmem c h.1 h.2⟩ else 0
  refine ⟨s', b, fun c hc => ?_, ?_⟩
  · have hc' := Finset.mem_filter.1 hc
    refine ⟨by simp only [b, dif_pos hc'], hU c hc'.2⟩
  · apply Subtype.ext
    rw [Submodule.coe_sum]
    conv_lhs => rw [hs]
    rw [Finset.sum_filter_of_ne (p := fun c => Φ.1 c ≠ 0)]
    · refine Finset.sum_congr rfl fun c hcs => ?_
      by_cases hc : Φ.1 c = 0
      · simp [hc]
      · simp only [Submodule.coe_smul, b, dif_pos (show c ∈ s ∧ Φ.1 c ≠ 0 from ⟨hcs, hc⟩)]
    · intro c _ h hc
      apply h
      simp [hc]

theorem form_eq_zero_of_support {n d : ℕ} {ϖ : kˣ} (hϖ : IsUnif ϖ)
    (Bf : fullRk k n d →ₗ[ℂ] fullRk k n d →ₗ⋆[ℂ] ℂ) (U₁ U₂ : Set (Matrix (Fin n) (Fin d) k))
    (hB : ∀ Z₁ ∈ U₁, ∀ Z₂ ∈ U₂, ∀ N : ℕ, 1 ≤ N → ∀ Ψ₁ Ψ₂ : fullRk k n d, Ψ₁.1 = boxFn ϖ Z₁ (fun _ => N) →
        Ψ₂.1 = boxFn ϖ Z₂ (fun _ => N) → Bf Ψ₁ Ψ₂ = 0)
    (Φ₁ Φ₂ : fullRk k n d) (h₁ : ∀ X, Φ₁.1 X ≠ 0 → X ∈ U₁) (h₂ : ∀ X, Φ₂.1 X ≠ 0 → X ∈ U₂) :
    Bf Φ₁ Φ₂ = 0 := by
  obtain ⟨a₁, ha₁⟩ := exists_sum_box_of_support hϖ Φ₁ U₁ h₁
  obtain ⟨a₂, ha₂⟩ := exists_sum_box_of_support hϖ Φ₂ U₂ h₂
  obtain ⟨s₁, b₁, hb₁, e₁⟩ := ha₁ (max (max a₁ a₂) 1) (le_max_of_le_left (le_max_left _ _))
  obtain ⟨s₂, b₂, hb₂, e₂⟩ := ha₂ (max (max a₁ a₂) 1) (le_max_of_le_left (le_max_right _ _))
  rw [e₁, e₂]
  simp only [map_sum, LinearMap.sum_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply]
  refine Finset.sum_eq_zero fun c' hc' => ?_
  rw [Finset.sum_eq_zero fun c hc => ?_, smul_zero]
  rw [hB c (hb₁ c hc).2 c' (hb₂ c' hc').2 _ (le_max_right _ _) _ _ (hb₁ c hc).1 (hb₂ c' hc').1]
  simp

end GlobalTheory.BoxTransport

theorem GlobalTheory.BoxTransport.transport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ →
    ∀ (Bf : GlobalTheory.FullRankCoinv.fullRk k n d →ₗ[ℂ] GlobalTheory.FullRankCoinv.fullRk k n d →ₗ⋆[ℂ] ℂ) (hG : ∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d), Ψ₁'.1 = GlobalTheory.FullRankCoinv.lact ν g Ψ₁.1 →
        Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂)
    (hH : ∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.FullRankCoinv.fullRk k n d,
        Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂)
    (Y₁ Y₂ : Matrix (Fin n) (Fin d) k) (g : GL (Fin n) k) (h : GL (Fin d) k),
    (∀ Z₁ ∈ GlobalTheory.RankCoinv.box ϖ ((g.1)ᵀ * Y₁ * h.1) (fun _ => 1), ∀ Z₂ ∈ GlobalTheory.RankCoinv.box ϖ (Y₂ * h.1) (fun _ => 1),
      ∀ N : ℕ, 1 ≤ N → ∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d, Ψ₁.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₁ (fun _ => N) →
        Ψ₂.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₂ (fun _ => N) → Bf Ψ₁ Ψ₂ = 0) →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Z₁ ∈ GlobalTheory.RankCoinv.box ϖ Y₁ (fun _ => N₀), ∀ Z₂ ∈ GlobalTheory.RankCoinv.box ϖ Y₂ (fun _ => N₀),
      ∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d, Ψ₁.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₁ (fun _ => N) →
        Ψ₂.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₂ (fun _ => N) → Bf Ψ₁ Ψ₂ = 0 := by
  open GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.RankCoinv.Decomp GlobalTheory.SplitFlip GlobalTheory.BoxTransport in
  intro k _ _ _ _ n d ν ϖ hϖ Bf hG hH Y₁ Y₂ g h hyp
  have hc₁ : Continuous (fun X : Matrix (Fin n) (Fin d) k => (g.1)ᵀ * X * h.1) := by fun_prop
  have hc₂ : Continuous (fun X : Matrix (Fin n) (Fin d) k => X * h.1) := by fun_prop
  obtain ⟨n₁, hn₁⟩ := exists_box_subset hϖ (X := Y₁)
    (((isClopen_box ϖ ((g.1)ᵀ * Y₁ * h.1) (fun _ => 1)).isOpen.preimage hc₁).mem_nhds (mem_box_self ϖ _ _))
  obtain ⟨n₂, hn₂⟩ := exists_box_subset hϖ (X := Y₂)
    (((isClopen_box ϖ (Y₂ * h.1) (fun _ => 1)).isOpen.preimage hc₂).mem_nhds (mem_box_self ϖ _ _))
  refine ⟨max n₁ n₂, fun N hN Z₁ hZ₁ Z₂ hZ₂ Ψ₁ Ψ₂ e₁ e₂ => ?_⟩
  have hs₁ : ∀ X, Ψ₁.1 X ≠ 0 → (g.1)ᵀ * X * h.1 ∈ box ϖ ((g.1)ᵀ * Y₁ * h.1) (fun _ => 1) := by
    intro X hX
    have hXb : X ∈ box ϖ Z₁ (fun _ => N) := by
      by_contra hn
      exact hX (by rw [e₁]; exact Set.indicator_of_notMem hn _)
    have hX₁ : X ∈ box ϖ Y₁ (fun _ => n₁) := box_mono hϖ Y₁ (le_max_left _ _)
      (by rw [← box_eq_of_mem hZ₁]; exact box_mono hϖ Z₁ hN hXb)
    exact hn₁ hX₁
  have hs₂ : ∀ X, Ψ₂.1 X ≠ 0 → X * h.1 ∈ box ϖ (Y₂ * h.1) (fun _ => 1) := by
    intro X hX
    have hXb : X ∈ box ϖ Z₂ (fun _ => N) := by
      by_contra hn
      exact hX (by rw [e₂]; exact Set.indicator_of_notMem hn _)
    have hX₂ : X ∈ box ϖ Y₂ (fun _ => n₂) := box_mono hϖ Y₂ (le_max_right _ _)
      (by rw [← box_eq_of_mem hZ₂]; exact box_mono hϖ Z₂ hN hXb)
    exact hn₂ hX₂
  have eh : (h⁻¹).1 * h.1 = 1 := Units.inv_mul h
  have eg : (g.1)ᵀ * ((g⁻¹).1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  obtain ⟨m, -, hm⟩ := hH h⁻¹
  let Ψ₁' : fullRk k n d := ⟨JacReduce.rtr h⁻¹ Ψ₁.1, JacReduce.fullRk_rtr _ Ψ₁.2⟩
  let Ψ₂' : fullRk k n d := ⟨JacReduce.rtr h⁻¹ Ψ₂.1, JacReduce.fullRk_rtr _ Ψ₂.2⟩
  rw [← hm Ψ₁ Ψ₁' Ψ₂ Ψ₂' rfl rfl]
  suffices hz : Bf Ψ₁' Ψ₂' = 0 by rw [hz, mul_zero]
  let Φ : fullRk k n d := ⟨lact ν g⁻¹ Ψ₁'.1, Reduce.lact_mem ν g⁻¹ Ψ₁'.2⟩
  let c : ℂ := (ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2) *
    ((ν (gdet g⁻¹) : ℂ) * apow (gdet g⁻¹) ((d : ℂ) / 2))
  have hc0 : c ≠ 0 := mul_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _))
    (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _))
  have hlact : (c • Ψ₁').1 = lact ν g Φ.1 := by
    funext Y
    have eY : ((g⁻¹).1)ᵀ * ((g.1)ᵀ * Y) = Y := by
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
    simp only [Φ, lact, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, eY, c]
    ring
  have hg := hG g Φ (c • Ψ₁') Ψ₂' hlact
  have hsupΦ : ∀ X, Φ.1 X ≠ 0 → X ∈ box ϖ ((g.1)ᵀ * Y₁ * h.1) (fun _ => 1) := by
    intro X hX
    have hW : Ψ₁.1 (((g⁻¹).1)ᵀ * X * (h⁻¹).1) ≠ 0 := by
      intro h0
      apply hX
      simp only [Φ, Ψ₁', lact, JacReduce.rtr_apply, h0, mul_zero]
    have := hs₁ _ hW
    rwa [show (g.1)ᵀ * (((g⁻¹).1)ᵀ * X * (h⁻¹).1) * h.1 = X by
      simp only [Matrix.mul_assoc]; rw [eh, Matrix.mul_one, ← Matrix.mul_assoc, eg, Matrix.one_mul]] at this
  have hsup₂ : ∀ X, Ψ₂'.1 X ≠ 0 → X ∈ box ϖ (Y₂ * h.1) (fun _ => 1) := by
    intro X hX
    have hW : Ψ₂.1 (X * (h⁻¹).1) ≠ 0 := hX
    have := hs₂ _ hW
    rwa [Matrix.mul_assoc, eh, Matrix.mul_one] at this
  have hz := form_eq_zero_of_support hϖ Bf _ _ hyp Φ Ψ₂' hsupΦ hsup₂
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hz] at hg
  exact (mul_eq_zero.1 hg).resolve_left hc0
