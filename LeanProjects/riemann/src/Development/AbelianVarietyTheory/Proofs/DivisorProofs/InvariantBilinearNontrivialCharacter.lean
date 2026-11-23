import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankBilinearInvariantScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalValueFirstClopenPartitionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalValueSecondClopenPartitionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinedBoxDisjointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EboxIsClopenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalUniformizerBoxTransformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalUnitBoxInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialCharacterUniformizerOrUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBoxMovedByGlStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRowSectionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRightInverseExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGlBoxTransformStatement

noncomputable section
namespace GlobalTheory.NormalCore
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem self_mem_ebox {A D : Type} (ϖ : kˣ) (C : Matrix A D k) (r : A → D → ℕ) : C ∈ ebox ϖ C r := by
  intro i j; simp

theorem mem_of_pv_ne_zero {n d : ℕ} {Bf : fullRk k n d →ₗ[ℂ] fullRk k n d →ₗ⋆[ℂ] ℂ}
    {B₁ B₂ : Set (Matrix (Fin n) (Fin d) k)} (h : pv Bf B₁ B₂ ≠ 0) :
    B₁.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d ∧
      B₂.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d := by
  by_contra hn
  exact h (by rw [pv, dif_neg hn])

theorem exists_pos_sum {ι : Type} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℂ) (c : ℂ)
    (hf : ∀ i ∈ s, ∃ r : ℝ, 0 < r ∧ f i = r * c) : ∃ P : ℝ, 0 < P ∧ ∑ i ∈ s, f i = P * c := by
  choose! r hr using hf
  refine ⟨∑ i ∈ s, r i, Finset.sum_pos (fun i hi => (hr i hi).1) hs, ?_⟩
  rw [Finset.sum_congr rfl fun i hi => (hr i hi).2, Complex.ofReal_sum, Finset.sum_mul]

theorem cells_left {n d : ℕ} {ϖ : kˣ} (hϖ : IsUnif ϖ) (Bf : fullRk k n d →ₗ[ℂ] fullRk k n d →ₗ⋆[ℂ] ℂ)
    (p : Matrix (Fin n) (Fin d) k) (r r' : Fin n → Fin d → ℕ) (hr : ∀ i j, r i j ≤ r' i j)
    (B₂ : Set (Matrix (Fin n) (Fin d) k)) (c : ℂ)
    (hm : (ebox ϖ p r).indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d)
    (hc : ∀ x ∈ ebox ϖ p r, ∃ t : ℝ, 0 < t ∧ pv Bf (ebox ϖ x r') B₂ = t * c) :
    ∃ P : ℝ, 0 < P ∧ pv Bf (ebox ϖ p r) B₂ = P * c := by
  obtain ⟨S, hS⟩ := GlobalTheory.T.refined_box_disjoint_cover k (Fin n) (Fin d) ϖ hϖ r r' hr
  obtain ⟨hU, hD⟩ := hS p
  rw [GlobalTheory.T.principal_value_first_clopen_partition k n d Bf _ S (fun x => ebox ϖ (p + x) r') _ B₂ hm (fun x _ => GlobalTheory.T.ebox_isClopen k _ _ ϖ _ _) hD hU]
  refine exists_pos_sum S ?_ _ c fun x hx => hc _ ?_
  · have := self_mem_ebox ϖ p r
    rw [hU] at this
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 this
    exact ⟨x, hx⟩
  · rw [hU]
    exact Set.mem_iUnion₂.2 ⟨x, hx, self_mem_ebox _ _ _⟩

theorem cells_right {n d : ℕ} {ϖ : kˣ} (hϖ : IsUnif ϖ) (Bf : fullRk k n d →ₗ[ℂ] fullRk k n d →ₗ⋆[ℂ] ℂ)
    (p : Matrix (Fin n) (Fin d) k) (r r' : Fin n → Fin d → ℕ) (hr : ∀ i j, r i j ≤ r' i j)
    (B₁ : Set (Matrix (Fin n) (Fin d) k)) (c : ℂ)
    (hm : (ebox ϖ p r).indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d)
    (hc : ∀ x ∈ ebox ϖ p r, ∃ t : ℝ, 0 < t ∧ pv Bf B₁ (ebox ϖ x r') = t * c) :
    ∃ P : ℝ, 0 < P ∧ pv Bf B₁ (ebox ϖ p r) = P * c := by
  obtain ⟨S, hS⟩ := GlobalTheory.T.refined_box_disjoint_cover k (Fin n) (Fin d) ϖ hϖ r r' hr
  obtain ⟨hU, hD⟩ := hS p
  rw [GlobalTheory.T.principal_value_second_clopen_partition k n d Bf _ S (fun x => ebox ϖ (p + x) r') B₁ _ hm (fun x _ => GlobalTheory.T.ebox_isClopen k _ _ ϖ _ _) hD hU]
  refine exists_pos_sum S ?_ _ c fun x hx => hc _ ?_
  · have := self_mem_ebox ϖ p r
    rw [hU] at this
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 this
    exact ⟨x, hx⟩
  · rw [hU]
    exact Set.mem_iUnion₂.2 ⟨x, hx, self_mem_ebox _ _ _⟩

theorem apow_half_pos (x : kˣ) (d : ℕ) : ∃ a : ℝ, 0 < a ∧ apow x ((d : ℂ) / 2) = a := by
  refine ⟨(GlobalTheory.SplitWeil.nabs k x) ^ ((d : ℝ) / 2), Real.rpow_pos_of_pos (GlobalTheory.SplitWeil.Model.nabs_pos x) _, ?_⟩
  rw [apow, Complex.ofReal_cpow (GlobalTheory.SplitWeil.Model.nabs_pos x).le]
  push_cast; rfl

theorem eq_one_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) (h : (P : ℂ) * z = Q) :
    z = 1 := by
  have h1 : P = Q := by
    have := congrArg norm h
    rwa [norm_mul, hz, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hP.le,
      Real.norm_of_nonneg hQ.le] at this
  subst h1
  have h0 : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  exact mul_left_cancel₀ h0 (by rw [h, mul_one])

theorem pv_box_eq_zero {n d : ℕ} {ν : kˣ →* ℂˣ} {ϖ : kˣ} (hϖ : IsUnif ϖ) (hu : ∀ x, ‖(ν x : ℂ)‖ = 1) (hν : ν ≠ 1)
    (Bf : fullRk k n d →ₗ[ℂ] fullRk k n d →ₗ⋆[ℂ] ℂ)
    (hG : (∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' Ψ₂ : fullRk k n d), Ψ₁'.1 = lact ν g Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂))
    (hH : (∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' : fullRk k n d,
      Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂))
    (i₀ : Fin n) (j₀ : Fin d) (p₁ p₂ : Matrix (Fin n) (Fin d) k) (h₀ : ∀ i j, valuation k (p₁ i j) ≤ 1)
    (h₁ : ∀ j, p₁ i₀ j = if j = j₀ then 1 else 0) (h₂ : ∀ i, i ≠ i₀ → p₁ i j₀ = 0) (h₃ : ∀ i, p₂ i j₀ = 0)
    (hS : ∃ S : Matrix (Fin d) (Fin n) k, (∀ j i, valuation k (S j i) ≤ 1) ∧ (∀ i, S j₀ i = 0) ∧ p₂ * S = 1)
    (N : ℕ) (hN : 1 ≤ N) : pv Bf (box ϖ p₁ fun _ => N) (box ϖ p₂ fun _ => N) = 0 := by
  by_contra hne
  rcases GlobalTheory.T.nontrivial_character_uniformizer_or_unit k ν ϖ hϖ hν with ht | ⟨u, hu1, ht⟩
  · obtain ⟨r, hr, hT⟩ := GlobalTheory.T.full_rank_bilinear_invariant_scaling k n d ν Bf hG hH (dgl i₀ ϖ) (dgl j₀ ϖ⁻¹) (box ϖ p₁ fun _ => N)
      (box ϖ p₂ fun _ => N)
    obtain ⟨e₁, e₂⟩ := GlobalTheory.T.diagonal_uniformizer_box_transform k n d i₀ j₀ ϖ p₁ p₂ N hN h₁ h₂ h₃
    rw [e₁, e₂, gdet_dgl] at hT
    obtain ⟨a, ha, hae⟩ := apow_half_pos ϖ d
    rw [hae] at hT
    have hν0 : (ν ϖ : ℂ) ≠ 0 := Units.ne_zero _
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hne' : pv Bf (ebox ϖ p₁ (scaledBoxRadiiAtEntry i₀ j₀ N)) (ebox ϖ p₂ (baseCellRadiiAtColumn j₀ N)) ≠ 0 := by
      rw [hT]; exact mul_ne_zero (mul_ne_zero hr0 (inv_ne_zero (mul_ne_zero hν0 ha0))) hne
    set c := pv Bf (ebox ϖ p₁ (baseCellRadiiAtEntry i₀ j₀ N)) (ebox ϖ p₂ (baseCellRadiiAtColumn j₀ N)) with hc
    obtain ⟨m₁, m₂⟩ := mem_of_pv_ne_zero hne
    obtain ⟨P, hP, hPe⟩ : ∃ P : ℝ, 0 < P ∧ pv Bf (box ϖ p₁ fun _ => N) (box ϖ p₂ fun _ => N) = P * c := by
      refine cells_left hϖ Bf p₁ (fun _ _ => N) (baseCellRadiiAtEntry i₀ j₀ N) (fun i j => ?_) _ c m₁ fun x₁ hx₁ => ?_
      · simp only [baseCellRadiiAtEntry]; split_ifs <;> omega
      refine cells_right hϖ Bf p₂ (fun _ _ => N) (baseCellRadiiAtColumn j₀ N) (fun i j => ?_) _ c m₂ fun x₂ hx₂ => ?_
      · simp only [baseCellRadiiAtColumn]; split_ifs <;> omega
      obtain ⟨g, h, hg, f₁, f₂⟩ := GlobalTheory.T.integral_row_section_exists k n d i₀ j₀ ϖ hϖ p₁ p₂ N hN h₀ h₁ h₂ h₃ hS x₁ hx₁ x₂ hx₂
      obtain ⟨t, ht0, hte⟩ := GlobalTheory.T.full_rank_bilinear_invariant_scaling k n d ν Bf hG hH g h (ebox ϖ p₁ (baseCellRadiiAtEntry i₀ j₀ N)) (ebox ϖ p₂ (baseCellRadiiAtColumn j₀ N))
      rw [f₁, f₂, hg] at hte
      exact ⟨t, ht0, by simpa using hte⟩
    obtain ⟨Q, hQ, hQe⟩ : ∃ Q : ℝ, 0 < Q ∧
        pv Bf (ebox ϖ p₁ (scaledBoxRadiiAtEntry i₀ j₀ N)) (ebox ϖ p₂ (baseCellRadiiAtColumn j₀ N)) = Q * c := by
      refine cells_left hϖ Bf p₁ _ (baseCellRadiiAtEntry i₀ j₀ N) (fun i j => ?_) _ c (mem_of_pv_ne_zero hne').1 fun x₁ hx₁ => ?_
      · simp only [baseCellRadiiAtEntry, scaledBoxRadiiAtEntry]; split_ifs <;> omega
      obtain ⟨h, f₁, f₂⟩ := GlobalTheory.T.unipotent_box_moved_by_gl k n d i₀ j₀ ϖ hϖ p₁ p₂ N hN h₁ h₂ h₃ x₁ hx₁
      obtain ⟨t, ht0, hte⟩ := GlobalTheory.T.full_rank_bilinear_invariant_scaling k n d ν Bf hG hH 1 h (ebox ϖ p₁ (baseCellRadiiAtEntry i₀ j₀ N)) (ebox ϖ p₂ (baseCellRadiiAtColumn j₀ N))
      have hg : gdet (1 : GL (Fin n) k) = 1 := by ext; simp [gdet]
      simp only [Units.val_one, transpose_one, Matrix.one_mul] at hte
      rw [f₁, f₂, hg] at hte
      exact ⟨t, ht0, by simpa using hte⟩
    have hc0 : c ≠ 0 := by
      rintro h0
      exact hne (by rw [hPe, h0, mul_zero])
    rw [hQe, hPe] at hT
    have key : ((Q * a : ℝ) : ℂ) * (ν ϖ : ℂ) = ((r * P : ℝ) : ℂ) := by
      have h5 : (Q : ℂ) = r * ((ν ϖ : ℂ) * a)⁻¹ * P := mul_right_cancel₀ hc0 (by rw [hT]; ring)
      push_cast; rw [h5]; field_simp
    exact ht (Units.ext (eq_one_of_norm_one (hu ϖ) (mul_pos hQ ha) (mul_pos hr hP) key))
  · obtain ⟨r, hr, hT⟩ := GlobalTheory.T.full_rank_bilinear_invariant_scaling k n d ν Bf hG hH (dgl i₀ u) (dgl j₀ u⁻¹) (box ϖ p₁ fun _ => N)
      (box ϖ p₂ fun _ => N)
    obtain ⟨e₁, e₂⟩ := GlobalTheory.T.diagonal_unit_box_invariant k n d i₀ j₀ ϖ u p₁ p₂ N hu1 h₁ h₂ h₃
    rw [e₁, e₂, gdet_dgl, apow_of_valuation_eq_one hu1, mul_one] at hT
    have hν0 : (ν u : ℂ) ≠ 0 := Units.ne_zero _
    have key : ((1 : ℝ) : ℂ) * (ν u : ℂ) = r := by
      have h5 : (1 : ℂ) = r * (ν u : ℂ)⁻¹ := mul_right_cancel₀ hne (by rw [← hT]; ring)
      push_cast; rw [one_mul]; field_simp at h5; exact h5
    exact ht (Units.ext (eq_one_of_norm_one (hu u) one_pos hr key))

end GlobalTheory.NormalCore
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.NormalCore.normal_core : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SmGL.IsUnitaryChar ν → ν ≠ 1 →
    ∀ (Bf : GlobalTheory.FullRankCoinv.fullRk k n d →ₗ[ℂ] GlobalTheory.FullRankCoinv.fullRk k n d →ₗ⋆[ℂ] ℂ) (hG : ∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d), Ψ₁'.1 = GlobalTheory.FullRankCoinv.lact ν g Ψ₁.1 →
        Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂)
    (hH : ∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.FullRankCoinv.fullRk k n d,
        Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂)
    (i₀ : Fin n) (j₀ : Fin d) (Y₁ Y₂ : Matrix (Fin n) (Fin d) k),
    (∀ i j, ValuativeRel.valuation k (Y₁ i j) ≤ 1) → (∀ j, Y₁ i₀ j = if j = j₀ then 1 else 0) →
    (∀ i, i ≠ i₀ → Y₁ i j₀ = 0) → (∀ i, Y₂ i j₀ = 0) →
    (∃ S : Matrix (Fin d) (Fin n) k, (∀ j i, ValuativeRel.valuation k (S j i) ≤ 1) ∧ (∀ i, S j₀ i = 0) ∧ Y₂ * S = 1) →
    ∀ Z₁ ∈ GlobalTheory.RankCoinv.box ϖ Y₁ (fun _ => 1), ∀ Z₂ ∈ GlobalTheory.RankCoinv.box ϖ Y₂ (fun _ => 1), ∀ N : ℕ, 1 ≤ N →
      ∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d, Ψ₁.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₁ (fun _ => N) →
        Ψ₂.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₂ (fun _ => N) → Bf Ψ₁ Ψ₂ = 0 := by
  open GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.SplitFlip GlobalTheory.NormalCore in
  intro k _ _ _ _ n d ν ϖ hϖ hu hν Bf hG hH i₀ j₀ Y₁ Y₂ h₀ h₁ h₂ h₃ hS Z₁ hZ₁ Z₂ hZ₂ N hN Ψ₁ Ψ₂ e₁ e₂
  obtain ⟨g, h, g₁, g₂, g₃, g₄, q₀, q₁, q₂, q₃, qS⟩ :=
    GlobalTheory.T.integral_right_inverse_exists k n d i₀ j₀ ϖ hϖ Y₁ Y₂ h₀ h₁ h₂ h₃ hS Z₁ hZ₁ Z₂ hZ₂
  have hz := GlobalTheory.NormalCore.pv_box_eq_zero hϖ hu hν Bf hG hH i₀ j₀ _ _ q₀ q₁ q₂ q₃ qS N hN
  obtain ⟨r, -, hT⟩ := GlobalTheory.T.full_rank_bilinear_invariant_scaling k n d ν Bf hG hH g h (GlobalTheory.RankCoinv.box ϖ ((g.1)ᵀ * Z₁ * h.1) fun _ => N)
    (GlobalTheory.RankCoinv.box ϖ (Z₂ * h.1) fun _ => N)
  have hone : ∀ i j, ValuativeRel.valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro i j; rw [Matrix.one_apply]; split_ifs <;> simp
  have f₂ := GlobalTheory.T.integral_gl_box_transform k n d ϖ 1 h hone (by simpa using hone) g₃ g₄ Z₂ N
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul] at f₂
  rw [GlobalTheory.T.integral_gl_box_transform k n d ϖ g h g₁ g₂ g₃ g₄ Z₁ N, f₂, hz, mul_zero] at hT
  rw [← GlobalTheory.NormalCore.pv_eq Bf Ψ₁ Ψ₂ e₁ e₂, hT]
