import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsLocalBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsBranchesGoodPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsPowerUnitCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix

noncomputable section

theorem eval_linForm_eq_linEval {n : ℕ} (u x : Fin n → ℂ) :
    eval x (linForm u) = GroundTheory.Heights₂.Heights.linEval u x := by
  simp [linForm, GroundTheory.Heights₂.Heights.linEval]

theorem BranchesToGoodPosition.proof (hG : BranchesGoodPoint.Statement)
    (hC : PowerUnitCount.Statement) : BranchesToGoodPosition.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord
  obtain ⟨q, π, s, hqW, ⟨N₁, hN₁, hcov₁⟩, ⟨N₂, hN₂, hsl₂⟩, ⟨N₃, hN₃, hz₃⟩, hs, hder, hprop⟩ :=
    hG n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord
  have hJW : J ≤ W := le_trans le_sup_left hW.1.2
  have hWJ : ∀ x, x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
      x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J := fun x hx f hf => hx f (hJW hf)
  have huW : ∀ x, x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
      GroundTheory.Heights₂.Heights.linEval u x = 0 := fun x hx => by
    rw [← eval_linForm_eq_linEval]
    exact hx _ (hW.1.2 (le_sup_right (a := J) (Ideal.subset_span rfl)))
  choose H hHd hH0 hHeq using hord
  set F : Fin m → (Fin (d + 1) → ℂ) → Fin d → ℂ := fun b τ => π *ᵥ (γ b).toFun τ with hFdef
  have hFd : ∀ b, DifferentiableOn ℂ (F b) (Metric.ball 0 (γ b).radius) := fun b =>
    (Matrix.mulVecLin π).toContinuousLinearMap.differentiable.comp_differentiableOn
      (γ b).differentiableOn
  have hchart := fun b => hC d (ord b) (Metric.ball 0 (γ b).radius) (F b) (H b) (s b)
    Metric.isOpen_ball (hs b).1 (hs b).2.1 (hFd b) (hHd b) (hH0 b _ (hs b).1) (hder b)
  choose P₀ hP₀ hinj hcnt using hchart
  choose ε hε hεP using fun b => hprop b (P₀ b) (hP₀ b)

  obtain ⟨b₀, -⟩ : ∃ b, q ∈ (γ b).image := by
    simpa using hcov₁ ⟨hWJ q hqW, mem_of_mem_nhds hN₁⟩
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨b₀, Finset.mem_univ _⟩
  obtain ⟨δ₁, hδ₁, hδ₁N⟩ := Metric.mem_nhds_iff.1 (inter_mem hN₁ (inter_mem hN₂ hN₃))
  set ε₀ := Finset.univ.inf' hne ε with hε₀
  have hε₀pos : 0 < ε₀ := (Finset.lt_inf'_iff hne).2 fun b _ => hε b
  set δ := min δ₁ ε₀ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have h2δN : Metric.ball q (2 * δ) ⊆ N₁ ∩ (N₂ ∩ N₃) :=
    (Metric.ball_subset_ball (by rw [hδdef]; linarith [min_le_left δ₁ ε₀])).trans hδ₁N
  have h2δε : ∀ b, 2 * δ ≤ ε b := fun b => by
    rw [hδdef]; linarith [min_le_right δ₁ ε₀, Finset.inf'_le ε (Finset.mem_univ b)]

  have hpar : ∀ b, ∀ τ ∈ Metric.ball 0 (γ b).radius, (γ b).toFun τ ∈ Metric.ball q (2 * δ) →
      τ ∈ P₀ b := fun b τ hτ hx =>
    hεP b τ hτ (Metric.ball_subset_ball (h2δε b) hx)
  set U := Metric.ball q δ with hUdef
  have hUsub : U ⊆ Metric.ball q (2 * δ) := Metric.ball_subset_ball (by linarith)
  set P : Fin m → Set (Fin (d + 1) → ℂ) := fun b => Metric.ball 0 (γ b).radius ∩ (γ b).toFun ⁻¹' U
    with hPdef
  have hPo : ∀ b, IsOpen (P b) := fun b =>
    (γ b).differentiableOn.continuousOn.isOpen_inter_preimage Metric.isOpen_ball Metric.isOpen_ball
  have hPn : ∀ b, P b ∈ 𝓝 (s b) := fun b =>
    (hPo b).mem_nhds ⟨(hs b).1, by simp [U, (hs b).2.2, hδ]⟩
  have hPP₀ : ∀ b, P b ⊆ P₀ b := fun b τ hτ => hpar b τ hτ.1 (hUsub hτ.2)
  choose V ρ hVo hVm hρ hVsl hVc using fun b => hcnt b (P b) (hPn b) (hPP₀ b)

  have hslq : ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W, x ∈ Metric.ball q (2 * δ) →
      ∃ τ ∈ Metric.ball 0 (γ b₀).radius, τ 0 = 0 ∧ (γ b₀).toFun τ = x ∧ τ ∈ P₀ b₀ := by
    intro x hx hxb
    obtain ⟨τ, ⟨hτ, hτ0⟩, rfl⟩ := hsl₂ b₀ ⟨hx, (h2δN hxb).2.1⟩
    exact ⟨τ, hτ, hτ0, rfl, hpar b₀ τ hτ hxb⟩
  refine ⟨q, π, U, ⋂ b, V b, Finset.univ.inf' hne ρ, ?_⟩
  refine
    { isOpen_U := Metric.isOpen_ball
      isBounded_U := Metric.isBounded_ball
      mem_U := Metric.mem_ball_self hδ
      mem_W := hqW
      isOpen_V := isOpen_iInter_of_finite hVo
      mem_V := Set.mem_iInter.2 fun b => by simpa [F, (hs b).2.2] using hVm b
      pos := (Finset.lt_inf'_iff hne).2 fun b _ => hρ b
      zeros := ?_
      injOn := ?_
      count := ?_ }
  · intro x hxU hxJ hux hxV
    have hx2 : x ∈ Metric.ball q (2 * δ) :=
      Metric.closedBall_subset_ball (by linarith) (Metric.closure_ball_subset_closedBall hxU)
    have hxW : x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W :=
      hz₃ x ⟨hxJ, (h2δN hx2).2.2⟩ hux
    obtain ⟨τ, hτ, hτ0, rfl, hτP₀⟩ := hslq _ hxW hx2
    exact ⟨(hVsl b₀ _ (Set.mem_iInter.1 hxV b₀) τ hτP₀ hτ0 rfl).2, hxW⟩
  · rintro x ⟨hxU, hxW⟩ x' ⟨hxU', hxW'⟩ hππ
    obtain ⟨τ, hτ, hτ0, rfl, hτP₀⟩ := hslq _ hxW (hUsub hxU)
    obtain ⟨τ', hτ', hτ0', rfl, hτP₀'⟩ := hslq _ hxW' (hUsub hxU')
    rw [hinj b₀ ⟨hτP₀, hτ0⟩ ⟨hτP₀', hτ0'⟩ hππ]
  · intro w hw t ht0 htρ
    have hwb : ∀ b, w ∈ V b := Set.mem_iInter.1 hw
    have htb : ∀ b, ‖t‖ < ρ b := fun b => lt_of_lt_of_le htρ (Finset.inf'_le ρ (Finset.mem_univ b))
    set T : Fin m → Set (Fin (d + 1) → ℂ) :=
      fun b => {τ | τ ∈ P b ∧ F b τ = w ∧ τ 0 ^ ord b * H b τ = t} with hTdef
    have hval : ∀ b, ∀ τ ∈ T b, GroundTheory.Heights₂.Heights.linEval u ((γ b).toFun τ) = t := by
      rintro b τ ⟨hτP, -, hτt⟩
      rw [← hτt]
      exact hHeq b τ hτP.1
    have hset : {x | x ∈ U ∩ zeroLocus J ∧ π *ᵥ x = w ∧ linVal u x = t} =
        ⋃ b, (γ b).toFun '' T b := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hxU, hxJ⟩, hπx, hux⟩
        obtain ⟨b, τ, hτ, rfl⟩ : ∃ b, x ∈ (γ b).image := by
          simpa using hcov₁ ⟨hxJ, (h2δN (hUsub hxU)).1⟩
        refine ⟨b, τ, ⟨⟨hτ, hxU⟩, hπx, ?_⟩, rfl⟩
        rw [← hHeq b τ hτ]
        exact hux
      · rintro ⟨b, τ, hτT, rfl⟩
        exact ⟨⟨hτT.1.2, (γ b).mapsTo hτT.1.1⟩, hτT.2.1, hval b τ hτT⟩
    have hdisjT : Pairwise (Function.onFun Disjoint fun b => (γ b).toFun '' T b) := by
      intro b c hbc
      refine Set.disjoint_left.2 ?_
      rintro x ⟨τ, hτT, rfl⟩ ⟨τ', hτT', hx⟩
      have h0 := hdisj b c hbc ⟨⟨τ, hτT.1.1, rfl⟩, ⟨τ', hτT'.1.1, hx⟩⟩
      have h1 := hval b τ hτT
      simp only [Set.mem_ofPred_eq] at h0
      rw [h0] at h1
      exact (norm_pos_iff.1 ht0) h1.symm
    rw [hset, Set.encard_iUnion_of_finite hdisjT, finsum_eq_sum_of_fintype, Nat.cast_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [((γ b).injOn.mono fun τ hτ => hτ.1.1).encard_image]
    exact hVc b w (hwb b) t ht0 (htb b)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
