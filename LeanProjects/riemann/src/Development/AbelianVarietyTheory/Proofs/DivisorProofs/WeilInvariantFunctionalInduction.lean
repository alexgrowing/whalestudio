import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt

open ValuativeRel Topology Matrix

noncomputable section

namespace GlobalTheory.RowCut

lemma mem_SB_iff {Z : Type} [TopologicalSpace Z] (f : Z → ℂ) :
    f ∈ GlobalTheory.SplitWeil.SB Z ↔ IsLocallyConstant f ∧ HasCompactSupport f := Iff.rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n m : ℕ}

def IsTop (X : Matrix (Fin (n + 1)) (Fin (m + 1)) k) (i : Fin (m + 1)) : Prop :=
  ∀ j, valuation k (X 0 j) ≤ valuation k (X 0 i)

def sel (X : Matrix (Fin (n + 1)) (Fin (m + 1)) k) : Fin (m + 1) := Classical.epsilon (IsTop X)

lemma isTop_sel (X : Matrix (Fin (n + 1)) (Fin (m + 1)) k) : IsTop X (sel X) :=
  Classical.epsilon_spec (Finite.exists_max fun j => valuation k (X 0 j))

lemma sel_ne_zero {X : Matrix (Fin (n + 1)) (Fin (m + 1)) k} (hX : X 0 ≠ 0) : X 0 (sel X) ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hX
  intro h
  have h1 := isTop_sel X j
  rw [h, map_zero] at h1
  exact hj ((valuation k).zero_iff.1 (le_antisymm h1 zero_le'))

lemma sel_eventually {X : Matrix (Fin (n + 1)) (Fin (m + 1)) k} (hX : X 0 ≠ 0) :
    ∀ᶠ X' in 𝓝 X, sel X' = sel X := by
  set s := sel X with hs_def
  have hs : X 0 s ≠ 0 := sel_ne_zero hX
  set M := valuation k (X 0 s) with hM_def
  have hM : M ≠ 0 := (Valuation.ne_zero_iff _).2 hs
  have key : ∀ᶠ X' in 𝓝 X, ∀ j, (X 0 j ≠ 0 → valuation k (X' 0 j) = valuation k (X 0 j)) ∧
      (X 0 j = 0 → valuation k (X' 0 j) < M) := by
    rw [Filter.eventually_all]
    intro j
    have hc : Continuous fun X' : Matrix (Fin (n + 1)) (Fin (m + 1)) k => X' 0 j :=
      (continuous_apply j).comp (continuous_apply 0)
    by_cases hj : X 0 j = 0
    · have h0 : {x : k | valuation k x < M} ∈ 𝓝 (X 0 j) := by
        rw [hj]
        exact (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 M hM, by simp⟩
      filter_upwards [hc.continuousAt.preimage_mem_nhds h0] with X' h
      exact ⟨fun h' => absurd hj h', fun _ => h⟩
    · have h0 := (valuation k).locally_const ((Valuation.ne_zero_iff _).2 hj)
      filter_upwards [hc.continuousAt.preimage_mem_nhds h0] with X' h
      exact ⟨fun _ => h, fun h' => absurd h' hj⟩
  have htop : ∀ᶠ X' in 𝓝 X, IsTop X' = IsTop X := by
    filter_upwards [key] with X' h
    funext i
    apply propext
    have hvs : valuation k (X' 0 s) = M := (h s).1 hs
    by_cases hi : X 0 i = 0
    · refine iff_of_false (fun h' => ?_) (fun h' => ?_)
      · have := h' s
        rw [hvs] at this
        exact absurd (lt_of_le_of_lt this ((h i).2 hi)) (lt_irrefl _)
      · have := h' s
        rw [hi, map_zero] at this
        exact hM (le_antisymm this zero_le')
    · have hv := (h i).1 hi
      constructor
      · intro h' j
        by_cases hj : X 0 j = 0
        · rw [hj, map_zero]; exact zero_le'
        · rw [← (h j).1 hj, ← hv]; exact h' j
      · intro h' j
        rw [hv]
        by_cases hj : X 0 j = 0
        · exact le_of_lt (lt_of_lt_of_le ((h j).2 hj) (h' s))
        · rw [(h j).1 hj]; exact h' j
  filter_upwards [htop] with X' h
  simp only [sel, h, hs_def]

variable {Y : Type} [TopologicalSpace Y]

def piece (Φ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (i : Fin (m + 1)) :
    Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ :=
  fun p => if sel p.2 = i then Φ p else 0

lemma piece_mem {Φ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ} (hΦ : Φ ∈ GlobalTheory.SplitWeil.SB _)
    (hrow : ∀ y X, X 0 = 0 → Φ (y, X) = 0) (i : Fin (m + 1)) :
    piece Φ i ∈ GlobalTheory.SplitWeil.SB _ := by
  rw [mem_SB_iff] at hΦ ⊢
  refine ⟨?_, hΦ.2.mono fun p hp h => hp (by simp [piece, h])⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  have hev := (IsLocallyConstant.iff_eventually_eq _).1 hΦ.1 p
  by_cases hp : Φ p = 0
  · filter_upwards [hev] with q hq
    simp [piece, hq, hp]
  · have hX : p.2 0 ≠ 0 := fun h => hp (by simpa using hrow p.1 p.2 h)
    filter_upwards [hev, (continuous_snd.tendsto p).eventually (sel_eventually hX)] with q hq hs
    simp only [piece, hq, hs]

lemma piece_vanish {Φ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ}
    (hrow : ∀ y X, X 0 = 0 → Φ (y, X) = 0) (i : Fin (m + 1)) (y : Y)
    (X : Matrix (Fin (n + 1)) (Fin (m + 1)) k) (hX : X 0 i = 0) : piece Φ i (y, X) = 0 := by
  simp only [piece]
  split_ifs with h
  · by_cases h0 : X 0 = 0
    · exact hrow y X h0
    · exact absurd (h ▸ hX) (sel_ne_zero h0)
  · rfl

lemma sum_piece (Φ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) :
    ∑ i, piece Φ i = Φ := by
  funext p
  simp [piece, Finset.sum_apply]

def swapH (i : Fin (m + 1)) :
    Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k ≃ₜ Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k where
  toFun p := (p.1, p.2.submatrix id (Equiv.swap 0 i))
  invFun p := (p.1, p.2.submatrix id (Equiv.swap 0 i))
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := continuous_fst.prodMk
    (continuous_snd.matrix_submatrix _ _)
  continuous_invFun := continuous_fst.prodMk
    (continuous_snd.matrix_submatrix _ _)

def permGL' (σ : Equiv.Perm (Fin (m + 1))) : GL (Fin (m + 1)) k :=
  ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm], by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm]⟩

lemma mul_permGL' (σ : Equiv.Perm (Fin (m + 1))) (X : Matrix (Fin (n + 1)) (Fin (m + 1)) k) :
    X * ((permGL' σ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = X.submatrix id σ.symm := by
  show X * σ.toPEquiv.toMatrix = _
  rw [PEquiv.mul_toMatrix_toPEquiv]

theorem eq_zero_of_row_vanish : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (Y : Type) [TopologicalSpace Y] (m : ℕ) (μ : kˣ →* ℂˣ)
    (L : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k) →ₗ[ℂ] ℂ),
      (∀ (g : GL (Fin (m + 1)) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k)),
        (∀ (y : Y) (X : Matrix (Fin (n + 1)) (Fin (m + 1)) k),
          (Φ' : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (y, X) =
            (Φ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (y, X * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k))) →
        L Φ' = (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * L Φ) →
      (∀ Φ : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k),
        (∀ (y : Y) (X : Matrix (Fin (n + 1)) (Fin (m + 1)) k), X 0 0 = 0 → (Φ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (y, X) = 0) →
        L Φ = 0) →
      ∀ Φ : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k),
        (∀ (y : Y) (X : Matrix (Fin (n + 1)) (Fin (m + 1)) k), X 0 = 0 → (Φ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (y, X) = 0) →
        L Φ = 0 := by
  intro k _ _ _ _ n Y _ m μ L hL h0 Φ hrow
  have step1 : ∀ (i : Fin (m + 1))
      (Ψ : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k)),
      (∀ y X, X 0 i = 0 → (Ψ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) (y, X) = 0) →
      L Ψ = 0 := by
    intro i Ψ hΨ
    have hm := (mem_SB_iff _).1 Ψ.2
    have hmem : ((Ψ : Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k → ℂ) ∘ swapH (k := k) (n := n) (Y := Y) i)
        ∈ GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k) :=
      (mem_SB_iff _).2 ⟨hm.1.comp_continuous (swapH i).continuous, hm.2.comp_homeomorph (swapH i)⟩
    have h1 := hL (permGL' (Equiv.swap 0 i)) Ψ ⟨_, hmem⟩ (by
      intro y X
      rw [mul_permGL', Equiv.symm_swap]
      rfl)
    have h2 : L ⟨_, hmem⟩ = 0 := h0 _ (by
      intro y X hX
      refine hΨ y (X.submatrix id (Equiv.swap 0 i)) ?_
      simpa using hX)
    rw [h2] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (Units.ne_zero _)
  have hsum : Φ = ∑ i, (⟨piece Φ.1 i, piece_mem Φ.2 hrow i⟩ :
      GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin (m + 1)) k)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (sum_piece Φ.1).symm
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => step1 i _ fun y X hX => piece_vanish hrow i y X hX

end GlobalTheory.RowCut
