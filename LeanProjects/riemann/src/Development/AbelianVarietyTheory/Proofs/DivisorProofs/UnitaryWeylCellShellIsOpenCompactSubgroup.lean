import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapLtSwapIffOfAddTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalWeylCellTranslate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

noncomputable section

namespace GlobalTheory.WeylCell.WeylUnipotentShell.ShellGroup

section Order

theorem le_max_one_of_mul_self_le {x e : WithZero (Multiplicative ℤ)} (h : x * x ≤ e) : x ≤ max 1 e := by
  by_contra hc
  push_neg at hc
  have h1 : 1 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hc)
  have h2 : x ≤ x * x := le_mul_of_one_le_right' h1
  exact absurd (lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hc) (h2.trans h)) (lt_irrefl _)

theorem mul_le_of_mul_self_le {x y e : WithZero (Multiplicative ℤ)} (hx : x * x ≤ e) (hy : y * y ≤ e) :
    x * y ≤ e := by
  rcases le_total x y with h | h
  · exact (mul_le_mul' h le_rfl).trans hy
  · exact (mul_le_mul' le_rfl h).trans hx

end Order

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ball_eq_preimage {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (j : ℤ) :
    {x : L | Valued.v x ≤ WithZero.exp j} = (fun x => ϖ ^ j * x) ⁻¹' (intL L : Set L) := by
  have hϖ : Valued.v ϖ = WithZero.exp (-1) := h.2.2.2.1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, intL, Valuation.mem_integer_iff, map_mul,
    map_zpow₀, hϖ]
  rw [← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one, WithZero.exp_neg, inv_mul_le_iff₀ WithZero.exp_pos, mul_one]

theorem ne_zero_of_unramInv {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : ϖ ≠ 0 := by
  intro e
  have hϖ : Valued.v ϖ = WithZero.exp (-1) := h.2.2.2.1
  rw [e, map_zero] at hϖ
  exact WithZero.exp_ne_zero hϖ.symm

theorem isOpen_ball {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (j : ℤ) :
    IsOpen {x : L | Valued.v x ≤ WithZero.exp j} := by
  rw [ball_eq_preimage h]
  exact (Valued.isOpen_integer L).preimage (continuous_const.mul continuous_id)

theorem isClosed_ball {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (j : ℤ) :
    IsClosed {x : L | Valued.v x ≤ WithZero.exp j} := by
  rw [ball_eq_preimage h]
  exact (Valued.isClosed_integer L).preimage (continuous_const.mul continuous_id)

theorem isCompact_ball [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (j : ℤ) :
    IsCompact {x : L | Valued.v x ≤ WithZero.exp j} := by
  rw [ball_eq_preimage h]
  have hc := GlobalTheory.LFun.IntPtsUnitary.isCompact_intL h
  have e : (fun x => ϖ ^ j * x) ⁻¹' (intL L : Set L) = (Homeomorph.mulLeft₀ (ϖ ^ j)
      (zpow_ne_zero j (ne_zero_of_unramInv h))) ⁻¹' (intL L : Set L) := rfl
  rw [e, Homeomorph.isCompact_preimage]
  exact hc

section Block

variable {n : ℕ}

def InBlock (a a' : Fin n) (X : GL (Fin n) L) : Prop :=
  X ∈ unipB L (Fin n) ∧ ∀ i j : Fin n, i < j → (i < a ∨ a' < j) → (X : Matrix (Fin n) (Fin n) L) i j = 0

variable {a m a' : Fin n}

theorem InBlock.entry (ham : m.val = a.val + 1) (hma : a'.val = m.val + 1) {X : GL (Fin n) L}
    (hX : InBlock a a' X) (i j : Fin n) :
    (X : Matrix (Fin n) (Fin n) L) i j = 1 ∨ (X : Matrix (Fin n) (Fin n) L) i j = 0 ∨
      (i = a ∧ j = m) ∨ (i = a ∧ j = a') ∨ (i = m ∧ j = a') := by
  obtain ⟨hB, hZ⟩ := hX
  rw [mem_unipB] at hB
  rcases lt_trichotomy i j with h | rfl | h
  · by_cases h1 : i < a ∨ a' < j
    · exact Or.inr (Or.inl (hZ i j h h1))
    · push_neg at h1
      simp only [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.ext_iff] at h h1 ⊢
      omega
  · exact Or.inl (hB.2 i)
  · exact Or.inr (Or.inl (hB.1 i j h))

theorem InBlock.mul_corner (ham : m.val = a.val + 1) (hma : a'.val = m.val + 1) {X Y : GL (Fin n) L}
    (hX : InBlock a a' X) (hY : InBlock a a' Y) :
    ((X * Y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' =
      (X : Matrix (Fin n) (Fin n) L) a a' + (X : Matrix (Fin n) (Fin n) L) a m * (Y : Matrix (Fin n) (Fin n) L) m a' +
        (Y : Matrix (Fin n) (Fin n) L) a a' := by
  have hXB := (mem_unipB L).1 hX.1
  have hYB := (mem_unipB L).1 hY.1
  have key : ∀ l : Fin n, (X : Matrix (Fin n) (Fin n) L) a l * (Y : Matrix (Fin n) (Fin n) L) l a' =
      (if l = a then (Y : Matrix (Fin n) (Fin n) L) a a' else 0) +
      (if l = m then (X : Matrix (Fin n) (Fin n) L) a m * (Y : Matrix (Fin n) (Fin n) L) m a' else 0) +
      (if l = a' then (X : Matrix (Fin n) (Fin n) L) a a' else 0) := by
    intro l
    by_cases h1 : l = a
    · subst h1
      have e1 : l ≠ m := fun e => by rw [Fin.ext_iff] at e; omega
      have e2 : l ≠ a' := fun e => by rw [Fin.ext_iff] at e; omega
      rw [if_pos rfl, if_neg e1, if_neg e2, hXB.2, one_mul, add_zero, add_zero]
    by_cases h2 : l = m
    · subst h2
      have e2 : l ≠ a' := fun e => by rw [Fin.ext_iff] at e; omega
      rw [if_neg h1, if_pos rfl, if_neg e2, zero_add, add_zero]
    by_cases h3 : l = a'
    · subst h3
      rw [if_neg h1, if_neg h2, if_pos rfl, hYB.2, mul_one, zero_add, zero_add]
    rw [if_neg h1, if_neg h2, if_neg h3, add_zero, add_zero]
    have hv1 : l.val ≠ a.val := fun e => h1 (Fin.ext e)
    have hv2 : l.val ≠ m.val := fun e => h2 (Fin.ext e)
    have hv3 : l.val ≠ a'.val := fun e => h3 (Fin.ext e)
    rcases Nat.lt_or_gt_of_ne hv1 with h4 | h4
    · rw [hXB.1 a l (Fin.lt_iff_val_lt_val.2 h4), zero_mul]
    · have h5 : a'.val < l.val := by omega
      rw [hYB.1 l a' (Fin.lt_iff_val_lt_val.2 h5), mul_zero]
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_congr rfl fun l _ => key l, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

end Block

end GlobalTheory.WeylCell.WeylUnipotentShell.ShellGroup

namespace GlobalTheory.WeylCell.WeylUnipotentShell.ShellGroup

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {a m a' : Fin n} {σ : L →+* L}

theorem inv_corner (harev : a.rev = a') (ha'rev : a'.rev = a) {X : GL (Fin n) L} (hX : X ∈ GU σ n) :
    ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' = σ ((X : Matrix (Fin n) (Fin n) L) a a') := by
  rw [(GlobalTheory.LGrp.mem_GU_iff σ n X).1 hX a a', ha'rev, harev]

theorem inv_mid (ha'rev : a'.rev = a) (hmrev : m.rev = m) {X : GL (Fin n) L} (hX : X ∈ GU σ n) :
    ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) m a' = σ ((X : Matrix (Fin n) (Fin n) L) a m) := by
  rw [(GlobalTheory.LGrp.mem_GU_iff σ n X).1 hX m a', ha'rev, hmrev]

theorem mid_eq (hma : a'.val = m.val + 1) (ha'rev : a'.rev = a) (hmrev : m.rev = m) {X : GL (Fin n) L}
    (hX : X ∈ GU σ n) (hB : InBlock a a' X) :
    (X : Matrix (Fin n) (Fin n) L) m a' = -σ ((X : Matrix (Fin n) (Fin n) L) a m) := by
  have e := GlobalTheory.UnipShiftU.unipB_inv_apply_succ hB.1 hma
  rw [inv_mid ha'rev hmrev hX] at e
  rw [e, neg_neg]

theorem corner_rel (ham : m.val = a.val + 1) (hma : a'.val = m.val + 1) (harev : a.rev = a') (ha'rev : a'.rev = a)
    (hmrev : m.rev = m) {X : GL (Fin n) L} (hX : X ∈ GU σ n) (hB : InBlock a a' X) (hBi : InBlock a a' X⁻¹) :
    (X : Matrix (Fin n) (Fin n) L) a m * σ ((X : Matrix (Fin n) (Fin n) L) a m) =
      -((X : Matrix (Fin n) (Fin n) L) a a' + σ ((X : Matrix (Fin n) (Fin n) L) a a')) := by
  have e := InBlock.mul_corner ham hma hB hBi
  rw [mul_inv_cancel, inv_mid ha'rev hmrev hX, inv_corner harev ha'rev hX, Units.val_one,
    Matrix.one_apply_ne (fun h => by rw [Fin.ext_iff] at h; omega)] at e
  linear_combination -e

theorem mid_sq_le (ham : m.val = a.val + 1) (hma : a'.val = m.val + 1) (harev : a.rev = a') (ha'rev : a'.rev = a)
    (hmrev : m.rev = m) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {X : GL (Fin n) L} (hX : X ∈ GU σ n)
    (hB : InBlock a a' X) (hBi : InBlock a a' X⁻¹) {e : WithZero (Multiplicative ℤ)}
    (hc : Valued.v ((X : Matrix (Fin n) (Fin n) L) a a') ≤ e) :
    Valued.v ((X : Matrix (Fin n) (Fin n) L) a m) * Valued.v ((X : Matrix (Fin n) (Fin n) L) a m) ≤ e := by
  have e1 : Valued.v ((X : Matrix (Fin n) (Fin n) L) a m) * Valued.v ((X : Matrix (Fin n) (Fin n) L) a m) =
      Valued.v ((X : Matrix (Fin n) (Fin n) L) a m * σ ((X : Matrix (Fin n) (Fin n) L) a m)) := by
    rw [map_mul, hσv]
  rw [e1, corner_rel ham hma harev ha'rev hmrev hX hB hBi, Valuation.map_neg]
  exact Valuation.map_add_le _ hc (by rw [hσv]; exact hc)

theorem entry_le (ham : m.val = a.val + 1) (hma : a'.val = m.val + 1) (harev : a.rev = a') (ha'rev : a'.rev = a)
    (hmrev : m.rev = m) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {X : GL (Fin n) L} (hX : X ∈ GU σ n)
    (hB : InBlock a a' X) (hBi : InBlock a a' X⁻¹) {e : WithZero (Multiplicative ℤ)}
    (hc : Valued.v ((X : Matrix (Fin n) (Fin n) L) a a') ≤ e) (i j : Fin n) :
    Valued.v ((X : Matrix (Fin n) (Fin n) L) i j) ≤ max 1 e := by
  have hb := le_max_one_of_mul_self_le (mid_sq_le ham hma harev ha'rev hmrev hσv hX hB hBi hc)
  rcases InBlock.entry ham hma hB i j with h | h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [h, map_one]; exact le_max_left _ _
  · rw [h, map_zero]; exact zero_le'
  · exact hb
  · exact hc.trans (le_max_right _ _)
  · rw [mid_eq hma ha'rev hmrev hX hB, Valuation.map_neg, hσv]; exact hb

theorem corner_mul_le (ham : m.val = a.val + 1) (hma : a'.val = m.val + 1) (harev : a.rev = a') (ha'rev : a'.rev = a)
    (hmrev : m.rev = m) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {X Y : GL (Fin n) L} (hX : X ∈ GU σ n)
    (hY : Y ∈ GU σ n) (hB : InBlock a a' X) (hBi : InBlock a a' X⁻¹) (hC : InBlock a a' Y) (hCi : InBlock a a' Y⁻¹)
    {e : WithZero (Multiplicative ℤ)} (hx : Valued.v ((X : Matrix (Fin n) (Fin n) L) a a') ≤ e)
    (hy : Valued.v ((Y : Matrix (Fin n) (Fin n) L) a a') ≤ e) :
    Valued.v (((X * Y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a') ≤ e := by
  rw [InBlock.mul_corner ham hma hB hC, mid_eq hma ha'rev hmrev hY hC]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ hx ?_) hy
  rw [map_mul, Valuation.map_neg, hσv]
  exact mul_le_of_mul_self_le (mid_sq_le ham hma harev ha'rev hmrev hσv hX hB hBi hx)
    (mid_sq_le ham hma harev ha'rev hmrev hσv hY hC hCi hy)

end GlobalTheory.WeylCell.WeylUnipotentShell.ShellGroup

namespace GlobalTheory.WeylCell.WeylUnipotentShell.ShellGroup

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isCompact_bounded [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (n : ℕ) (N : ℤ) :
    IsCompact {g : GL (Fin n) L | (∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) L) i j) ≤ WithZero.exp N) ∧
      ∀ i j, Valued.v (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ WithZero.exp N} := by
  have hB := isCompact_ball h N
  have hM : IsCompact {A : Matrix (Fin n) (Fin n) L | ∀ i j, A i j ∈ {x : L | Valued.v x ≤ WithZero.exp N}} := by
    have := isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin n => hB
    have e : {A : Matrix (Fin n) (Fin n) L | ∀ i j, A i j ∈ {x : L | Valued.v x ≤ WithZero.exp N}} =
        Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => {x : L | Valued.v x ≤ WithZero.exp N} :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    exact e ▸ this
  have := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) L)).isCompact_preimage
    (hM.prod (hM.image MulOpposite.continuous_op))
  convert this using 1
  ext g
  exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
    have : A = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := MulOpposite.op_injective e
    exact this ▸ hA i j⟩⟩

end GlobalTheory.WeylCell.WeylUnipotentShell.ShellGroup

namespace GlobalTheory.WeylCell.WeylUnipotentShell

open ShellGroup in

theorem shellU_open_compact_subgroup : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    (∀ j : ℤ, IsOpen (shellU k y j) ∧ IsCompact (shellU k y j) ∧ (1 : cellU y) ∈ shellU k y j ∧
      (∀ u v : cellU y, u ∈ shellU k y j → v ∈ shellU k y j → u * v ∈ shellU k y j) ∧
      (∀ u : cellU y, u ∈ shellU k y j → u⁻¹ ∈ shellU k y j)) ∧
    shellU k y 0 = (((KU σ n).subgroupOf (cellU y) : Subgroup (cellU y)) : Set (cellU y)) := by
  intro L _ _ _ ϖ σ q h n k hk hn y hyK hy
  have hA := val_rev_lo_of_last k hk hn
  have hrv : ((lo k).rev : Fin n).val = n - ((lo k).val + 1) := Fin.val_rev _
  have hlt := (lo k).isLt
  let m : Fin n := ⟨(lo k).val + 1, by omega⟩
  have ham : m.val = (lo k).val + 1 := rfl
  have hma : ((lo k).rev : Fin n).val = m.val + 1 := by rw [ham]; omega
  have harev : (lo k).rev = (lo k).rev := rfl
  have ha'rev : ((lo k).rev : Fin n).rev = lo k := Fin.rev_rev _
  have hmrev : m.rev = m := by
    ext
    rw [Fin.val_rev, ham]
    omega
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := h.2.1
  have hblk : ∀ u : cellU y, InBlock (lo k) (lo k).rev ((u : GU σ n) : GL (Fin n) L) := by
    intro u
    have := (mem_cellU_last_iff L ϖ σ q h n k hk hn y hyK hy u).1 u.2
    exact ⟨(mem_unipB L).2 ⟨this.1.1, this.1.2⟩, this.2⟩
  have hblki : ∀ u : cellU y, InBlock (lo k) (lo k).rev (((u : GU σ n) : GL (Fin n) L))⁻¹ := fun u => hblk u⁻¹
  have hG : ∀ u : cellU y, ((u : GU σ n) : GL (Fin n) L) ∈ GU σ n := fun u => (u : GU σ n).2
  have hcorner : ∀ (u : cellU y) (j : ℤ), u ∈ shellU k y j ↔
      Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤ WithZero.exp j :=
    fun u j => Iff.rfl
  have hinvS : ∀ (j : ℤ) (u : cellU y), u ∈ shellU k y j → u⁻¹ ∈ shellU k y j := by
    intro j u hu
    rw [hcorner] at hu ⊢
    show Valued.v ((((((u : GU σ n) : GL (Fin n) L))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤ _
    rw [inv_corner harev ha'rev (hG u), hσv]
    exact hu
  have hent : ∀ (j : ℤ) (u : cellU y), u ∈ shellU k y j → ∀ i l,
      Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i l) ≤ max 1 (WithZero.exp j) :=
    fun j u hu i l => entry_le ham hma harev ha'rev hmrev hσv (hG u) (hblk u) (hblki u) hu i l
  have hcont : Continuous fun u : cellU y =>
      (((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem _ _
  have hshell : ∀ j : ℤ, shellU k y j = (fun u : cellU y =>
      (((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ⁻¹'
        {x : L | Valued.v x ≤ WithZero.exp j} := fun j => rfl
  have hGc : IsClosed (GU σ n : Set (GL (Fin n) L)) :=
    isClosed_eq (((Units.continuous_val.matrix_map (GlobalTheory.LGrp.continuous_of_unramInv h)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul Units.continuous_val) continuous_const
  have hCc : IsClosed (cellU y : Set (GU σ n)) := (isClosed_cell _).preimage continuous_subtype_val
  have hι : Topology.IsClosedEmbedding fun u : cellU y => ((u : GU σ n) : GL (Fin n) L) :=
    hGc.isClosedEmbedding_subtypeVal.comp hCc.isClosedEmbedding_subtypeVal
  refine ⟨fun j => ⟨?_, ?_, ?_, ?_, hinvS j⟩, ?_⟩
  · rw [hshell]
    exact (isOpen_ball h j).preimage hcont
  · have hcl : IsClosed (shellU k y j) := by
      rw [hshell]
      exact (isClosed_ball h j).preimage hcont
    rw [hι.isInducing.isCompact_iff]
    refine (isCompact_bounded h n (max 0 j)).of_isClosed_subset (hι.isClosedMap _ hcl) ?_
    rintro _ ⟨u, hu, rfl⟩
    have hmax : max 1 (WithZero.exp j) ≤ WithZero.exp (max 0 j) :=
      max_le (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; exact le_max_left _ _)
        (WithZero.exp_le_exp.2 (le_max_right _ _))
    exact ⟨fun i l => (hent j u hu i l).trans hmax, fun i l => (hent j u⁻¹ (hinvS j u hu) i l).trans hmax⟩
  · rw [hcorner]
    show Valued.v (((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤ _
    rw [Units.val_one, Matrix.one_apply_ne (fun e => by rw [Fin.ext_iff] at e; omega), map_zero]
    exact zero_le'
  · intro u v hu hv
    rw [hcorner] at hu hv ⊢
    exact corner_mul_le ham hma harev ha'rev hmrev hσv (hG u) (hG v) (hblk u) (hblki u) (hblk v) (hblki v) hu hv
  · ext u
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, ← SetLike.mem_coe, GlobalTheory.LFun.IntPtsUnitary.coe_KU, Set.mem_preimage,
      GlobalTheory.LFun.IntPtsUnitary.coe_GLint]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, intL, Valuation.mem_integer_iff]
    constructor
    · intro hu
      have h1 := hent 0 u hu
      have h2 := hent 0 u⁻¹ (hinvS 0 u hu)
      rw [WithZero.exp_zero, max_self] at h1 h2
      exact ⟨h1, h2⟩
    · intro hu
      rw [hcorner, WithZero.exp_zero]
      exact hu.1 _ _

end GlobalTheory.WeylCell.WeylUnipotentShell

end
