import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorDependsBelowAndSmallTranslationInvaria
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorVanishesUnlessLastRowBounded

noncomputable section

open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.StairDepth

variable {k : Type} [Field k] {G : Grid k}

variable (G) in

def wt (ϖ : kˣ) (e : ℕ) (X : ℕ × ℕ) (a : ℕ) : kˣ :=
  if X.1 = G.m ∧ X.2 + 2 ≤ G.m then ϖ ^ (e * (a + 1 - topRank G X.2)) else 1

variable (G) in

def dg (ϖ : kˣ) (e : ℕ) : G.VertexGroup := fun X => diagGL fun a : Fin (G.rank X) => wt G ϖ e X a

theorem wt_core (ϖ : kˣ) (e : ℕ) (X : ℕ × ℕ) {a : ℕ} (ha : a < topRank G X.2) : wt G ϖ e X a = 1 := by
  unfold wt
  split_ifs
  · rw [show a + 1 - topRank G X.2 = 0 by omega]
    simp
  · rfl

theorem wt_end (ϖ : kˣ) (e : ℕ) {i j : ℕ} (h : G.m < j + 2) (a : ℕ) : wt G ϖ e (i, j) a = 1 := by
  unfold wt
  rw [if_neg]
  rintro ⟨-, h2⟩
  dsimp only at h2
  omega

theorem moveArgs_apply (ϖ : kˣ) (e : ℕ) (z : G.Args) (b : Edge) (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)) :
    G.moveArgs .one (dg G ϖ e) z b r s = (wt G ϖ e b.tgt r : k) * z b r s * ((wt G ϖ e b.src s)⁻¹ : kˣ) := by
  simp only [Grid.moveArgs, Assignment.read, dg]
  change ((diagonal fun a : Fin (G.rank b.tgt) => (wt G ϖ e b.tgt a : k))ᵀ * z b *
    (diagonal fun a : Fin (G.rank b.src) => (((wt G ϖ e b.src a)⁻¹ : kˣ) : k))ᵀ) r s = _
  rw [diagonal_transpose, diagonal_transpose, mul_diagonal, diagonal_mul]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem elt_eq [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ G.s) (J : G.Level) (ϖ : kˣ) (e : ℕ) (hm : 2 ≤ G.m) :
    (Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) = dg G ϖ e := by
  have hd1 : ∀ X : ℕ × ℕ, ¬ (X.1 = G.m ∧ X.2 + 2 ≤ G.m) → dg G ϖ e X = 1 := by
    intro X hX
    apply Units.ext
    ext a b
    simp [dg, diagGL, wt, hX, Matrix.one_apply, Matrix.diagonal_apply]
  funext X
  obtain ⟨i, j⟩ := X
  by_cases hc : i = G.m ∧ j + 2 ≤ G.m
  · obtain ⟨rfl, hj⟩ := hc
    rw [through_elt _ hj]
    apply Units.ext
    ext a b
    simp [stair, dg, diagGL, wt, hj]
  · rw [hd1 _ hc]
    by_cases hi : i = G.m
    · subst hi
      have hj : G.m < j + 2 := by
        simp only [true_and] at hc
        omega
      obtain _ | j := j
      · omega
      · simp only [Reps.elt, onColumn_apply]
        rw [dif_neg (by omega)]
    · simp only [Reps.elt, onColumn]
      rw [dif_neg hi]

theorem val_wt_le {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (X : ℕ × ℕ) (a : ℕ) : valuation k (wt G ϖ e X a : k) ≤ 1 := by
  unfold wt
  split_ifs
  · simpa using val_pow_anti hϖ (Nat.zero_le (e * (a + 1 - topRank G X.2)))
  · simp

theorem moved_supp {ϖ : kˣ} {e : ℕ}
    {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool) {z : G.Args}
    (hz : moved G keep (dg G ϖ e) T z ≠ 0) {b : Edge} (hb : b ∈ oppositePath G.m) (r : Fin (G.rank b.tgt))
    (s : Fin (G.rank b.src)) :
    valuation k ((wt G ϖ e b.tgt r : k) * z b r s * ((wt G ϖ e b.src s)⁻¹ : kˣ)) ≤ 1 := by
  have hT0 : T (G.moveArgs .one (dg G ϖ e) z) ≠ 0 := by
    intro h0; apply hz; simp [moved, Grid.pathAct, h0]
  have hint : G.moveArgs .one (dg G ϖ e) z b ∈ matLat _ (SplitFlip.stdLat k _) := by
    by_contra hc; exact hT0 (hT.2.1 _ b hb hc)
  rw [← moveArgs_apply]
  exact mem_matLat_stdLat.1 hint r s

theorem moved_per {ϖ : kˣ} {e : ℕ}
    {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool) (z z' : G.Args)
    (hδ : ∀ b ∈ oppositePath G.m, ∀ (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)),
      valuation k ((wt G ϖ e b.tgt r : k) * (z' - z) b r s * ((wt G ϖ e b.src s)⁻¹ : kˣ)) ≤
        valuation k ((ϖ ^ e : kˣ) : k)) :
    moved G keep (dg G ϖ e) T z' = moved G keep (dg G ϖ e) T z := by
  have key : T (G.moveArgs .one (dg G ϖ e) z') = T (G.moveArgs .one (dg G ϖ e) z) := by
    let d : G.Args := fun b => if b ∈ oppositePath G.m then
      G.moveArgs .one (dg G ϖ e) z' b - G.moveArgs .one (dg G ϖ e) z b else 0
    have h1 : T (G.moveArgs .one (dg G ϖ e) z + d) = T (G.moveArgs .one (dg G ϖ e) z) := by
      apply hT.2.2
      intro b
      rw [FourierDepth.mem_matLat_smul_stdLat]
      intro r s
      by_cases hb : b ∈ oppositePath G.m
      · simp only [d, if_pos hb, Matrix.sub_apply, moveArgs_apply]
        convert hδ b hb r s using 2
        simp only [Pi.sub_apply, Matrix.sub_apply]
        ring
      · simp [d, hb]
    rw [← h1]
    apply hT.1
    intro b hb
    have hb' : b ∈ oppositePath G.m := hb
    simp [d, hb']
  simp only [moved, Grid.pathAct, key]

variable (hs : 1 ≤ G.s)

private theorem lt_of_frame_symm_eq_inl {p c m : ℕ} (h : p + c = m) (i : Fin m) (q : Fin p)
    (hq : (frame h).symm i = Sum.inl q) : (i : ℕ) < p := by
  have hi : i = frame h (Sum.inl q) := by
    rw [← hq]
    simp
  rw [hi]
  simp [frame]

private theorem lt_and_lt_of_fromBlocks_frame_ne_zero {p q c d m n : ℕ} (A : Matrix (Fin p) (Fin q) k) (h1 : p + c = m) (h2 : q + d = n)
    (s : Fin m) (r : Fin n)
    (hne : fromBlocks A 0 0 (0 : Matrix (Fin c) (Fin d) k) ((frame h1).symm s) ((frame h2).symm r) ≠ 0) :
    (s : ℕ) < p ∧ (r : ℕ) < q := by
  rcases hs' : (frame h1).symm s with s' | s' <;> rcases hr' : (frame h2).symm r with r' | r' <;>
    rw [hs', hr'] at hne <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply,
      ne_eq, not_true_eq_false] at hne
  exact ⟨lt_of_frame_symm_eq_inl h1 s s' hs', lt_of_frame_symm_eq_inl h2 r r' hr'⟩

theorem fill_sub_wt_le (ϖ : kˣ) (e : ℕ) {x a : ColArgs G} {y b : RowArgs G} {t : ValueGroupWithZero k}
    (ha : ∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ t) (hb : ∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ t)
    (u : Vars G) {c : Edge} (hc : c ∈ oppositePath G.m) (r : Fin (G.rank c.tgt)) (s : Fin (G.rank c.src)) :
    valuation k ((wt G ϖ e c.tgt r : k) * (fill hs (x + a) (y + b) u - fill hs x y u) c r s *
      ((wt G ϖ e c.src s)⁻¹ : kˣ)) ≤ t := by
  have key : ∀ (r : Fin (G.rank c.tgt)) (s : Fin (G.rank c.src)),
      (fill hs (x + a) (y + b) u - fill hs x y u) c r s ≠ 0 →
        wt G ϖ e c.tgt r = 1 ∧ wt G ϖ e c.src s = 1 := by
    rcases FlatDep.mem_opp hc with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · intro r s _
      exact ⟨wt_end (G := G) ϖ e (i := i + 1) (j := G.m) (by omega) _,
        wt_end (G := G) ϖ e (i := i) (j := G.m) (by omega) _⟩
    · by_cases hjm : j < G.m - 1
      · show ∀ (r : Fin (G.rank (G.m, j))) (s : Fin (G.rank (G.m, j + 1))),
          (fill hs (x + a) (y + b) u - fill hs x y u) (Edge.theta G.m j) r s ≠ 0 →
            wt G ϖ e (G.m, j) r = 1 ∧ wt G ϖ e (G.m, j + 1) s = 1
        intro r s hne
        rw [Pi.sub_apply, fill_theta, fill_theta, Matrix.sub_apply, Matrix.transpose_apply,
          Matrix.transpose_apply] at hne
        simp only [downMap, dif_pos hjm, Pi.add_apply, FlatDep.stepPt_add, Matrix.reindex_apply,
          Matrix.submatrix_apply] at hne
        rw [Matrix.add_apply, add_sub_cancel_left] at hne
        obtain ⟨hs1, hr1⟩ := lt_and_lt_of_fromBlocks_frame_ne_zero _ _ _ s r hne
        exact ⟨wt_core ϖ e (G.m, j) hr1, wt_core ϖ e (G.m, j + 1) hs1⟩
      · intro r s _
        exact ⟨wt_end (G := G) ϖ e (i := G.m) (j := j) (by omega) _,
          wt_end (G := G) ϖ e (i := G.m) (j := j + 1) (by omega) _⟩
  by_cases hD : (fill hs (x + a) (y + b) u - fill hs x y u) c r s = 0
  · rw [hD, mul_zero, zero_mul, map_zero]
    exact zero_le'
  · obtain ⟨h1, h2⟩ := key r s hD
    rw [h1, h2]
    simp only [Units.val_one, inv_one, one_mul, mul_one]
    exact FlatDep.fill_sub_le hs ha hb u hc r s

theorem colVar_le {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool)
    {x : ColArgs G} {y : RowArgs G} {u : Vars G} (hz : moved G keep (dg G ϖ e) T (fill hs x y u) ≠ 0)
    (j : Fin (G.m - 1)) (hj : (j : ℕ) + 2 = G.m) (r : Fin (topRank G (j + 1))) :
    valuation k (((ϖ ^ e : kˣ) : k) * colVar x u j r) ≤ 1 := by
  have hjm : (j : ℕ) < G.m - 1 := by omega
  have hb : Edge.theta G.m j ∈ oppositePath G.m := FlatDep.mem_opp_theta (by omega)
  have e1 := topRank_add hs (j : ℕ)
  have e2 := topRank_add hs ((j : ℕ) + 1)
  have h2 : topRank G j + (G.m - 2 - j + 1) = G.rank (G.m, j) := by omega
  have h1 : topRank G (j + 1) + (G.m - 2 - j) = G.rank (G.m, j + 1) := by omega
  have hm := moved_supp hT keep hz hb (frame h2 (Sum.inr ⟨0, by omega⟩)) (frame h1 (Sum.inl r))
  rw [fill_theta, Matrix.transpose_apply] at hm
  simp only [downMap, dif_pos hjm, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at hm
  have hw1 : wt G ϖ e (G.m, (j : ℕ)) (topRank G j) = ϖ ^ e := by
    unfold wt
    rw [if_pos ⟨rfl, by omega⟩]
    simp
  have hw2 : wt G ϖ e (G.m, (j : ℕ) + 1) r = 1 := wt_core ϖ e _ r.isLt
  simp only [frame, Equiv.trans_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply,
    Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, add_zero] at hm
  rw [hw1, hw2] at hm
  simp only [Units.val_one, inv_one, mul_one] at hm
  simp only [colVar]
  convert hm using 4
  congr 1
  apply Fin.ext
  show (G.m - 2 - (j : ℕ)) / 2 = 0
  omega

private theorem lt_of_frame_entry_ne_zero_of_inr_zero {p c m : ℕ} {n' : Type} (h : p + c = m) (s : Fin m) (col : n')
    (M : Matrix (Fin p ⊕ Fin c) n' k) (hM : ∀ l col, M (Sum.inr l) col = 0)
    (hne : M ((frame h).symm s) col ≠ 0) : (s : ℕ) < p := by
  rcases hq : (frame h).symm s with q | q
  · exact lt_of_frame_symm_eq_inl h s q hq
  · rw [hq, hM] at hne
    exact absurd rfl hne

theorem shift_wt_le {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (x : ColArgs G) (y : RowArgs G) (u : Vars G) (j₀ : Fin (G.m - 1))
    (hj₀ : (j₀ : ℕ) + 2 = G.m) (q : ℕ) {t s₀ : k} (ht : valuation k t ≤ valuation k s₀)
    {c : Edge} (hc : c ∈ oppositePath G.m) (r : Fin (G.rank c.tgt)) (s : Fin (G.rank c.src)) :
    valuation k ((wt G ϖ e c.tgt r : k) * (fill hs x y (u + FlatLast.shiftVar j₀ q t) - fill hs x y u) c r s *
      ((wt G ϖ e c.src s)⁻¹ : kˣ)) ≤ valuation k s₀ := by
  have key : ∀ (r : Fin (G.rank c.tgt)) (s : Fin (G.rank c.src)),
      (fill hs x y (u + FlatLast.shiftVar j₀ q t) - fill hs x y u) c r s ≠ 0 → wt G ϖ e c.src s = 1 := by
    rcases FlatDep.mem_opp hc with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · intro r s _
      exact wt_end (G := G) ϖ e (i := i) (j := G.m) (by omega) _
    · by_cases hjm : j < G.m - 1
      · show ∀ (r : Fin (G.rank (G.m, j))) (s : Fin (G.rank (G.m, j + 1))),
          (fill hs x y (u + FlatLast.shiftVar j₀ q t) - fill hs x y u) (Edge.theta G.m j) r s ≠ 0 →
            wt G ϖ e (G.m, j + 1) s = 1
        intro r s hne
        rw [Pi.sub_apply, fill_theta, fill_theta, Matrix.sub_apply, Matrix.transpose_apply,
          Matrix.transpose_apply] at hne
        simp only [downMap, dif_pos hjm, Matrix.reindex_apply, Matrix.submatrix_apply] at hne
        rw [← Matrix.sub_apply] at hne
        have hlt := lt_of_frame_entry_ne_zero_of_inr_zero _ s _ _ (by
          intro l col
          simp [stepPt, basePt, FlatLast.shiftVar]) hne
        exact wt_core ϖ e (G.m, j + 1) hlt
      · intro r s _
        exact wt_end (G := G) ϖ e (i := G.m) (j := j + 1) (by omega) _
  by_cases hD : (fill hs x y (u + FlatLast.shiftVar j₀ q t) - fill hs x y u) c r s = 0
  · rw [hD, mul_zero, zero_mul, map_zero]
    exact zero_le'
  · rw [key r s hD]
    simp only [inv_one, Units.val_one, mul_one]
    rw [map_mul]
    calc valuation k (wt G ϖ e c.tgt r : k) *
          valuation k ((fill hs x y (u + FlatLast.shiftVar j₀ q t) - fill hs x y u) c r s)
        ≤ 1 * valuation k s₀ :=
          mul_le_mul' (val_wt_le hϖ e _ _)
            (FlatLast.valuation_fill_sub_le hs x y u _ (FlatLast.valuation_shiftVar_le j₀ q ht) c r s)
      _ = valuation k s₀ := one_mul _

variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)

private theorem valuation_sum_colVar_even_le_one {ϖ : kˣ} {e : ℕ} (x a : ColArgs G) (u : Vars G)
    (ha : ∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ valuation k ((ϖ ^ e : kˣ) : k))
    (hc : ∀ (j : Fin (G.m - 1)), (j : ℕ) + 2 = G.m → ∀ r,
      valuation k (((ϖ ^ e : kˣ) : k) * colVar x u j r) ≤ 1) :
    valuation k (∑ j : Fin (G.m - 1), if Even (G.m - 2 - ↑j) then
      ∑ r, (if ↑j + 1 < G.m - 1 then 0 else a (↑j + 1) (topLast G (↑j + 1 + 1)) r) * colVar x u j r
      else 0) ≤ 1 := by
  apply Valuation.map_sum_le
  intro j _
  have hjlt := j.isLt
  by_cases hev : Even (G.m - 2 - ↑j)
  · rw [if_pos hev]
    apply Valuation.map_sum_le
    intro r _
    by_cases hj : (j : ℕ) + 1 < G.m - 1
    · rw [if_pos hj, zero_mul, map_zero]
      exact zero_le'
    · have hj2 : (j : ℕ) + 2 = G.m := by omega
      rw [if_neg hj, map_mul]
      have h1 := ha (j + 1) (by omega) (topLast G (↑j + 1 + 1)) r
      have h2 := hc j hj2 r
      rw [map_mul] at h2
      exact le_trans (mul_le_mul' h1 le_rfl) h2
  · rw [if_neg hev, map_zero]
    exact zero_le'

private theorem addChar_neg_add_eq_of_conductor_one (hψ : HasConductor ψ 1) (p E : k) (hE : valuation k E ≤ 1) :
    ψ (-(p + E)) = ψ (-p) := by
  rw [neg_add, AddChar.map_add_eq_mul,
    (hψ 1).mpr (by simp) (-E) (by rw [Valuation.map_neg]; simpa using hE), mul_one]

theorem flat_per {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hψ : HasConductor ψ 1) (hT : G.IsTensor ϖ e (oppositePath G.m) T)
    (keep : Bool) (x a : ColArgs G) (y b : RowArgs G)
    (ha : ∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ valuation k ((ϖ ^ e : kˣ) : k))
    (hb : ∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ valuation k ((ϖ ^ e : kˣ) : k)) :
    flatTensor hs ψ ν (moved G keep (dg G ϖ e) T) (x + a) (y + b) = flatTensor hs ψ ν (moved G keep (dg G ϖ e) T) x y := by
  unfold flatTensor
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [flatIntegrand]
  have hper : moved G keep (dg G ϖ e) T (fill hs (x + a) (y + b) u) =
      moved G keep (dg G ϖ e) T (fill hs x y u) :=
    moved_per hT keep _ _ (fun c hc r s => fill_sub_wt_le hs ϖ e ha hb u hc r s)
  rw [hper]
  by_cases hz : moved G keep (dg G ϖ e) T (fill hs x y u) = 0
  · rw [hz, zero_mul, zero_mul]
  · have hE := valuation_sum_colVar_even_le_one x a u ha (fun j hj r => colVar_le hs hT keep hz j hj r)
    rw [FlatDep.phase_add, addChar_neg_add_eq_of_conductor_one ψ hψ _ _ hE]

theorem flat_supp {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool)
    (x : ColArgs G) (y : RowArgs G) (hne : flatTensor hs ψ ν (moved G keep (dg G ϖ e) T) x y ≠ 0) :
    (∀ j, j < G.m → ∀ r s, (j + 1 = G.m → r ≠ topLast G (j + 1)) → valuation k (x j r s) ≤ 1) ∧
      ∀ i, i < G.m → ∀ r s, valuation k (y i r s) ≤ 1 := by
  have hex : ∃ u, moved G keep (dg G ϖ e) T (fill hs x y u) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hne
    unfold flatTensor
    simp [flatIntegrand, hall]
  obtain ⟨u, hu⟩ := hex
  constructor
  · intro j hj r s hr
    have hb := FlatDep.mem_opp_theta (G := G) hj
    have e1 := topRank_add hs j
    have e2 := topRank_add hs (j + 1)
    by_cases hjm : j < G.m - 1
    · have h2 : topRank G j + (G.m - 2 - j + 1) = G.rank (G.m, j) := by omega
      have h1 : topRank G (j + 1) + (G.m - 2 - j) = G.rank (G.m, j + 1) := by omega
      have hm := moved_supp hT keep hu hb (frame h2 (Sum.inl s)) (frame h1 (Sum.inl r))
      rw [fill_theta, Matrix.transpose_apply] at hm
      simp only [downMap, dif_pos hjm, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply] at hm
      simp only [frame, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply,
        Fin.coe_cast, Fin.coe_castAdd] at hm
      rw [wt_core ϖ e (G.m, j) s.isLt, wt_core ϖ e (G.m, j + 1) r.isLt] at hm
      simpa [stepPt, basePt, Free, Kept] using hm
    · have hj1 : j + 1 = G.m := by omega
      have hrne : (r : ℕ) ≠ topRank G (j + 1) - 1 := fun h => hr hj1 (Fin.ext h)
      have hrl : (r : ℕ) < G.rank (G.m, j + 1) := by
        have := r.isLt
        omega
      have hsl : (s : ℕ) < G.rank (G.m, j) := by
        have := s.isLt
        omega
      have hm := moved_supp hT keep hu hb ⟨s, hsl⟩ ⟨r, hrl⟩
      rw [fill_theta, Matrix.transpose_apply] at hm
      simp only [downMap, dif_neg hjm, dif_pos hj1, Matrix.submatrix_apply] at hm
      rw [wt_end (G := G) ϖ e (i := G.m) (j := j) (by omega),
        wt_end (G := G) ϖ e (i := G.m) (j := j + 1) (by omega)] at hm
      simpa using hm
  · intro i hi r s
    have hb : Edge.ex i G.m ∈ oppositePath G.m := by
      simp [oppositePath, hi]
    have hm := moved_supp hT keep hu hb s r
    rw [fill_ex, Matrix.transpose_apply, wt_end (G := G) ϖ e (i := i + 1) (j := G.m) (by omega),
      wt_end (G := G) ϖ e (i := i) (j := G.m) (by omega)] at hm
    simpa using hm

theorem flat_last [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1)
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool) (x : ColArgs G) (y : RowArgs G)
    (hF : flatTensor hs ψ ν (moved G keep (dg G ϖ e) T) x y ≠ 0) (j₀ : Fin (G.m - 1)) (hj₀ : (j₀ : ℕ) + 2 = G.m)
    (r : Fin (topRank G ((j₀ : ℕ) + 1))) :
    valuation k (x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r) ≤ valuation k (((ϖ ^ e)⁻¹ : kˣ) : k) := by
  obtain ⟨hsc, ht2⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI := hsc
  haveI := ht2
  haveI : SigmaFinite ν := inferInstance
  haveI hinv : (varsVol G ν).IsAddRightInvariant := by
    unfold varsVol
    infer_instance
  by_contra hlt
  push_neg at hlt
  set X := x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r with hX
  have hnot : X ∉ cball ((1 : kˣ) * (ϖ ^ e)⁻¹) := by
    simp only [cball, Set.mem_setOf_eq, one_mul, not_le]
    exact hlt
  obtain ⟨t, ht, hψt⟩ := hψ.exists_ne_one (ϖ ^ e) hnot
  have hneg : valuation k (-t) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
    rw [Valuation.map_neg]
    exact ht
  have hshift : flatTensor hs ψ ν (moved G keep (dg G ϖ e) T) x y =
      ((ψ (-(X * -t)) : Circle) : ℂ) * flatTensor hs ψ ν (moved G keep (dg G ϖ e) T) x y := by
    unfold flatTensor
    calc ∫ u, flatIntegrand hs ψ (moved G keep (dg G ϖ e) T) x y u ∂varsVol G ν
        = ∫ u, flatIntegrand hs ψ (moved G keep (dg G ϖ e) T) x y (u + FlatLast.shiftVar j₀ r (-t))
            ∂varsVol G ν := (integral_add_right_eq_self _ _).symm
      _ = ∫ u, ((ψ (-(X * -t)) : Circle) : ℂ) * flatIntegrand hs ψ (moved G keep (dg G ϖ e) T) x y u
            ∂varsVol G ν := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          simp only [flatIntegrand]
          rw [moved_per hT keep (fill hs x y u) (fill hs x y (u + FlatLast.shiftVar j₀ r (-t)))
            (fun c hc r' s' => shift_wt_le hs hϖ e x y u j₀ hj₀ r hneg hc r' s')]
          rw [FlatLast.phase_shift x u j₀ hj₀ r (-t)]
          have hrow : rowVar x u ((j₀ : ℕ) + 1) r = X := by
            unfold rowVar
            rw [dif_neg (by omega)]
          rw [hrow, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
          ring
      _ = _ := MeasureTheory.integral_const_mul _ _
  have h1 : ((ψ (-(X * -t)) : Circle) : ℂ) = 1 := (mul_eq_right₀ hF).mp hshift.symm
  apply hψt
  have h3 : -(X * -t) = t * X := by ring
  rw [← h3]
  exact Circle.ext h1

theorem isSBArgs_stair [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hm : 2 ≤ G.m) (hϖ : IsUnif ϖ)
    (hψ : HasConductor ψ 1) (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool) :
    IsSBArgs G ϖ e (flatTensor hs ψ ν (moved G keep (dg G ϖ e) T)) := by
  have h1 : (1 : ValueGroupWithZero k) ≤ valuation k (((ϖ ^ e)⁻¹ : kˣ) : k) := by
    simpa using val_inv_pow_mono hϖ (Nat.zero_le e)
  refine ⟨(GlobalTheory.T.flatTensor_depends_below_and_small_translation_invariant G hs ψ ν ϖ e T keep _ hϖ hψ hT).1, fun x y a b ha hb => flat_per hs ψ ν hψ hT keep x a y b ha hb,
    fun x y hxy => ⟨fun j hj r s => ?_, fun i hi r s => ((flat_supp hs ψ ν hT keep x y hxy).2 i hi r s).trans h1⟩⟩
  by_cases hr : j + 1 = G.m ∧ r = topLast G (j + 1)
  · obtain ⟨h2, rfl⟩ := hr
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact flat_last hs ψ ν hϖ hψ hT keep x y hxy ⟨j, by omega⟩ (by simp only; omega) s
  · exact ((flat_supp hs ψ ν hT keep x y hxy).1 j hj r s fun h h' => hr ⟨h, h'⟩).trans h1

end GlobalTheory.StairDepth

end
