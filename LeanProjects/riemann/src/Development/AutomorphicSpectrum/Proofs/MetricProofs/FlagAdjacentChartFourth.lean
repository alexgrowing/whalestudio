import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBlockDiagMapGenBlock
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSecondStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartThirdStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Read

section Minors

variable {N : ℕ}

theorem minor_self_of_lowerUni {X : Matrix (Fin N) (Fin N) ℂ} (hX : IsLowerUni X) (C : Finset (Fin N)) :
    minorIJ X C C = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, det_of_lowerTriangular (X.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)) fun a b e =>
    hX.2 _ _ ((C.orderEmbOfFin rfl).strictMono (show a < b from e))]
  exact Finset.prod_eq_one fun a _ => hX.1 _

theorem minor_insert_of_lowerUni {X : Matrix (Fin N) (Fin N) ℂ} (hX : IsLowerUni X) {C : Finset (Fin N)} {a b : Fin N}
    (hb : b ∈ C) (htop : ∀ c ∈ C, c ≤ b) (hab : b < a) : minorIJ X (insert a (C.erase b)) C = X a b := by
  have ha : a ∉ C.erase b := fun h => absurd (htop a (Finset.mem_of_mem_erase h)) (not_le.2 hab)
  have hcard : (insert a (C.erase b)).card = C.card := by
    rw [Finset.card_insert_of_notMem ha, Finset.card_erase_of_mem hb]
    have := Finset.card_pos.2 ⟨b, hb⟩
    omega
  have hfm : ∀ r, C.orderEmbOfFin rfl r ∈ C := fun r => Finset.orderEmbOfFin_mem _ _ _
  let g : Fin C.card → Fin N := fun r => if C.orderEmbOfFin rfl r = b then a else C.orderEmbOfFin rfl r
  have hne : ∀ r s, r < s → C.orderEmbOfFin rfl r ≠ b := fun r s hrs =>
    (((C.orderEmbOfFin rfl).strictMono hrs).trans_le (htop _ (hfm s))).ne
  have hgr : ∀ r s, r < s → g r = C.orderEmbOfFin rfl r := fun r s hrs => if_neg (hne r s hrs)
  have hg : StrictMono g := fun r s hrs => by
    rw [hgr r s hrs]
    have h1 := (C.orderEmbOfFin rfl).strictMono hrs
    by_cases e : C.orderEmbOfFin rfl s = b
    · show _ < ite _ _ _
      rw [if_pos e]
      exact (h1.trans_le (htop _ (hfm s))).trans hab
    · show _ < ite _ _ _
      rw [if_neg e]
      exact h1
  have hmem : ∀ r, g r ∈ insert a (C.erase b) := fun r => by
    by_cases e : C.orderEmbOfFin rfl r = b
    · show ite _ _ _ ∈ _
      rw [if_pos e]
      exact Finset.mem_insert_self _ _
    · show ite _ _ _ ∈ _
      rw [if_neg e]
      exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨e, hfm r⟩)
  have hu := Finset.orderEmbOfFin_unique hcard hmem hg
  unfold minorIJ
  rw [dif_pos hcard, ← hu, det_of_lowerTriangular (X.submatrix g (C.orderEmbOfFin rfl)) fun r s e => by
    have hrs : r < s := e
    show X (g r) _ = 0
    rw [hgr r s hrs]
    exact hX.2 _ _ ((C.orderEmbOfFin rfl).strictMono hrs)]
  obtain ⟨r₀, hr₀⟩ : b ∈ Set.range (C.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hb
  rw [Finset.prod_eq_single r₀]
  · show X (ite _ _ _) _ = _
    rw [if_pos hr₀, hr₀]
  · intro r _ hr
    have e : C.orderEmbOfFin rfl r ≠ b := fun e => hr ((C.orderEmbOfFin rfl).injective (e.trans hr₀.symm))
    show X (ite _ _ _) _ = _
    rw [if_neg e]
    exact hX.1 _
  · simp

theorem mul_elem_apply (L : Matrix (Fin N) (Fin N) ℂ) (ca cb : Fin N) (t : ℂ) (a b : Fin N) :
    (L * (1 + Matrix.single cb ca t)) a b = L a b + if b = ca then L a cb * t else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  rw [Matrix.mul_apply, Finset.sum_eq_single cb]
  · by_cases e : b = ca
    · subst e
      simp
    · simp [e, Matrix.single_apply, Ne.symm e]
  · intro c _ hc
    simp [Matrix.single_apply, Ne.symm hc]
  · simp

variable {j : ℕ}

theorem mul_elem_lower {L : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) (hd : IsBlockDiag j L) {ca cb : Fin N}
    (hlt : ca < cb) (hblk : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j)) (t : ℂ) :
    IsLowerUni (L * (1 + Matrix.single cb ca t)) ∧ IsBlockDiag j (L * (1 + Matrix.single cb ca t)) := by
  refine ⟨⟨fun a => ?_, fun a b hab => ?_⟩, fun a b hab => ?_⟩
  · rw [mul_elem_apply, hL.1]
    split_ifs with e
    · subst e
      rw [hL.2 _ _ hlt, zero_mul, add_zero]
    · rw [add_zero]
  · rw [mul_elem_apply, hL.2 _ _ hab]
    split_ifs with e
    · subst e
      rw [hL.2 _ _ (hab.trans hlt), zero_mul, add_zero]
    · rw [add_zero]
  · rw [mul_elem_apply, hd a b hab]
    split_ifs with e
    · subst e
      rw [hd a cb fun e' => hab (e'.trans hblk.symm), zero_mul, add_zero]
    · rw [add_zero]

theorem lowMat_lowerUni {Ψ : Type} (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : IsLowerUni (lowMat c τ) :=
  ⟨fun _ => (dif_neg fun e => lt_irrefl _ e.1).trans (if_pos rfl),
    fun _ _ h => (dif_neg fun e => lt_asymm h e.1).trans (if_neg h.ne)⟩

theorem lowMat_blockDiag {Ψ : Type} (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : IsBlockDiag j (lowMat c τ) := fun a b h =>
  (dif_neg fun e => h e.2).trans (if_neg fun e => h (by rw [e]))

theorem stepOf_val (N j : ℕ) (c : Fin N) :
    (stepOf N j c : ℕ) = if N - j ≤ (c : ℕ) then (c : ℕ) - (N - j) else (c : ℕ) + j := rfl

theorem stepOf_mem (hj : j ≤ N) (c : Fin N) : c ∈ stepCols N j (stepOf N j c) := by
  have := c.2
  have hv := stepOf_val N j c
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs at hv ⊢ <;> omega

theorem stepOf_top (hj : j ≤ N) (c d : Fin N) (hd : d ∈ stepCols N j (stepOf N j c)) : d ≤ c := by
  have := c.2
  have := d.2
  have hv := stepOf_val N j c
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  rw [Fin.le_def]
  split_ifs at hv hd <;> omega

theorem stepOf_proper (hj : j ≤ N) {a b : Fin N} (hlt : b < a) (hblk : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) :
    IsProperStep N j (stepOf N j b) := by
  have := a.2
  have := b.2
  have h : (b : ℕ) < a := hlt
  have hv := stepOf_val N j b
  simp only [IsProperStep]
  split_ifs at hv <;> omega

end Minors

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

theorem pluck_eq {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {zb : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb)) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) {z : (Σ k, ι k) → ℂ} {H : Matrix (Fin N) (Fin N) ℂ} (hH : IsBlockDiag j H)
    (hz : ∀ m : ι k, z ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ H I (stepCols N j p.2))
    {I : Finset (Fin N)} (hI : IsStepRows N j p.2 I) :
    pluck M F zb k z I = minorIJ H I (stepCols N j p.2) := by
  let val := GlobalTheory.CompanionTheory.Ar.PB.CPts.regVal hzb
  let uA : (Σ k, ι k) → Finset (Fin N) → GlobalTheory.CompanionTheory.Ar.PB.CPts.regRing M.x zb :=
    fun q I => ⟨F.u q I, GlobalTheory.CompanionTheory.Ar.PB.ValRing.exists_isValueAt hzb (hG.2.1 q I).1⟩
  let vA : Finset (Fin N) → (Σ k, ι k) → GlobalTheory.CompanionTheory.Ar.PB.CPts.regRing M.x zb :=
    fun I q => ⟨F.u' I q, GlobalTheory.CompanionTheory.Ar.PB.ValRing.exists_isValueAt hzb (hG.2.1 q I).2⟩
  have rel : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb * valAt M.x (F.u ⟨k, m⟩ I') zb = if I = I' then 1 else 0 := fun I' hI' => by
    have e : ∑ m : ι k, vA I ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I = I' then 1 else 0 := by
      apply Subtype.ext
      have := hF.2.2.1 p k hp I I' hI hI'
      split_ifs at this ⊢ <;> simpa [uA, vA] using this
    have e' := congrArg val e
    rw [map_sum] at e'
    simp only [map_mul] at e'
    refine e'.trans ?_
    split_ifs <;> simp
  unfold pluck
  simp_rw [hz, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_eq_single I]
  · simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, rel I hI, if_pos rfl, one_mul]
  · intro I' _ hne
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    by_cases hs : IsStepRows N j p.2 I'
    · rw [rel I' hs, if_neg (Ne.symm hne), zero_mul]
    · rw [minorIJ_block_zero hH hs, mul_zero]
  · simp

theorem twMinor_eq {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {zb : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb)) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) {z : (Σ k, ι k) → ℂ} {H : Matrix (Fin N) (Fin N) ℂ} (hH : IsBlockDiag j H)
    (hz : ∀ m : ι k, z ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ H I (stepCols N j p.2))
    (g : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)) :
    twMinor M F zb p.2 k g z J = minorIJ (g * H) J (stepCols N j p.2) := by
  unfold twMinor
  rw [minorIJ_mul_sum, Finset.sum_congr rfl fun I hI => by
    rw [pluck_eq M hF hzb hG hp hH hz (Finset.mem_filter.1 hI).2]]
  exact Finset.sum_subset (Finset.filter_subset _ _) fun I _ hI => by
    rw [minorIJ_block_zero hH fun h => hI (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩), mul_zero]

theorem twMinor_self {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {zb : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb)) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) {z : (Σ k, ι k) → ℂ} {g X : Matrix (Fin N) (Fin N) ℂ} (hg : IsBlockDiag j g)
    (hd : g.det ≠ 0) (hX : IsLowerUni X) (hXd : IsBlockDiag j X)
    (hz : ∀ m : ι k, z ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ (g * X) I (stepCols N j p.2)) :
    twMinor M F zb p.2 k g⁻¹ z (stepCols N j p.2) = 1 := by
  rw [twMinor_eq M hF hzb hG hp (hg.mul hXd) hz, Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.2 hd),
    minor_self_of_lowerUni hX]

theorem lowRead_eq {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {zb : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb)) {h : Ψ → Matrix (Fin N) (Fin N) ℂ}
    {τ' : Ψ} (hg : IsBlockDiag j (h τ')) (hd : (h τ').det ≠ 0) {X : Matrix (Fin N) (Fin N) ℂ} (hX : IsLowerUni X)
    (hXd : IsBlockDiag j X) {a' b' : Fin N} (hlt : b' < a') (hblk : ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j))
    {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, M.blk (τ', stepOf N j b') = some k → ∀ m : ι k, z ⟨k, m⟩ =
      ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ (h τ' * X) I (stepCols N j (stepOf N j b'))) :
    lowRead M F zb h z τ' a' b' = X a' b' := by
  have hpr := stepOf_proper M.j_le hlt hblk
  obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', stepOf N j b') = some k := by
    rcases e : M.blk (τ', stepOf N j b') with _ | k
    · exact absurd hpr ((M.blk_none _).1 e)
    · exact ⟨k, rfl⟩
  have hz' := hz k hk
  have e1 := fun J => twMinor_eq M hF hzb hG (p := (τ', stepOf N j b')) hk (hg.mul hXd) hz' (h τ')⁻¹ J
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.2 hd)] at e1
  unfold lowRead
  rw [hk]
  show twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z _ / twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z _ = _
  rw [e1, e1, minor_self_of_lowerUni hX, div_one]
  exact minor_insert_of_lowerUni hX (stepOf_mem M.j_le b') (stepOf_top M.j_le b') hlt

end Flag

theorem chart_reads : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ w ∈ wD ε V, wPhi M F bl h ε k₀ τ ca cb w ∈ wO M Rb τ a k₀ ca cb F kb V r h ∧ wRho M Rb τ k₀ ca cb F kb r h ε (wPhi M F bl h ε k₀ τ ca cb w) = w := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW w hw
  obtain ⟨-, E⟩ := GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW
  have Mm := GlobalTheory.T.wPhi_mem_mcPts_wP K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW w hw
  obtain ⟨-, hbase, hex⟩ := E w hw
  obtain ⟨hb, hbj, hk₀, hca, hcb, -, hF, hBC, hr, -, hh⟩ := hW
  have hwV : wB ε w ∈ V := hw
  obtain ⟨hzb, -, hG, horb⟩ := hBC.2.2.2.2 _ hwV
  have hV : wB ε w ∈ (Rb.A.chart kb).target := hBC.2.1 hwV
  have hr1 : r (bl (wB ε w)) = (Rb.A.chart kb).symm (wB ε w) :=
    Rb.inj _ _ (fun hc => by simpa using hc.2 1 Submodule.mem_top) (orbit_trans (hr _ hzb) (orbit_symm horb))
  set z := wPhi M F bl h ε k₀ τ ca cb w with hzdef
  have hlt : ca < cb := by
    rw [Fin.lt_def]
    omega
  have hj := M.j_le
  have hblk : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) := by
    have := a.2
    have := b.2
    have := cb.2
    unfold lastCol at hca
    split_ifs at hca <;> omega
  have hstep : stepOf N j ca = a := by
    have := a.2
    have := b.2
    have := ca.2
    unfold lastCol at hca
    apply Fin.ext
    rw [stepOf_val]
    split_ifs at hca ⊢ <;> omega
  have hL := fun τ' => lowMat_lowerUni (wL ε w) τ'
  have hLd := fun τ' => lowMat_blockDiag (wL ε w) τ'
  obtain ⟨hL1, hL1d⟩ := mul_elem_lower (hL τ) (hLd τ) hlt hblk (wT ε w)
  have hz1 : ∀ τ' i k, M.blk (τ', i) = some k → ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ =
      ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (bl (wB ε w)) * minorIJ (h τ' * lowMat (wL ε w) τ') I (stepCols N j i) :=
    fun τ' i k hk m => by
      have := (hex τ' i).1.2 k hk m
      rwa [show basePart M.blk (fstPt k₀ z) = bl (wB ε w) from hbase] at this
  have hbs : basePart M.blk (sndPt k₀ z) = bl (wB ε w) := by
    rw [← hbase]
    funext q
    have hne : q.1.1 ≠ k₀ := fun e => q.1.2 (τ, a) (e ▸ hk₀)
    show z (v₁ k₀ ⟨q.1.1, q.2⟩) = z (v₀ k₀ ⟨q.1.1, q.2⟩)
    rw [v₁_ne hne]
    rfl
  have hz2 : ∀ k, M.blk (τ, a) = some k → ∀ m : ι k, sndPt k₀ z ⟨k, m⟩ =
      ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (bl (wB ε w)) *
        minorIJ (h τ * (lowMat (wL ε w) τ * (1 + Matrix.single cb ca (wT ε w)))) I (stepCols N j a) :=
    fun k hk m => by
      have := (hex τ a).2.2 k hk m
      rw [hbs, if_pos rfl] at this
      rw [this, show h τ * (lowMat (wL ε w) τ * (1 + Matrix.single cb ca (wT ε w))) =
        wH h ε τ w * (1 + Matrix.single cb ca (wT ε w)) from (Matrix.mul_assoc _ _ _).symm]
  have hread1 : ∀ τ' (a' b' : Fin N), b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) →
      lowRead M F (bl (wB ε w)) h (fstPt k₀ z) τ' a' b' = lowMat (wL ε w) τ' a' b' :=
    fun τ' a' b' e e' => lowRead_eq M hF hzb hG (hh τ').1 (hh τ').2 (hL τ') (hLd τ') e e'
      fun k hk m => hz1 τ' _ k hk m
  have hread2 : lowRead M F (bl (wB ε w)) h (sndPt k₀ z) τ cb ca =
      (lowMat (wL ε w) τ * (1 + Matrix.single cb ca (wT ε w))) cb ca :=
    lowRead_eq M hF hzb hG (hh τ).1 (hh τ).2 hL1 hL1d hlt hblk.symm (by rw [hstep]; exact hz2)
  refine ⟨⟨Mm, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hbase, hr1]
    exact (Rb.A.chart kb).map_target hV
  · rw [hbase, hr1, (Rb.A.chart kb).right_inv hV]
    exact hwV
  · intro p k hp
    rw [hbase, twMinor_self M hF hzb hG hp (hh p.1).1 (hh p.1).2 (hL p.1) (hLd p.1) (hz1 p.1 p.2 k hp)]
    exact one_ne_zero
  · rw [hbase, twMinor_self M hF hzb hG (p := (τ, a)) hk₀ (hh τ).1 (hh τ).2 hL1 hL1d (hz2 k₀ hk₀)]
    exact one_ne_zero
  · funext i
    obtain ⟨s, rfl⟩ := ε.surjective i
    unfold wRho
    rw [Equiv.symm_apply_apply]
    rcases s with l | q | u
    · show Rb.A.chart kb (r (baseOf M k₀ z)) l = w (ε (Sum.inl l))
      rw [hbase, hr1, (Rb.A.chart kb).right_inv hV]
      rfl
    · show lowRead M F (baseOf M k₀ z) h (fstPt k₀ z) q.1.1 q.1.2.1 q.1.2.2 = w (ε (Sum.inr (Sum.inl q)))
      rw [hbase, hread1 _ _ _ q.2.1 q.2.2]
      exact dif_pos q.2
    · show lowRead M F (baseOf M k₀ z) h (sndPt k₀ z) τ cb ca - lowRead M F (baseOf M k₀ z) h (fstPt k₀ z) τ cb ca =
        w (ε (Sum.inr (Sum.inr u)))
      rw [hbase, hread2, hread1 _ _ _ hlt hblk.symm, mul_elem_apply, if_pos rfl, (hL τ).1, one_mul, add_sub_cancel_left]
      rfl

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Read
