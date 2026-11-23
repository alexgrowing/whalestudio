import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MeanDefs
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SgSegUnique

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem card_fiber_restriction_pi {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (φ : ι' → ι)
    (hφ : Function.Injective φ) (S : Finset ℕ) (A' : ι' → ℕ) (hA' : ∀ i, A' i ∈ S) :
    ((Fintype.piFinset (fun _ : ι => S)).filter (fun A => A ∘ φ = A')).card =
      S.card ^ (Fintype.card ι - Fintype.card ι') := by
  classical
  have h1 : (Fintype.piFinset (fun _ : ι => S)).filter (fun A => A ∘ φ = A') =
      Fintype.piFinset (fun i : ι => if h : ∃ i', φ i' = i then {A' h.choose} else S) := by
    ext A
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hA, hc⟩ i
      by_cases h : ∃ i', φ i' = i
      · simp only [h, dite_true, Finset.mem_singleton]
        rw [← hc, Function.comp, h.choose_spec]
      · simp only [h, dite_false]
        exact hA i
    · intro hA
      constructor
      · intro i
        by_cases h : ∃ i', φ i' = i
        · have := hA i
          simp only [h, dite_true, Finset.mem_singleton] at this
          rw [this]
          exact hA' _
        · have := hA i
          simpa only [h, dite_false] using this
      · funext i'
        have h : ∃ i'', φ i'' = φ i' := ⟨i', rfl⟩
        have := hA (φ i')
        simp only [h, dite_true, Finset.mem_singleton] at this
        rw [Function.comp, this, hφ h.choose_spec]
  rw [h1, Fintype.card_piFinset]
  have h2 : ∀ i : ι, (if h : ∃ i', φ i' = i then ({A' h.choose} : Finset ℕ) else S).card =
      if (∃ i', φ i' = i) then 1 else S.card := by
    intro i
    by_cases h : ∃ i', φ i' = i <;> simp [h]
  simp_rw [h2]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have h3 : (Finset.univ.filter (fun i : ι => ∃ i', φ i' = i)) = Finset.univ.image φ := by
    ext i
    simp
  have h4 : (Finset.univ.filter (fun i : ι => ∃ i', φ i' = i)).card = Fintype.card ι' := by
    rw [h3, Finset.card_image_of_injective _ hφ, Finset.card_univ]
  have h5 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι)) (fun i : ι => ∃ i', φ i' = i)
  rw [h4, Finset.card_univ] at h5
  omega

theorem sum_pi_marginal_injective {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (φ : ι' → ι)
    (hφ : Function.Injective φ) (S : Finset ℕ) (g : (ι' → ℕ) → ℝ) :
    ∑ A ∈ Fintype.piFinset (fun _ : ι => S), g (A ∘ φ) =
      (S.card : ℝ) ^ (Fintype.card ι - Fintype.card ι') * ∑ A' ∈ Fintype.piFinset (fun _ : ι' => S), g A' := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Fintype.piFinset (fun _ : ι => S))
    (t := Fintype.piFinset (fun _ : ι' => S)) (g := fun A => A ∘ φ)
    (fun A hA => Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.1 hA (φ i)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun A' hA' => ?_
  have h1 : ∑ A ∈ (Fintype.piFinset (fun _ : ι => S)).filter (fun A => A ∘ φ = A'), g (A ∘ φ) =
      ∑ A ∈ (Fintype.piFinset (fun _ : ι => S)).filter (fun A => A ∘ φ = A'), g A' :=
    Finset.sum_congr rfl fun A hA => by rw [(Finset.mem_filter.1 hA).2]
  rw [h1, Finset.sum_const, nsmul_eq_mul, card_fiber_restriction_pi φ hφ S A' (Fintype.mem_piFinset.1 hA')]
  push_cast
  rfl

theorem sum_pi_option_split {α : Type} [Fintype α] [DecidableEq α] (S : Finset ℕ) (h : (α → ℕ) → ℕ → ℝ) :
    ∑ A' ∈ Fintype.piFinset (fun _ : Option α => S), h (fun i => A' (some i)) (A' none) =
      ∑ f ∈ Fintype.piFinset (fun _ : α => S), ∑ x ∈ S, h f x := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun A' => (fun i => A' (some i), A' none)) (fun q => fun o => o.elim q.2 q.1)
    ?_ ?_ ?_ ?_ ?_
  · intro A' hA'
    have := Fintype.mem_piFinset.1 hA'
    exact Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun i => this (some i), this none⟩
  · intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hq
    refine Fintype.mem_piFinset.2 fun o => ?_
    cases o with
    | none => exact h2
    | some i => exact Fintype.mem_piFinset.1 h1 i
  · intro A' _
    funext o
    cases o <;> rfl
  · intro q _
    rfl
  · intro A' _
    rfl

structure MeanKappaNumericalFacts (K : Cst) (X : Dat) : Prop where
  hyp' : HypI K.C₀ K.CH X.p X.n' X.m X.TT X.G' X.N₁ X.Y (X.Yb / 2) (X.a : ℝ) X.b' X.bl X.bu X.ccl X.Dp X.cStar
  cb : CBoundI 4 X.p X.m X.TT X.a X.ccl X.cStar X.c4
  j0nn : 0 ≤ X.J0 K
  windowLowerBound : (X.a : ℝ) + X.a / (((X.m : ℝ) + 1) * X.Y) ≤ ((X.ua + X.Jn K + X.ccl : ℕ) : ℝ)
  winA : ((X.ua + X.Jn K + X.ccl : ℕ) : ℝ) ≤ X.a + X.a / (((X.m : ℝ) + 1) * X.Y) + 2 * X.J0 K
  winB : ((X.ub + X.Jn K + X.ccl : ℕ) : ℝ) ≤ X.bu + 2 * X.J0 K
  logl : ((X.m : ℝ) + 1) * X.Y ^ 2 * Real.log X.a ≤ X.a / X.b'
  m0nn : 0 ≤ m0I K.Cm X.p X.m X.G' X.N₁ X.c4
  m0le : m0I K.Cm X.p X.m X.G' X.N₁ X.c4 ≤ X.b' / (((X.m : ℝ) + 1) * (X.p : ℝ) ^ X.G' * X.Y)

def locOf (X : Dat) (aT bT : Fin X.n' → ℕ) : Formalism.MainNotions.ColumnSystems.Loc :=
  { p := X.p, n' := X.n', m := X.m, TT := X.TT, aT := aT, bT := bT, a := X.a, b' := X.b', Y := X.Y, Yb := X.Yb / 2,
    N1 := X.N₁, G' := X.G', bl := X.bl, bh := X.bu, ccl := X.ccl, DLP := X.Dp, cs := X.cStar, c := X.c4 }

theorem local_hypothesis_of_global (K : Cst) (X : Dat) (aT bT : Fin X.n' → ℕ)
    (h : HypI K.C₀ K.CH X.p X.n' X.m X.TT X.G' X.N₁ X.Y (X.Yb / 2) (X.a : ℝ) X.b' X.bl X.bu X.ccl X.Dp X.cStar) :
    Formalism.MainNotions.ColumnSystems.WindowHypotheses K.C₀ K.CH K.CH K.CH K.CH K.CH (locOf X aT bT) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
    h24⟩ := h
  have h23' : (8 : ℝ) * ((X.Dp : ℝ) + 1) ≤ (X.cStar : ℝ) := by exact_mod_cast h23
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    Nat.cast_nonneg _, h21, h22, h23', h24⟩

def instOf (K : Cst) (X : Dat) (R : RS X.p X.n') (jj : Fin (numSeg X.TT)) (B : X.TT → ℕ) : Inst :=
  { L := locOf X (fun _ => 0) (ex B), hm := X.hm, W := R.W, Qq := R.Qq, O := R.O, Kf := R.Kf, ι := R.ι, σ := R.σ,
    jO := R.jO, w := R.w, std := R.std, j := jj, m := m0I K.Cm X.p X.m X.G' X.N₁ X.c4,
    xa := ((X.ua + X.Jn K + X.ccl : ℕ) : ℝ) - ((X.a : ℝ) + X.a / (((X.m : ℝ) + 1) * X.Y)),
    xb := 2 * X.J0 K }

theorem instance_window_eq (K : Cst) (X : Dat) (R : RS X.p X.n') (jj : Fin (numSeg X.TT)) (B : X.TT → ℕ) :
    (instOf K X R jj B).winA = X.WaP K := by
  unfold Inst.winA Dat.WaP
  have h : ((instOf K X R jj B).L.a : ℝ) + (instOf K X R jj B).L.a / ((instOf K X R jj B).L.k * (instOf K X R jj B).L.Y) +
      (instOf K X R jj B).xa = ((X.ua + X.Jn K + X.ccl : ℕ) : ℝ) := by
    show (X.a : ℝ) + X.a / (((X.m : ℝ) + 1) * X.Y) +
      (((X.ua + X.Jn K + X.ccl : ℕ) : ℝ) - ((X.a : ℝ) + X.a / (((X.m : ℝ) + 1) * X.Y))) = _
    ring
  rw [h, Nat.floor_natCast]
  rfl

def kapSeg (K : Cst) (X : Dat) (R : RS X.p X.n') (jj : Fin (numSeg X.TT)) (B : X.TT → ℕ)
    (f : Fin (segS X.TT jj) → ℕ) (x : ℕ) : ℝ :=
  Formalism.MainNotions.G.kapT R.O X.p X.m (segI K.C₀ K.CE1 K.CE2 X.p X.n' X.m X.TT X.G' X.N₁ X.Y X.a X.b' X.c4 (ex B) jj)
    (m0I K.Cm X.p X.m X.G' X.N₁ X.c4) (DjI K.CA X.p X.m X.TT X.N₁ X.Y X.a) f x

theorem segment_mean_kappa_bound (D : Formalism.BasicNotions.D7) (K : Cst) (hK : K.Pos) (hA : K.admitted D) (X : Dat) (hF : MeanKappaNumericalFacts K X) (R : RS X.p X.n')
    (jj : Fin (numSeg X.TT)) (B : X.TT → ℕ) (hB : ∀ s, B s ∈ X.WbP K) :
    (∑ aTop ∈ Fintype.piFinset (fun _ : Fin (segS X.TT jj) => X.WaP K), ∑ aPlus ∈ X.WaP K,
        kapSeg K X R jj B aTop aPlus) /
      ((X.WaP K).card : ℝ) ^ (segS X.TT jj + 1) ≤ K.CA * ((segS X.TT jj : ℝ) + 1) * X.N₁ / X.Y := by
  have hHI : HI K.C₀ K.CH K.CH K.CH K.CH K.CH 4 (instOf K X R jj B) := by
    refine ⟨local_hypothesis_of_global K X _ _ hF.hyp', hF.cb, ?_, ?_, ?_, le_rfl, ?_, hF.logl, hF.m0nn, hF.m0le⟩
    · show 0 ≤ ((X.ua + X.Jn K + X.ccl : ℕ) : ℝ) - ((X.a : ℝ) + X.a / (((X.m : ℝ) + 1) * X.Y))
      linarith [hF.windowLowerBound]
    · show ((X.ua + X.Jn K + X.ccl : ℕ) : ℝ) - ((X.a : ℝ) + X.a / (((X.m : ℝ) + 1) * X.Y)) ≤ 2 * X.J0 K
      linarith [hF.winA]
    · show 0 ≤ 2 * X.J0 K
      linarith [hF.j0nn]
    · intro s hs
      have hs' : s ∈ X.TT := hs
      have h1 := Finset.mem_Icc.1 (hB ⟨s, hs'⟩)
      have h2 : ex B s = B ⟨s, hs'⟩ := dif_pos hs'
      show X.bl ≤ (ex B s : ℝ) ∧ (ex B s : ℝ) ≤ X.bu + 2 * X.J0 K
      rw [h2]
      refine ⟨?_, ?_⟩
      · have h3 : (X.lb : ℝ) ≤ B ⟨s, hs'⟩ := by exact_mod_cast h1.1
        exact le_trans (Nat.le_ceil _) h3
      · have h3 : (B ⟨s, hs'⟩ : ℝ) ≤ ((X.ub + X.Jn K + X.ccl : ℕ) : ℝ) := by exact_mod_cast h1.2
        exact le_trans h3 hF.winB
  have h2 := hA.1 (instOf K X R jj B) hHI
  unfold meanKapT at h2
  rw [instance_window_eq] at h2
  have hY : 0 < X.Y := lt_of_lt_of_le one_pos hF.hyp'.1
  have ht : (((instOf K X R jj B).S K.C₀ K.CE1 K.CE2).t : ℝ) ≤ (segS X.TT jj : ℝ) := by
    have : ((instOf K X R jj B).S K.C₀ K.CE1 K.CE2).t ≤ segS X.TT jj := Nat.sub_le _ _
    exact_mod_cast this
  refine le_trans h2 ?_
  show K.CA * ((((instOf K X R jj B).S K.C₀ K.CE1 K.CE2).t : ℝ) + 1) * (X.N₁ : ℝ) / X.Y ≤ _
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith) hK.2.2.1.le) (Nat.cast_nonneg _)) hY.le

theorem segment_sum_kappa_bound (D : Formalism.BasicNotions.D7) (K : Cst) (hK : K.Pos) (hA : K.admitted D) (X : Dat) (hF : MeanKappaNumericalFacts K X)
    (R : RS X.p X.n') (jj : Fin (numSeg X.TT)) (B : X.TT → ℕ) (hB : ∀ s, B s ∈ X.WbP K)
    (hc : 0 < (X.WaP K).card) :
    ∑ A ∈ Fintype.piFinset (fun _ : X.TT => X.WaP K),
        kapTI R.O K.C₀ K.CA K.CE1 K.CE2 K.Cm X.p X.n' X.m X.TT X.G' X.N₁ X.Y X.a X.b' X.c4 (ex A) (ex B) jj ≤
      ((X.WaP K).card : ℝ) ^ X.N * (K.CA * ((segS X.TT jj : ℝ) + 1) * X.N₁ / X.Y) := by
  have h1 := segment_mean_kappa_bound D K hK hA X hF R jj B hB
  have hcpos : (0 : ℝ) < ((X.WaP K).card : ℝ) := by exact_mod_cast hc
  rw [div_le_iff₀ (pow_pos hcpos _)] at h1
  have h2 : ∀ A : X.TT → ℕ,
      kapTI R.O K.C₀ K.CA K.CE1 K.CE2 K.Cm X.p X.n' X.m X.TT X.G' X.N₁ X.Y X.a X.b' X.c4 (ex A) (ex B) jj =
        (fun A' : Option (Fin (segS X.TT jj)) → ℕ => kapSeg K X R jj B (fun i => A' (some i)) (A' none))
          (A ∘ sgTop X.TT jj) := by
    intro A
    show kapSeg K X R jj B (segATop X.TT (ex A) jj) (segAPlus X.TT (ex A) jj) = _
    have e1 : segATop X.TT (ex A) jj = fun i => (A ∘ sgTop X.TT jj) (some i) := by
      funext i
      exact dif_pos (sg_pos_spec X.TT jj i).1
    have e2 : segAPlus X.TT (ex A) jj = (A ∘ sgTop X.TT jj) none := dif_pos (sg_next_mem X.TT jj).1
    rw [e1, e2]
  have h3 := sum_pi_marginal_injective (sgTop X.TT jj) (sgTop_inj X.TT jj) (X.WaP K)
    (fun A' : Option (Fin (segS X.TT jj)) → ℕ => kapSeg K X R jj B (fun i => A' (some i)) (A' none))
  have h4 := (Finset.sum_congr rfl (fun A (_ : A ∈ Fintype.piFinset (fun _ : X.TT => X.WaP K)) => h2 A)).trans h3
  rw [h4, sum_pi_option_split (X.WaP K) (kapSeg K X R jj B)]
  have hcard : Fintype.card (Option (Fin (segS X.TT jj))) = segS X.TT jj + 1 := by simp
  have hN : Fintype.card X.TT = X.N := Fintype.card_coe _
  have hle : segS X.TT jj + 1 ≤ X.N := by
    rw [← hcard, ← hN]
    exact Fintype.card_le_of_injective _ (sgTop_inj X.TT jj)
  rw [hcard, hN]
  calc ((X.WaP K).card : ℝ) ^ (X.N - (segS X.TT jj + 1)) *
        ∑ f ∈ Fintype.piFinset (fun _ : Fin (segS X.TT jj) => X.WaP K), ∑ x ∈ X.WaP K, kapSeg K X R jj B f x
      ≤ ((X.WaP K).card : ℝ) ^ (X.N - (segS X.TT jj + 1)) *
        (K.CA * ((segS X.TT jj : ℝ) + 1) * X.N₁ / X.Y * ((X.WaP K).card : ℝ) ^ (segS X.TT jj + 1)) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg hcpos.le _)
    _ = ((X.WaP K).card : ℝ) ^ (X.N - (segS X.TT jj + 1) + (segS X.TT jj + 1)) *
        (K.CA * ((segS X.TT jj : ℝ) + 1) * X.N₁ / X.Y) := by
        rw [pow_add]
        ring
    _ = _ := by rw [Nat.sub_add_cancel hle]

theorem meanX_of (D : Formalism.BasicNotions.D7) (K : Cst) (hK : K.Pos) (hA : K.admitted D) (X : Dat) (hF : MeanKappaNumericalFacts K X)
    (R : RS X.p X.n') : MeanX K X R := by
  unfold MeanX meanN
  have hN : Fintype.card X.TT = X.N := Fintype.card_coe _
  rw [hN]
  have hY : 0 < X.Y := lt_of_lt_of_le one_pos hF.hyp'.1
  have hCA : 0 < K.CA := hK.2.2.1
  have hCs : 0 < K.Cs := hK.2.2.2.2.2.2.2.2
  have hb0 : 0 ≤ (K.CA + K.Cs) * X.N * X.N₁ / X.Y := by positivity
  have hNpos : 0 < X.N := by
    obtain ⟨x, hx, -⟩ := hF.hyp'.2.2.1
    exact Finset.card_pos.2 ⟨x, hx⟩
  by_cases hca : (X.WaP K).card = 0
  · rw [hca]
    simpa [hNpos.ne'] using hb0
  by_cases hcb : (X.WbP K).card = 0
  · rw [hcb]
    simpa [hNpos.ne'] using hb0
  have hca' : 0 < (X.WaP K).card := Nat.pos_of_ne_zero hca
  have hcb' : 0 < (X.WbP K).card := Nat.pos_of_ne_zero hcb
  have hcaR : (0 : ℝ) < ((X.WaP K).card : ℝ) := by exact_mod_cast hca'
  have hcbR : (0 : ℝ) < ((X.WbP K).card : ℝ) := by exact_mod_cast hcb'
  rw [div_le_iff₀ (mul_pos (pow_pos hcaR _) (pow_pos hcbR _))]
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.1 hca'
  obtain ⟨b₀, hb₀⟩ := Finset.card_pos.1 hcb'
  have hWin : WinX X.TT X.m X.Y X.a X.bl X.bu (2 * cleaningBudget K.C₀ X.m X.N₁ X.a X.b') (2 * cleaningBudget K.C₀ X.m X.N₁ X.a X.b')
      (fun _ => a₀) (fun _ => b₀) := by
    have h1 := Finset.mem_Icc.1 ha₀
    have h2 := Finset.mem_Icc.1 hb₀
    constructor
    · intro s _
      refine ⟨by exact_mod_cast h1.1, ?_⟩
      have h3 : (a₀ : ℝ) ≤ ((X.ua + X.Jn K + X.ccl : ℕ) : ℝ) := by exact_mod_cast h1.2
      exact le_trans h3 hF.winA
    · intro s _
      refine ⟨?_, ?_⟩
      · have h3 : (X.lb : ℝ) ≤ b₀ := by exact_mod_cast h2.1
        exact le_trans (Nat.le_ceil _) h3
      · have h3 : (b₀ : ℝ) ≤ ((X.ub + X.Jn K + X.ccl : ℕ) : ℝ) := by exact_mod_cast h2.2
        exact le_trans h3 hF.winB
  have hkp : kapPI K.C₀ K.CE1 K.CE2 K.Cm K.Ckap X.p X.m X.TT X.G' X.N₁ X.Y X.a X.b' X.c4 ≤
      K.Cs * X.N * X.N₁ / X.Y :=
    (hA.2.2.1 X.p R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w X.n' X.m X.TT X.G' X.N₁ X.Y (X.Yb / 2) X.a X.b' X.bl X.bu
      X.ccl X.Dp X.cStar (fun _ => a₀) (fun _ => b₀) X.c4 R.std hF.hyp' hWin hF.cb _ hF.m0nn hF.m0le).2
  set PA := Fintype.piFinset (fun _ : X.TT => X.WaP K) with hPA
  set PB := Fintype.piFinset (fun _ : X.TT => X.WbP K) with hPB
  have hcPA : (PA.card : ℝ) = ((X.WaP K).card : ℝ) ^ X.N := by
    rw [hPA, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, hN]
    push_cast
    rfl
  have hcPB : (PB.card : ℝ) = ((X.WbP K).card : ℝ) ^ X.N := by
    rw [hPB, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, hN]
    push_cast
    rfl
  have e2 : ∑ A ∈ PA, ∑ B ∈ PB, ∑ jj, kapTI R.O K.C₀ K.CA K.CE1 K.CE2 K.Cm X.p X.n' X.m X.TT X.G' X.N₁ X.Y X.a X.b'
        X.c4 (ex A) (ex B) jj =
      ∑ jj, ∑ B ∈ PB, ∑ A ∈ PA, kapTI R.O K.C₀ K.CA K.CE1 K.CE2 K.Cm X.p X.n' X.m X.TT X.G' X.N₁ X.Y X.a X.b'
        X.c4 (ex A) (ex B) jj := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun B _ => Finset.sum_comm]
    rw [Finset.sum_comm]
  have e3 : ∑ jj, ∑ B ∈ PB, ∑ A ∈ PA, kapTI R.O K.C₀ K.CA K.CE1 K.CE2 K.Cm X.p X.n' X.m X.TT X.G' X.N₁ X.Y X.a X.b'
        X.c4 (ex A) (ex B) jj ≤
      ∑ jj : Fin (numSeg X.TT), (PB.card : ℝ) * (((X.WaP K).card : ℝ) ^ X.N *
        (K.CA * ((segS X.TT jj : ℝ) + 1) * X.N₁ / X.Y)) := by
    refine Finset.sum_le_sum fun jj _ => ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun B hB => segment_sum_kappa_bound D K hK hA X hF R jj B (Fintype.mem_piFinset.1 hB) hca'
  have e4 : ∑ jj : Fin (numSeg X.TT), ((segS X.TT jj : ℝ) + 1) ≤ X.N := by
    have := sg_count X.TT hF.hyp'.2.2.2.1
    unfold Dat.N
    exact_mod_cast this
  have e5 : ∑ jj : Fin (numSeg X.TT), (PB.card : ℝ) * (((X.WaP K).card : ℝ) ^ X.N *
        (K.CA * ((segS X.TT jj : ℝ) + 1) * X.N₁ / X.Y)) =
      (PB.card : ℝ) * ((X.WaP K).card : ℝ) ^ X.N * (K.CA * X.N₁ / X.Y) *
        ∑ jj : Fin (numSeg X.TT), ((segS X.TT jj : ℝ) + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun jj _ => ?_
    ring
  have e6 : ∑ A ∈ PA, ∑ B ∈ PB, X.kx K R A B =
      (PA.card : ℝ) * ((PB.card : ℝ) * kapPI K.C₀ K.CE1 K.CE2 K.Cm K.Ckap X.p X.m X.TT X.G' X.N₁ X.Y X.a X.b' X.c4) +
      ∑ A ∈ PA, ∑ B ∈ PB, ∑ jj, kapTI R.O K.C₀ K.CA K.CE1 K.CE2 K.Cm X.p X.n' X.m X.TT X.G' X.N₁ X.Y X.a X.b'
        X.c4 (ex A) (ex B) jj := by
    unfold Dat.kx
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [e6, e2]
  have hpos : 0 ≤ (PB.card : ℝ) * ((X.WaP K).card : ℝ) ^ X.N * (K.CA * X.N₁ / X.Y) := by positivity
  have e7 := mul_le_mul_of_nonneg_left e4 hpos
  have e8 : (PA.card : ℝ) * ((PB.card : ℝ) * kapPI K.C₀ K.CE1 K.CE2 K.Cm K.Ckap X.p X.m X.TT X.G' X.N₁ X.Y X.a X.b'
      X.c4) ≤ (PA.card : ℝ) * ((PB.card : ℝ) * (K.Cs * X.N * X.N₁ / X.Y)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkp (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  rw [e5] at e3
  rw [hcPA, hcPB] at *
  calc _ ≤ ((X.WaP K).card : ℝ) ^ X.N * (((X.WbP K).card : ℝ) ^ X.N * (K.Cs * X.N * X.N₁ / X.Y)) +
        ((X.WbP K).card : ℝ) ^ X.N * ((X.WaP K).card : ℝ) ^ X.N * (K.CA * X.N₁ / X.Y) * X.N :=
        add_le_add e8 (le_trans e3 e7)
    _ = _ := by ring

end Formalism.MainNotions.flipOneThree.Pf

end
