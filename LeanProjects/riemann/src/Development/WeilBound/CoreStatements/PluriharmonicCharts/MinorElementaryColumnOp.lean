import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsBlockMapInitialVertex
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorCommutation
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

local instance (priority := 2000) intAlg3 {Φ : Type} [Field Φ] : Algebra ℤ (RatFunc Φ) := Ring.toIntAlgebra _

open GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]

section Minor

variable {R : Type} [CommRing R] {N j : ℕ}

theorem minor_elementary_column_op (h : Matrix (Fin N) (Fin N) R) (S I : Finset (Fin N)) {ca cb : Fin N} (hca : ca ∈ S)
    (hle : ∀ c ∈ S, c ≤ ca) (hlt : ca < cb) (t : R) :
    minorIJ (h * (1 + Matrix.single cb ca t)) I S = minorIJ h I S + t * minorIJ h I (insert cb (S.erase ca)) := by
  have hcb : cb ∉ S.erase ca := fun hh => absurd (hle _ (Finset.mem_of_mem_erase hh)) (not_le.2 hlt)
  have hcard : (insert cb (S.erase ca)).card = S.card := by
    rw [Finset.card_insert_of_notMem hcb, Finset.card_erase_add_one hca]
  by_cases e : I.card = S.card
  swap
  · rw [MinorCalc.minorIJ_of_card_ne _ e, MinorCalc.minorIJ_of_card_ne _ e,
      MinorCalc.minorIJ_of_card_ne _ (hcard ▸ e), mul_zero, add_zero]
  rw [MinorCalc.minorIJ_eq_det _ I S _ e rfl, MinorCalc.minorIJ_eq_det _ I S _ e rfl,
    MinorCalc.minorIJ_eq_det _ I _ _ e hcard]
  set f := S.orderEmbOfFin rfl with hf
  obtain ⟨i₀, hi₀⟩ : ca ∈ Set.range f := by rw [hf, Finset.range_orderEmbOfFin]; exact hca
  have hfS : ∀ x, f x ∈ S := fun x => Finset.orderEmbOfFin_mem _ _ _
  have hf' : Function.update (f : _ → Fin N) i₀ cb = (insert cb (S.erase ca)).orderEmbOfFin hcard := by
    refine Finset.orderEmbOfFin_unique hcard (fun x => ?_) fun x x' hx => ?_
    · by_cases ex : x = i₀
      · subst ex; simp
      · rw [Function.update_of_ne ex]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨fun h' => ex (f.injective (h'.trans hi₀.symm)), hfS x⟩)
    · have h1 : x ≠ i₀ := by
        rintro rfl
        exact absurd (hle _ (hfS x')) (not_le.2 (hi₀ ▸ f.strictMono hx))
      rw [Function.update_of_ne h1]
      by_cases ex : x' = i₀
      · subst ex
        rw [Function.update_self]
        exact (hle _ (hfS x)).trans_lt hlt
      · rw [Function.update_of_ne ex]; exact f.strictMono hx
  rw [← hf']
  set g := I.orderEmbOfFin e
  have e1 : (h * (1 + Matrix.single cb ca t)).submatrix g f =
      (h.submatrix g f).updateCol i₀ ((fun r => h (g r) ca) + t • fun r => h (g r) cb) := by
    ext r x
    rw [Matrix.submatrix_apply, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.updateCol_apply]
    split_ifs with ex
    · subst ex
      rw [hi₀, Matrix.mul_single_apply_same]
      simp [mul_comm]
    · have hne : f x ≠ ca := fun h' => ex (f.injective (h'.trans hi₀.symm))
      rw [show (h * single cb ca t) (g r) (f x) = 0 by simp [Matrix.mul_apply, Matrix.single_apply, hne.symm], add_zero]
      rfl
  rw [e1, Matrix.det_updateCol_add, Matrix.det_updateCol_smul]
  congr 2
  · ext r x
    rw [Matrix.updateCol_apply]
    split_ifs with ex
    · subst ex; rw [Matrix.submatrix_apply, hi₀]
    · rfl
  · congr 1
    ext r x
    rw [Matrix.updateCol_apply]
    show _ = h (g r) (Function.update f i₀ cb x)
    split_ifs with ex
    · subst ex; rw [Function.update_self]
    · rw [Function.update_of_ne ex]; rfl

variable {a b ca cb : Fin N}

theorem minor_elem (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (h : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N))
    (t : R) : minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a) =
      minorIJ h I (stepCols N j a) + t * minorIJ h I (colsB N j a ca cb) := by
  unfold lastCol at hca
  refine minor_elementary_column_op h _ I ?_ (fun c hc => ?_) (by rw [Fin.lt_def]; omega) t
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hca ⊢ <;> omega
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Fin.le_def]
    split_ifs at hca hc <;> omega

theorem elem_apply (t : R) (r c : Fin N) : (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) R) r c =
    (if r = c then 1 else 0) + if cb = r ∧ ca = c then t else 0 := by
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

theorem elem_lowerUni (hcb : (cb : ℕ) = ca + 1) (t : R) : IsLowerUni (1 + Matrix.single cb ca t) := by
  refine ⟨fun r => ?_, fun r c h => ?_⟩
  · rw [elem_apply, if_pos rfl, if_neg, add_zero]
    rintro ⟨rfl, h⟩
    rw [h] at hcb; omega
  · rw [elem_apply, if_neg h.ne, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    rw [Fin.lt_def] at h; omega

theorem same_blk (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) := by
  have := b.2
  unfold lastCol at hca
  split_ifs at hca <;> omega

theorem elem_block (hS : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j)) (t : R) :
    IsBlockDiag j (1 + Matrix.single cb ca t) := fun r c h => by
  rw [elem_apply, if_neg, if_neg, add_zero]
  · rintro ⟨rfl, rfl⟩; exact h hS.symm
  · rintro rfl; exact h Iff.rfl

theorem lowerUni_mul {A B : Matrix (Fin N) (Fin N) R} (hA : IsLowerUni A) (hB : IsLowerUni B) : IsLowerUni (A * B) := by
  refine ⟨fun r => ?_, fun r c h => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single r (fun x _ hx => ?_) (by simp), hA.1, hB.1, one_mul]
    rcases lt_or_gt_of_ne hx with h | h
    · rw [hB.2 _ _ h, mul_zero]
    · rw [hA.2 _ _ h, zero_mul]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    rcases lt_or_ge r x with h' | h'
    · rw [hA.2 _ _ h', zero_mul]
    · rw [hB.2 _ _ (h'.trans_lt h), mul_zero]

theorem minor_other (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (h : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N))
    (t : R) {i : Fin N} (hi : i ≠ a) :
    minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j i) = minorIJ h I (stepCols N j i) := by
  rw [MinorCalc.minorIJ_mul_of_support _ _ _ _ fun k c hc hk => ?_]
  · rw [MinorCalc.minorIJ_eq_det (1 + Matrix.single cb ca t) _ _ _ rfl rfl, Matrix.det_of_lowerTriangular
      ((1 + Matrix.single cb ca t).submatrix _ _) (fun x x' hx =>
        (elem_lowerUni hcb t).2 _ _ (((stepCols N j i).orderEmbOfFin rfl).strictMono (by exact hx))),
]
    have hone : ∀ x, (1 + Matrix.single cb ca t).submatrix ((stepCols N j i).orderEmbOfFin rfl)
        ((stepCols N j i).orderEmbOfFin rfl) x x = 1 := fun x => (elem_lowerUni hcb t).1 _
    simp only [hone, Finset.prod_const_one, mul_one]
  · rw [elem_apply, if_neg, if_neg, add_zero]
    · rintro ⟨rfl, rfl⟩
      apply hk
      have hi' : (i : ℕ) ≠ a := fun e => hi (Fin.ext e)
      have := b.2
      have := i.2
      unfold lastCol at hca
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      split_ifs at hca hc ⊢ <;> omega
    · rintro rfl; exact hk hc

end Minor

variable {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)
  {τ : Ψ} {a b ca cb : Fin N} {k₀ : K}

theorem wCo_eq (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hk : M.blk (τ, a) = some k₀)
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (t : RatFunc Φ) :
    M.wCo (τ, a) k₀ ca cb t = penCo y k₀ (fun m => y ⟨k₀, m⟩) (vecB M τ a k₀ ca cb) t := by
  funext q
  rcases q with ⟨_ | k, m⟩
  · simp only [FlagModel.wCo, penCo, vecB]
    rw [Finset.sum_congr rfl fun I _ => by rw [minor_elem M.j_le hb hab hca hcb], M.y_step _ _ hk m]
    simp only [CPts.minorIJ_map, mul_add, Finset.sum_add_distrib, map_sum, map_mul, Finset.mul_sum, mul_left_comm t]
  · rfl

theorem charZero_of_model (M : FlagModel y Ψ N j) : CharZero Φ :=
  charZero_of_injective_ringHom (f := algebraMap M.Ω Φ) (algebraMap M.Ω Φ).injective

theorem blocks_of_model (M : FlagModel y Ψ N j) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by
  by_cases hk : ∀ p, M.blk p ≠ some k
  · obtain ⟨i, hi⟩ := M.x_ne ⟨k, hk⟩
    exact ⟨i, by
      rw [show y ⟨k, i⟩ = algebraMap M.Ω Φ (M.x ⟨⟨k, hk⟩, i⟩) from M.y_base ⟨⟨k, hk⟩, i⟩]
      exact (map_ne_zero _).2 hi⟩
  · push Not at hk
    obtain ⟨p, hp⟩ := hk
    obtain ⟨F, hF, hG⟩ := M.exists_frame
    let am := algebraMap M.Ω Φ
    let H : Matrix (Fin N) (Fin N) Φ := (F.T p.1)⁻¹.map am * M.g p.1
    have hH : (F.T p.1).map am * H = M.g p.1 := CPts.map_mul_inv_map am (hF.1 p.1).2 _
    have hHb : IsBlockDiag j H := (((hF.1 p.1).1.inv (hF.1 p.1).2.isUnit).map am).mul (M.g_block p.1)
    have hHd : H.det ≠ 0 := fun h0 => (M.isUnit_det_g p.1).ne_zero (by rw [← hH, det_mul, h0, mul_zero])
    obtain ⟨m, hm, -⟩ := GlobalTheory.T.step_rows_inverse_nonzero_entry Φ ⊤ N j p.2 H (ι k) (fun m I => am (F.u ⟨k, m⟩ I))
      (fun I m => am (F.u' I ⟨k, m⟩)) M.j_le hHb (fun _ _ => ValuationSubring.mem_top _) hHd
      (ValuationSubring.mem_top _) (fun _ _ => ValuationSubring.mem_top _) (fun _ _ => ValuationSubring.mem_top _)
      (fun I I' hI hI' => by
          have := congrArg am (hF.2.2.1 p k hp I I' hI hI')
          rw [map_sum] at this
          simp only [map_mul] at this
          rw [this]
          split_ifs <;> simp)
    refine ⟨m, fun h0 => ?_⟩
    have rel := CPts.frame_gen M hF (RingHom.id Φ) hp m hHb isBlockDiag_one blockTriangular_one (by
      rw [Matrix.mul_one]; exact hH)
    simp only [RingHom.id_apply, h0, mul_zero] at rel
    exact mul_ne_zero ((map_ne_zero am).2 (Finset.prod_ne_zero_iff.2 fun k' _ =>
        zpow_ne_zero _ (M.x_chart_ne le_rfl hG k'))) hm rel.symm

theorem image_snd (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hk : M.blk (τ, a) = some k₀)
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1)
    (v₁ : (Σ k, ι k) → (Σ o : Option K, ι (o.getD k₀))) (h1 : ∀ p : (Σ k, ι k), p.1 ≠ k₀ → v₁ p = ⟨some p.1, p.2⟩)
    (h2 : ∀ m : ι k₀, v₁ ⟨k₀, m⟩ = ⟨none, m⟩) :
    imageZ v₁ (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y := by
  have hbm : IsBlockMap (ι := ι) (ι' := iW ι k₀) (fun k => if k = k₀ then none else some k) v₁ := by
    have hfst : ∀ p, (v₁ p).1 = if p.1 = k₀ then none else some p.1 := by
      rintro ⟨k, m⟩
      by_cases e : k = k₀
      · subst e; rw [h2]; simp
      · rw [h1 _ e]; simp [e]
    have hinj : Function.Injective fun k => if k = k₀ then none else some k := by
      intro k k' e
      dsimp only at e
      split_ifs at e with a b
      · rw [a, b]
      · exact Option.some.inj e
    refine ⟨hinj, ?_, hfst, ?_⟩
    · rintro ⟨k, m⟩ ⟨k', m'⟩ e
      obtain rfl : k = k' := hinj (by have := congrArg Sigma.fst e; rwa [hfst, hfst] at this)
      by_cases e' : k = k₀
      · subst e'
        rw [h2, h2] at e
        cases e; rfl
      · rw [h1 _ e', h1 _ e'] at e
        cases e; rfl
    · rintro ⟨_ | k, m⟩ ⟨k', e⟩
      · exact ⟨⟨k₀, m⟩, h2 m⟩
      · dsimp only at e
        split_ifs at e with a
        obtain rfl := Option.some.inj e
        exact ⟨⟨k', m⟩, h1 _ a⟩
  rw [imageZ_eq hbm]
  apply le_antisymm
  · rw [← imageZ_eq hbm, wCo_eq M hb hab hk hca hcb]
    intro f hf
    have h3 : f ∈ imageZ v₁ (mCoordIdeal (ext2 y k₀ fun m => y ⟨k₀, m⟩)) := pen_le_zero _ _ _ _ hf
    rw [imageZ_eq hbm] at h3
    convert h3 using 2
    funext ⟨k, m⟩
    by_cases e : k = k₀
    · subst e; simp only [Function.comp, h2]; rfl
    · simp only [Function.comp, h1 ⟨k, m⟩ e]; rfl
  · obtain ⟨B, hB, hind⟩ := M.g_indep
    let ev : MvPolynomial (LowIdx Ψ N j) M.Ω →ₐ[M.Ω] Φ := aeval fun q => (M.g q.1.1 * B q.1.1) q.1.2.1 q.1.2.2
    obtain ⟨c, hc, hz⟩ := exists_scale M ev.toRingHom (algebraMap M.Ω Φ) (fun a => aeval_C _ a) M.g B M.g_block hB
      (fun q => aeval_X _ q) y M.y_base M.y_step
    rw [mCoordIdeal_eq ev.toRingHom hind _ _ c hc hz]
    let φ := algebraMap Φ (RatFunc Φ)
    have hS := same_blk M.j_le hb hab hca hcb
    have hdiag : ∀ c, B τ c c ≠ 0 := fun c h0 => by
      have h1 : (M.g τ).det * (B τ).det = 1 := by rw [← det_mul, (hB τ).2.2.det]
      have h2 : ∏ i, B τ i i = 0 := Finset.prod_eq_zero (Finset.mem_univ c) h0
      rw [det_of_upperTriangular (hB τ).2.1, h2, mul_zero] at h1
      exact zero_ne_one h1
    have hden : φ (B τ cb cb) - RatFunc.X * φ (B τ ca cb) ≠ 0 := fun h0 => by
      have h3 : algebraMap (Polynomial Φ) (RatFunc Φ)
          (Polynomial.C (B τ cb cb) - Polynomial.X * Polynomial.C (B τ ca cb)) = 0 := by
        rw [map_sub, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
          ← RatFunc.algebraMap_eq_C]
        exact h0
      have h4 := congrArg (Polynomial.eval 0) ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h3)
      exact hdiag cb (by simpa [φ, RatFunc.algebraMap_eq_C] using h4)
    have haa : φ (B τ ca ca) ≠ 0 := (map_ne_zero φ).2 (hdiag ca)
    have hbb : φ (B τ cb cb) ≠ 0 := (map_ne_zero φ).2 (hdiag cb)
    let s : RatFunc Φ := RatFunc.X * φ (B τ ca ca) / (φ (B τ cb cb) - RatFunc.X * φ (B τ ca cb))
    have hs : φ (B τ ca ca) + s * φ (B τ ca cb) =
        φ (B τ ca ca) * φ (B τ cb cb) / (φ (B τ cb cb) - RatFunc.X * φ (B τ ca cb)) := by
      simp only [s]; field_simp; ring
    obtain ⟨V, hV1, hV2, -, hV⟩ := GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection.exists_conj (RatFunc Φ) N j ca cb ((B τ).map φ) RatFunc.X s hcb hS
      ((hB τ).1.map φ) ((hB τ).2.1.map φ) (fun c => (map_ne_zero φ).2 (hdiag c))
      (by show φ _ + s * φ _ ≠ 0; rw [hs]; exact div_ne_zero (mul_ne_zero haa hbb) hden)
      (by show _ * (φ _ + s * φ _) = s * φ _; rw [hs]; simp only [s]; field_simp)
    let G : Ψ → Matrix (Fin N) (Fin N) (RatFunc Φ) := fun τ' =>
      if τ' = τ then (M.g τ).map φ * (1 + Matrix.single cb ca RatFunc.X) else (M.g τ').map φ
    let B' : Ψ → Matrix (Fin N) (Fin N) (RatFunc Φ) := fun τ' => if τ' = τ then V else (B τ').map φ
    let ψ : M.Ω →+* RatFunc Φ := φ.comp (algebraMap M.Ω Φ)
    let f : MvPolynomial (LowIdx Ψ N j) M.Ω →+* RatFunc Φ := eval₂Hom ψ fun q => (G q.1.1 * B' q.1.1) q.1.2.1 q.1.2.2
    have hG1 : ∀ τ', IsBlockDiag j (G τ') := fun τ' => by
      simp only [G]
      split_ifs
      · exact ((M.g_block τ).map φ).mul (elem_block hS _)
      · exact (M.g_block τ').map φ
    have hG2 : ∀ τ', IsBlockDiag j (B' τ') ∧ (B' τ').BlockTriangular id ∧ IsLowerUni (G τ' * B' τ') := fun τ' => by
      simp only [G, B']
      split_ifs
      · refine ⟨hV1, hV2, ?_⟩
        rw [Matrix.mul_assoc, hV, ← Matrix.mul_assoc, ← Matrix.map_mul]
        exact lowerUni_mul ((hB τ).2.2.map φ) (elem_lowerUni hcb s)
      · refine ⟨(hB τ').1.map φ, (hB τ').2.1.map φ, ?_⟩
        rw [← Matrix.map_mul]
        exact (hB τ').2.2.map φ
    have hG3 : ∀ q : Σ k, baseIdx ι M.blk k, (M.wCo (τ, a) k₀ ca cb RatFunc.X ∘ v₁) ⟨q.1.1, q.2⟩ = ψ (M.x q) := by
      intro q
      have hne : q.1.1 ≠ k₀ := fun e => q.1.2 _ (e ▸ hk)
      simp only [Function.comp, h1 ⟨q.1.1, q.2⟩ hne]
      exact congrArg φ (M.y_base q)
    have hG4 : ∀ p k, M.blk p = some k → ∀ m : ι k, (M.wCo (τ, a) k₀ ca cb RatFunc.X ∘ v₁) ⟨k, m⟩ =
        ∑ I, ψ (M.coef ⟨k, m⟩ I) * minorIJ (G p.1) I (stepCols N j p.2) := by
      intro p k hp m
      by_cases e : k = k₀
      · subst e
        obtain rfl := M.blk_inj _ _ _ hp hk
        simp only [Function.comp, h2, G, if_true]
        rfl
      · simp only [Function.comp, h1 ⟨k, m⟩ e]
        show φ (y ⟨k, m⟩) = _
        rw [M.y_step p k hp m, map_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [map_mul]
        congr 1
        simp only [G]
        split_ifs with e'
        · rw [minor_other M.j_le hb hab hca hcb, CPts.minorIJ_map, e']
          rintro e''
          apply e
          have : p = (τ, a) := Prod.ext e' e''
          rw [this, hk] at hp
          exact (Option.some.inj hp).symm
        · rw [CPts.minorIJ_map]
    obtain ⟨c', -, hz'⟩ := exists_scale M f ψ (fun a => eval₂Hom_C _ _ a) G B' hG1 hG2
      (fun q => eval₂Hom_X' _ _ q) (M.wCo (τ, a) k₀ ca cb RatFunc.X ∘ v₁) hG3 hG4
    intro g hg
    have hg' : coneOver (polyPt M) g = 0 := hg
    show mConeMap _ g = 0
    rw [mConeMap_eq f _ _ c' hz', hg', map_zero, map_zero]

end PositivityTheory.Xgp.W
