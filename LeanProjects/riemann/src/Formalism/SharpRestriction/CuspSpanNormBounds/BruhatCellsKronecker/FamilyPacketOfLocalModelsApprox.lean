import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfProductFormula
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellSchur

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum Formalism.MainNotions.LocalModelPeriodLattices
open scoped nonZeroDivisors

section Blocks

variable {A B : Type} [Monoid B] (f : ℕ → ℕ → A → B)

theorem modBlocks_append (t : A) (s : ℕ) : ∀ (l : List (A × ℕ)) (a : ℕ) (L : List (Bˣ × ℕ+)),
    modBlocks f a (l ++ [(t, s)]) = some L →
    ∃ (L0 : List (Bˣ × ℕ+)) (τ : Bˣ) (hs : 0 < s), (τ : B) = f (a + (l.map Prod.snd).sum) s t ∧
      L = L0 ++ [(τ, ⟨s, hs⟩)]
  | [], a, L, h => by
    simp only [List.nil_append, modBlocks] at h
    split_ifs at h with hu
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨[], hu.1.unit, hu.2, by simp, by rw [← h]; rfl⟩
  | (t0, s0) :: l, a, L, h => by
    simp only [List.cons_append, modBlocks] at h
    split_ifs at h with hu
    obtain ⟨L1, hL1, hL⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨L0, τ, hs, hτ, hL0⟩ := modBlocks_append t s l (a + s0) L1 hL1
    refine ⟨(hu.1.unit, ⟨s0, hu.2⟩) :: L0, τ, hs, ?_, ?_⟩
    · rw [hτ]; simp only [List.map_cons, List.sum_cons]; rw [add_assoc]
    · rw [← hL, hL0]; rfl

end Blocks

section Van

variable {D : Formalism.BasicNotions.D7}

theorem modPt_ptApp (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) {m : ℕ} (h : Point D.host.E m) (t : D.host.E)
    (ht : t ≠ 0) (s : ℕ) (hs : 1 ≤ s) (a : Loc.Pt (D.s.atP p).Ep (m + s))
    (ha : modPt δ T T' p (ptApp h t ht s hs) = some a) :
    ∃ (a0 : Loc.Pt (D.s.atP p).Ep m) (τ : ((D.s.atP p).Ep)ˣ), (τ : (D.s.atP p).Ep) = blkTop δ T T' p (m + 1) s t ∧
      a = a0.snoc τ ⟨s, hs⟩ := by
  unfold modPt at ha
  have hp : (ptApp h t ht s hs).1 = h.1 ++ [(t, s)] := rfl
  rw [hp] at ha
  rcases hm : modBlocks (blkTop δ T T' p) 1 (h.1 ++ [(t, s)]) with _ | l
  · rw [hm] at ha; simp at ha
  · rw [hm] at ha
    dsimp only at ha
    split_ifs at ha with hsum
    obtain ⟨L0, τ, hs', hτ, hL⟩ := modBlocks_append (blkTop δ T T' p) t s h.1 1 l hm
    subst hL
    have e : (h.1.map Prod.snd).sum = m := by simpa using h.2.2
    have hsz : (L0.map (fun b => (b.2 : ℕ))).sum = m := by
      have h2 := hsum
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, PNat.mk_coe] at h2
      omega
    refine ⟨⟨L0, hsz⟩, τ, ?_, ?_⟩
    · rw [hτ, e, add_comm]
    · cases ha
      rfl

theorem twist_sub (p : PlF D) (s : ℕ) (x y : (D.s.atP p).Ep) : twist p s (x - y) = twist p s x - twist p s y := by
  unfold twist
  cases (D.s.atP p).split with
  | none => rfl
  | some sg =>
    apply sg.e.injective
    ext <;> simp [mul_sub]

theorem tModInv_sub (δ : ∀ p, (D.s.atP p).Fp) (p : PlF D) (ν s : ℕ) (x y : D.host.E) :
    tModInv δ p ν s (x - y) = tModInv δ p ν s x - tModInv δ p ν s y := by
  unfold tModInv
  rw [map_sub, twist_sub]
  ring

theorem loc_step (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (h1 : adm1 D) (m s : ℕ) (hs : 1 ≤ s) (hne : ¬ (m + s = D.R.rS + 1 ∧ s = 1))
    (T T' : ℕ) (h h' : Point D.host.E m) (t t' : D.host.E) (ht : t ≠ 0) (ht' : t' ≠ 0) (p : PlF D)
    (hloc : locK M δ T T' p (m + s) (ptApp h t ht s hs) (ptApp h' t' ht' s hs) ≠ 0) :
    tModInv δ p (nu D.R.rS (m + 1) (m + s)) s (t⁻¹ - t'⁻¹) ∈ (M p).R := by
  unfold locK at hloc
  split at hloc
  · rename_i a b ha hb
    obtain ⟨a0, τ, hτ, rfl⟩ := modPt_ptApp δ T T' p h t ht s hs a ha
    obtain ⟨b0, τ', hτ', rfl⟩ := modPt_ptApp δ T T' p h' t' ht' s hs b hb
    have hidx : m + 1 + s - 1 = m + s := by omega
    have hblk : ∀ y : D.host.E, blkTop δ T T' p (m + 1) s y = tMod δ p (nu D.R.rS (m + 1) (m + s)) s y := by
      intro y
      unfold blkTop blkMod
      rw [hidx, if_neg hne, if_neg hne, sub_zero]
    rw [hblk] at hτ hτ'
    have hδ := (hA p).2.1
    have e1 : ((τ⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep) = tModInv δ p (nu D.R.rS (m + 1) (m + s)) s t⁻¹ :=
      Units.inv_eq_of_mul_eq_one_right (by rw [hτ]; exact tMod_mul_tModInv δ p hδ _ s t ht)
    have e2 : ((τ'⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep) = tModInv δ p (nu D.R.rS (m + 1) (m + s)) s t'⁻¹ :=
      Units.inv_eq_of_mul_eq_one_right (by rw [hτ']; exact tMod_mul_tModInv δ p hδ _ s t' ht')
    by_contra hnot
    rw [tModInv_sub, ← e1, ← e2] at hnot
    have hN := (h1 (D.s.atP p).Fp (D.s.atP p).Ep (M p) (hA p).1).1 m ⟨s, hs⟩ τ τ' a0 b0 hnot
    unfold Loc.Model.Ns at hN
    rcases mul_eq_zero.1 hN with h0 | h0
    · have hOK := (hA p).1
      have := top_of_OK (M p) hOK
      have hpos : 0 < (M p).modK ((τ : (D.s.atP p).Ep) * τ') := by
        have := modK_of_OK (M p) hOK (τ * τ')
        rw [Units.val_mul] at this
        rw [this, ← Units.val_mul]
        exact Formalism.FourierDecayAlt.P.A5x5.modK_pos (R_top (M p) hOK).1 (R_top (M p) hOK).2.1 (τ * τ')
      exact (pow_ne_zero _ hpos.ne') (by exact_mod_cast h0)
    · exact hloc h0
  · exact absurd rfl hloc

theorem locK_cast (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ)
    (p : PlF D) {n N : ℕ} (e : n = N) (w w' : Point D.host.E n) :
    locK M δ T T' p N (e ▸ w) (e ▸ w') = locK M δ T T' p n w w' := by
  subst e
  rfl

theorem vanish_of (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (hd : ∀ p, IsDiffGen δ p) (h1 : adm1 D) (m s : ℕ) (hs : 1 ≤ s)
    (hms : m + s ≤ D.R.rS + 1) (hne : ¬ (m + s = D.R.rS + 1 ∧ s = 1)) (T T' : ℕ) (hfin : Gfin δ M T T')
    (h h' : Point D.host.E m) (t t' : D.host.E) (ht : t ≠ 0) (ht' : t' ≠ 0)
    (hK : Kglob δ M T T' (m + s) (ptApp h t ht s hs) (ptApp h' t' ht' s hs) ≠ 0) :
    t⁻¹ - t'⁻¹ ∈ LaP (D := D) (nu D.R.rS (m + 1) (m + s)) s ∧ (m + s = D.R.rS + 1 → s = 1 → t = t') := by
  refine ⟨?_, fun e1 e2 => absurd ⟨e1, e2⟩ hne⟩
  rw [localCondition_iff δ M hA hd]
  intro p
  refine loc_step δ M hA h1 m s hs hne T T' h h' t t' ht ht' p ?_
  intro h0
  apply hK
  unfold Kglob
  by_cases e : m + s = D.R.rS + 1
  · rw [dif_pos e]
    unfold KtopG
    split_ifs
    · refine finprod_eq_zero _ p ?_ (hfin.2.2.2 _ _)
      unfold KtopP
      rw [locK_cast, h0, mul_zero, zero_mul]
    · rfl
  · rw [dif_neg e]
    exact finprod_eq_zero _ p h0 (hfin.1 _ _ _ hms)

end Van

section Top

variable {D : Formalism.BasicNotions.D7}

theorem point_entry_single_column {K : Type} [Zero K] : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ j, j < (bs.map Prod.snd).sum → ∃ i, i < (bs.map Prod.snd).sum ∧ ∃ t : K, t ≠ 0 ∧
      ∀ j', ptEntry bs i j' = if j' = j then t else 0
  | [], _, j, hj => absurd hj (by simp)
  | (t, s) :: rest, h, j, hj => by
    simp only [List.map_cons, List.sum_cons] at hj ⊢
    by_cases hjs : j < s
    · refine ⟨s - 1 - j, by omega, t, (h (t, s) (by simp)).1, fun j' => ?_⟩
      simp only [ptEntry]
      by_cases hj' : j' = j
      · subst hj'
        rw [if_pos ⟨by omega, hjs⟩, if_pos (by omega), if_pos rfl]
      · rw [if_neg hj']
        by_cases h2 : j' < s
        · rw [if_pos ⟨by omega, h2⟩, if_neg (by omega)]
        · rw [if_neg (fun hh => h2 hh.2), if_neg (fun hh => by omega)]
    · obtain ⟨i0, hi0, t0, ht0, h0⟩ := point_entry_single_column rest (fun b hb => h b (by simp [hb])) (j - s) (by omega)
      refine ⟨i0 + s, by omega, t0, ht0, fun j' => ?_⟩
      simp only [ptEntry]
      rw [if_neg (fun hh => by omega)]
      by_cases h2 : s ≤ j'
      · rw [if_pos ⟨by omega, h2⟩, Nat.add_sub_cancel, h0]
        by_cases hj' : j' = j
        · rw [if_pos (by omega), if_pos hj']
        · rw [if_neg (by omega), if_neg hj']
      · rw [if_neg (fun hh => h2 hh.2), if_neg (by omega)]

theorem point_matrix_det_ne_zero {K : Type} [Field K] {n : ℕ} (p : Point K n) : (ptMat p).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  funext j
  obtain ⟨i, hi, t, ht, hrow⟩ := point_entry_single_column p.1 p.2.1 j.val (by rw [p.2.2]; exact j.isLt)
  have h1 : t * v j = 0 := by
    have h0 := congrFun hMv ⟨i, by have := p.2.2; omega⟩
    simpa [Matrix.mulVec, dotProduct, ptMat, hrow, Fin.val_inj] using h0
  exact (mul_eq_zero.mp h1).resolve_left ht

theorem schExt_det {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (d : K) :
    (schExt A 0 0 d).det = A.det * d := by
  have hsub : (schExt A 0 0 d).submatrix Fin.castSucc Fin.castSucc = A := by
    ext i j; simp [schExt]
  have hz : ∀ i : Fin n, schExt A 0 0 d (Fin.castSucc i) (Fin.last n) = 0 := by
    intro i; simp [schExt]
  have hl : schExt A 0 0 d (Fin.last n) (Fin.last n) = d := by simp [schExt]
  rw [Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_castSucc]
  simp only [Fin.succAbove_last, hsub, hz, hl, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.val_last]
  rw [← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, mul_comm]

private theorem ptEntry_append_singleton {K : Type} [Zero K] (t : K) : ∀ (l : List (K × ℕ)) (i j : ℕ),
    ptEntry (l ++ [(t, 1)]) i j =
      if i < (l.map Prod.snd).sum ∧ j < (l.map Prod.snd).sum then ptEntry l i j
      else if i = (l.map Prod.snd).sum ∧ j = (l.map Prod.snd).sum then t else 0 := by
  intro l
  induction l with
  | nil =>
    intro i j
    simp only [List.nil_append, ptEntry, List.map_nil, List.sum_nil]
    split_ifs <;> first | rfl | (exfalso; omega)
  | cons b l ih =>
    obtain ⟨t0, s0⟩ := b
    intro i j
    simp only [List.cons_append, ptEntry, ih, List.map_cons, List.sum_cons]
    split_ifs <;> first | rfl | (exfalso; omega)

theorem kind_snoc (h : Point D.host.E D.R.rS) (t : D.host.E) (ht : t ≠ 0) (hs : 1 ≤ 1) :
    kind (ptApp h t ht 1 hs) = some t := by
  have hS : (h.1.map Prod.snd).sum = D.R.rS := h.2.2
  have hM : ptMat (ptApp h t ht 1 hs) = schExt (ptMat h) 0 0 t := by
    ext a b
    rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨j, rfl⟩ | rfl <;>
    simp [ptMat, schExt, ptApp, ptEntry_append_singleton, hS, Fin.is_lt, ne_of_lt]
  have hdet : (ptMat h).det ≠ 0 := point_matrix_det_ne_zero h
  have hc : ∀ (hl : D.R.rS ≤ D.R.rS + 1) (i : Fin D.R.rS), Fin.castLE hl i = Fin.castSucc i :=
    fun _ _ => Fin.ext rfl
  have hc2 : ∀ (hl : D.R.rS + 1 ≤ D.R.rS + 1) (i : Fin (D.R.rS + 1)), Fin.castLE hl i = i :=
    fun _ _ => Fin.ext rfl
  have hD1 : Dmin (ptApp h t ht 1 hs) D.R.rS = (ptMat h).det := by
    unfold Dmin
    rw [dif_pos (Nat.le_succ _), hM]
    congr 1
    ext i j
    simp [schExt, hc]
  have hD2 : Dmin (ptApp h t ht 1 hs) (D.R.rS + 1) = (ptMat h).det * t := by
    unfold Dmin
    rw [dif_pos le_rfl, hM, ← schExt_det]
    congr 1
  unfold kind zetaOf
  rw [hD1, if_neg hdet, hD2, mul_div_cancel_left₀ t hdet]

theorem vanish_one (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (m : ℕ) (hs : 1 ≤ 1) (hms : m + 1 = D.R.rS + 1) (T T' : ℕ)
    (h h' : Point D.host.E m) (t t' : D.host.E) (ht : t ≠ 0) (ht' : t' ≠ 0)
    (hK : Kglob δ M T T' (m + 1) (ptApp h t ht 1 hs) (ptApp h' t' ht' 1 hs) ≠ 0) : t = t' := by
  have hm : m = D.R.rS := by omega
  subst hm
  unfold Kglob at hK
  rw [dif_pos hms] at hK
  unfold KtopG at hK
  split_ifs at hK with hk
  · change kind (ptApp h t ht 1 hs) = kind (ptApp h' t' ht' 1 hs) at hk
    rw [kind_snoc h t ht hs, kind_snoc h' t' ht' hs] at hk
    exact Option.some.inj hk
  · exact absurd rfl hK

theorem vanish_all (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (hd : ∀ p, IsDiffGen δ p) (h1 : adm1 D) (m s : ℕ) (hs : 1 ≤ s)
    (hms : m + s ≤ D.R.rS + 1) (T T' : ℕ) (hfin : Gfin δ M T T')
    (h h' : Point D.host.E m) (t t' : D.host.E) (ht : t ≠ 0) (ht' : t' ≠ 0)
    (hK : Kglob δ M T T' (m + s) (ptApp h t ht s hs) (ptApp h' t' ht' s hs) ≠ 0) :
    t⁻¹ - t'⁻¹ ∈ LaP (D := D) (nu D.R.rS (m + 1) (m + s)) s ∧ (m + s = D.R.rS + 1 → s = 1 → t = t') := by
  by_cases hne : m + s = D.R.rS + 1 ∧ s = 1
  · obtain ⟨hm, rfl⟩ := hne
    have htt := vanish_one δ M m hs hm T T' h h' t t' ht ht' hK
    subst htt
    refine ⟨?_, fun _ _ => rfl⟩
    rw [sub_self]
    show _ ∧ _
    constructor
    · first | exact zero_mem _ | exact Submodule.zero_mem _ | (simp; done)
    · first
        | (simp; done)
        | (rw [map_zero, mul_zero, sub_zero]; first | exact zero_mem _ | exact Submodule.zero_mem _)
        | (simp [Formalism.BasicNotions.D7.conjF]; done)
  · exact vanish_of δ M hA hd h1 m s hs hms hne T T' hfin h h' t t' ht ht' hK

end Top

section Red2

open scoped ComplexOrder
open Formalism.MainNotions

variable {D : Formalism.BasicNotions.D7}

def G3fm (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (m s : ℕ) : Prop :=
  let ν := nu D.R.rS (m + 1) (m + s)
  let L := La M δ ν s
  ∀ (T T' : ℕ), 0 < T → 0 < T' → T ≡ T' [MOD (Lat.gS D) ^ 2] → Nat.Coprime T (Lat.gS D) → Nat.Coprime T' (Lat.gS D) →
  ∀ (hs : 1 ≤ s),
    Gfin δ M T T' ∧
    ∀ (ι : Type) [Fintype ι] (hd : ι → Point D.host.E m),
      (∀ x y p, detNrmP M δ T T' p (hd x) = detNrmP M δ T T' p (hd y)) →
      ∃ Th : D.host.E → Matrix ι ι ℂ,
        (∀ t, (Th t).PosSemidef) ∧ (∀ t, ∀ l ∈ L, Th (t + l) = Th t) ∧
        (∀ (t : D.host.E) (ht : t ≠ 0), (Th t - Matrix.of fun x y =>
          ∏ᶠ p, ((((M p).modK (blkMod δ T T' p (m + 1) s t * blkMod δ T T' p (m + 1) s t)) ^
            (s * (s - 1) / 2) : ℝ) : ℂ) *
            locK M δ T T' p (m + s) (ptApp (hd x) t ht s hs) (ptApp (hd y) t ht s hs)).PosSemidef) ∧
        ∃ S : Finset D.host.E, (∀ a ∈ S, ∀ b ∈ S, a - b ∈ L → a = b) ∧
          (∀ t, Th t ≠ 0 → ∃ a ∈ S, t - a ∈ L) ∧
          ∀ x0 : ι, ((((∏ᶠ p, (detNrmP M δ T T' p (hd x0)) ^ (-(2 * (s : ℤ)))) : ℝ) : ℂ) •
            (Matrix.of fun x y => ∏ᶠ p, locK M δ T T' p m (hd x) (hd y)) - ∑ a ∈ S, Th a).PosSemidef

def LocalModelsUnderApproximation (D : Formalism.BasicNotions.D7) {Y : TermTie D} (X : TermLocs D Y) (cN : D.what₂.Word → D.what₂.Word → ℝ) : Prop :=
  4 * D.R.rS + 8 ≤ D.R.k →
    ∃ (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
      (hA : ∀ p, Agree δ M p), G2 δ M (X δ M hA) cN ∧
      (∀ m s, 1 ≤ s → m + s ≤ D.R.rS + 1 → G3fm δ M m s)

variable {eps : ℝ} (Fm : FamP eps) {Y : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)}

end Red2

end Formalism.MainNotions.BridgeLemma

end
