import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.InterpWeight
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CurvAndMarginClosed
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameThetaConstPos
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsMulNe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.KappaStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.ShareSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem drop_of_gaps {Ψ : Finset (E →+* ℂ)} {p0 : ℕ} {L : Wt Ψ r} (h : GapsGe p0 L 1) (τ : Ψ) :
    ∀ d : ℕ, ∀ i j : Fin r, (j : ℕ) = i + d → (p0 ≤ (i : ℕ) ∨ (j : ℕ) < p0) → L τ j + d ≤ L τ i := by
  intro d
  induction d with
  | zero =>
    intro i j hij _
    have : i = j := Fin.ext (by omega)
    subst this
    simp
  | succ d ih =>
    intro i j hij hb
    have hk : (i : ℕ) + d < r := by omega
    have h1 := ih i ⟨i + d, hk⟩ rfl (by
      rcases hb with hb | hb
      · exact Or.inl hb
      · right; simp only; omega)
    have h2 := h τ ⟨i + d, hk⟩ j (by simp only; omega) (by omega)
    push_cast
    linarith

theorem spread_of_gaps {Ψ : Finset (E →+* ℂ)} {p0 : ℕ} {L : Wt Ψ r} (h : GapsGe p0 L 1) (τ : Ψ)
    (i j i0 i1 : Fin r) (hi : (i : ℕ) < p0) (hj : p0 ≤ (j : ℕ)) (h0 : (i0 : ℕ) = 0) (h1 : (i1 : ℕ) = r - 1) :
    L τ i1 - L τ i0 ≤ L τ j - L τ i := by
  have a := drop_of_gaps h τ (r - 1 - j) j i1 (by omega) (Or.inl hj)
  have b := drop_of_gaps h τ i i0 i (by omega) (Or.inr hi)
  have c : (0 : ℤ) ≤ ((r - 1 - j : ℕ) : ℤ) := Nat.cast_nonneg _
  have d : (0 : ℤ) ≤ ((i : ℕ) : ℤ) := Nat.cast_nonneg _
  linarith

theorem wt_apply (X : Data E r) (L : Wt X.Ψ r) (a s : ℕ) (τ : X.Ψ) (i : Fin r) :
    (a • L - 2 • deMul X.Ψ r X.p0 s - kapW X) τ i =
      (a : ℤ) * L τ i - 2 * (if (i : ℕ) < X.p0 then -((s / 2 : ℕ) : ℤ) else ((s / 2 : ℕ) : ℤ)) -
        (2 * ((i : ℕ) : ℤ) - ((r : ℤ) - 1)) := by
  simp only [Pi.sub_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul, deMul, kapW]
  push_cast
  ring

end GlobalTheory.ShareSection

namespace GlobalTheory.ShareSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem block_fst (X : Data E r) {L : Wt X.Ψ r} (hg : GapsGe X.p0 L 1) (a s : ℕ) :
    ∀ (τ : X.Ψ) (i j : Fin r), i ≤ j → (j : ℕ) < X.p0 →
      (a • L - 2 • deMul X.Ψ r X.p0 s - kapW X) τ j ≤ (a • L - 2 • deMul X.Ψ r X.p0 s - kapW X) τ i := by
  intro τ i j hij hj
  have hij' : (i : ℕ) ≤ j := hij
  have hd := drop_of_gaps hg τ (j - i) i j (by omega) (Or.inr hj)
  rw [wt_apply, wt_apply, if_pos hj, if_pos (by omega)]
  have e : (((j - i : ℕ) : ℤ)) = (j : ℤ) - (i : ℤ) := by push_cast [Nat.cast_sub hij']; ring
  rw [e] at hd
  have ha : (0 : ℤ) ≤ a := Nat.cast_nonneg _
  have hm : (a : ℤ) * L τ j ≤ (a : ℤ) * L τ i := mul_le_mul_of_nonneg_left (by linarith) ha
  linarith

theorem block_snd (X : Data E r) {L : Wt X.Ψ r} (hg : GapsGe X.p0 L 1) (a s : ℕ) :
    ∀ (τ : X.Ψ) (i j : Fin r), X.p0 ≤ (i : ℕ) → i ≤ j →
      (a • L - 2 • deMul X.Ψ r X.p0 s - kapW X) τ j ≤ (a • L - 2 • deMul X.Ψ r X.p0 s - kapW X) τ i := by
  intro τ i j hi hij
  have hij' : (i : ℕ) ≤ j := hij
  have hd := drop_of_gaps hg τ (j - i) i j (by omega) (Or.inl hi)
  rw [wt_apply, wt_apply, if_neg (by omega), if_neg (by omega)]
  have e : (((j - i : ℕ) : ℤ)) = (j : ℤ) - (i : ℤ) := by push_cast [Nat.cast_sub hij']; ring
  rw [e] at hd
  have ha : (0 : ℤ) ≤ a := Nat.cast_nonneg _
  have hm : (a : ℤ) * L τ j ≤ (a : ℤ) * L τ i := mul_le_mul_of_nonneg_left (by linarith) ha
  linarith

theorem cross (X : Data E r) {L : Wt X.Ψ r} (hg : GapsGe X.p0 L 1) {T : ℕ} (hp : PairGe L (1.9 * T))
    (a s : ℕ) (hs : s ≤ T) (hr : X.p0 < r) :
    ∀ (τ : X.Ψ) (i j : Fin r), (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) →
      (a : ℝ) * (1.9 * T) - 2 * T - 2 * ((r : ℝ) - 1) ≤
        (((a • L - 2 • deMul X.Ψ r X.p0 s - kapW X) τ j : ℤ) : ℝ) -
          (((a • L - 2 • deMul X.Ψ r X.p0 s - kapW X) τ i : ℤ) : ℝ) := by
  intro τ i j hi hj
  have hsp := spread_of_gaps hg τ i j ⟨0, by omega⟩ ⟨r - 1, by omega⟩ hi hj rfl rfl
  have hpp := hp τ ⟨0, by omega⟩ ⟨r - 1, by omega⟩ rfl rfl
  have hD : (1.9 * T : ℝ) ≤ ((L τ j - L τ i : ℤ) : ℝ) := hpp.trans (by exact_mod_cast hsp)
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_left hD ha
  rw [wt_apply, wt_apply, if_pos hi, if_neg (by omega)]
  have hq0 : s / 2 * 2 ≤ T := (Nat.div_mul_le_self s 2).trans hs
  generalize s / 2 = q at hq0 ⊢
  have hq : (q : ℝ) * 2 ≤ T := by exact_mod_cast hq0
  have hij : ((j : ℕ) : ℝ) - (i : ℕ) ≤ (r : ℝ) - 1 := by
    have : (j : ℕ) + 1 ≤ r := j.isLt
    have : (j : ℝ) + 1 ≤ r := by exact_mod_cast this
    have : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    linarith
  push_cast at hm ⊢
  nlinarith

theorem gaps_G (X : Data E r) {L : Wt X.Ψ r} (hg : GapsGe X.p0 L 1) (n s : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X (n • L - 2 • deMul X.Ψ r X.p0 s) 0 := by
  intro τ i j hij hj
  have h1 := hg τ i j hij hj
  have e : ∀ k : Fin r, (n • L - 2 • deMul X.Ψ r X.p0 s) τ k =
      (n : ℤ) * L τ k - 2 * (if (k : ℕ) < X.p0 then -((s / 2 : ℕ) : ℤ) else ((s / 2 : ℕ) : ℤ)) := by
    intro k
    simp only [Pi.sub_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, deMul]
    push_cast
    ring
  have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg _
  have hm : (0 : ℤ) ≤ (n : ℤ) * (L τ i - L τ j) := mul_nonneg hn (by linarith)
  rw [e, e]
  by_cases hi : (i : ℕ) < X.p0
  · rw [if_pos hi, if_pos (by omega)]
    have : (0 : ℤ) ≤ (n : ℤ) * L τ i - 2 * -((s / 2 : ℕ) : ℤ) - ((n : ℤ) * L τ j - 2 * -((s / 2 : ℕ) : ℤ)) := by
      linarith
    exact_mod_cast this
  · rw [if_neg hi, if_neg (by omega)]
    have : (0 : ℤ) ≤ (n : ℤ) * L τ i - 2 * ((s / 2 : ℕ) : ℤ) - ((n : ℤ) * L τ j - 2 * ((s / 2 : ℕ) : ℤ)) := by
      linarith
    exact_mod_cast this

theorem pair_G (X : Data E r) {L : Wt X.Ψ r} {T : ℕ} (hp : PairGe L (1.9 * T)) (n s : ℕ) (hn : 6 ≤ n)
    (hs : s ≤ T) (hT : 1 ≤ T) (h0 : 0 < X.p0) (hr : X.p0 < r) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X (n • L - 2 • deMul X.Ψ r X.p0 s) 1 := by
  intro τ i0 i1 h0' h1'
  have hpp := hp τ i0 i1 h0' h1'
  have e : ∀ k : Fin r, (n • L - 2 • deMul X.Ψ r X.p0 s) τ k =
      (n : ℤ) * L τ k - 2 * (if (k : ℕ) < X.p0 then -((s / 2 : ℕ) : ℤ) else ((s / 2 : ℕ) : ℤ)) := by
    intro k
    simp only [Pi.sub_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, deMul]
    push_cast
    ring
  rw [e, e, if_pos (show (i0 : ℕ) < X.p0 by omega), if_neg (show ¬ (i1 : ℕ) < X.p0 by omega)]
  have hq0 : s / 2 * 2 ≤ T := (Nat.div_mul_le_self s 2).trans hs
  generalize s / 2 = q at hq0 ⊢
  have hq : (q : ℝ) * 2 ≤ T := by exact_mod_cast hq0
  have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  push_cast at hpp ⊢
  nlinarith

theorem card_mul_le_nd (X : Data E r) : X.Ψ.card * (r - 1) ≤ nd X := by
  let f : X.Ψ × Fin (r - 1) → Ent X := fun p =>
    (p.1, ⟨(⟨p.2.1 + 1, by have := p.2.isLt; omega⟩, ⟨0, by have := p.2.isLt; omega⟩), by simp [Fin.lt_def]⟩)
  have hf : Function.Injective f := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at h
    obtain ⟨h1, h2, -⟩ := h
    subst h1
    rw [Prod.mk.injEq]
    exact ⟨rfl, Fin.ext (by omega)⟩
  have := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, nd] using this

theorem size_le (c n R T : ℕ) (hc : 1 ≤ c) (hR : 2 ≤ R) (hn : 2 ≤ n) (hcn : c * (R - 1) ≤ n)
    (hT : 11 * n ^ 2 ≤ T) : 4 * c * R ^ 2 + 2 * R ≤ 2 * T := by
  obtain ⟨e, rfl⟩ : ∃ e, R = e + 1 := ⟨R - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hcn
  have he : 1 ≤ e := by omega
  have h1 : c * e * (c * e) ≤ n * n := Nat.mul_le_mul hcn hcn
  have h2a : (e + 1) ^ 2 ≤ 4 * (e * e) := by nlinarith
  have h2 : c * (e + 1) ^ 2 ≤ 4 * (c * e * (c * e)) :=
    calc c * (e + 1) ^ 2 ≤ c * (4 * (e * e)) := Nat.mul_le_mul_left _ h2a
      _ ≤ (c * c) * (4 * (e * e)) := Nat.mul_le_mul_right _ (Nat.le_mul_self c)
      _ = 4 * (c * e * (c * e)) := by ring
  have h3 : 2 * (e + 1) ≤ 4 * n := by nlinarith
  have h4 : 4 * n ≤ 2 * (n * n) := by nlinarith
  nlinarith

end GlobalTheory.ShareSection

namespace GlobalTheory.ShareSection

theorem exists_bddSec_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r)
    (Xa : ArchInM X.toData) (Fl : FlatM X.toData Xa), GlobalTheory.Shares.Margins X.toData Xa → 0 < X.p0 → X.p0 < r →
    GapsGe X.p0 Xa.L 1 → PairGe Xa.L (1.9 * Xa.T) →
    GapsGe X.p0 (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 0 →
    PairGe (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 1 → ∀ s : ℕ, Even s → s ≤ Xa.T →
    ∀ u : Frame X.Ψ r → ℂ, u ∈ X.SS (deMul X.Ψ r X.p0 s) → (∃ x ∈ X.dom, u x ≠ 0) →
    ∃ w : Frame X.Ψ r → ℂ, X.IsBddSec ((nd X.toData + 4) • Xa.L - 2 • deMul X.Ψ r X.p0 s) w ∧
      ∃ x ∈ X.dom, w x ≠ 0 := by
  intro E _ _ _ r X Xa Fl _ h0 hr hg hp _ _ s _ hsT _ _ _
  have hn := Xa.n_ge
  have hT := Xa.T_ge
  have hT1 : 1 ≤ Xa.T := le_trans (by nlinarith) hT

  have hδ : 0 < Fl.δ := by
    rcases Nat.eq_zero_or_pos Fl.δ with h | h
    · exfalso
      obtain ⟨x1, hx1, h1⟩ := Xa.thp_ne
      obtain ⟨k, hk⟩ := Xa.w_nz x1 hx1
      have hb : ∀ n : ℕ, X.toData.IsBddSec (Xa.Fp + n • Xa.L) (Xa.thp * Xa.w k ^ n) := by
        intro n
        induction n with
        | zero => simpa using Xa.thp_van.1.1
        | succ n ih =>
          have := BoundedSectionAlgebra.bdd_mul X.toData ih (Xa.w_van k).1.1
          rw [succ_nsmul, ← add_assoc, pow_succ, ← mul_assoc]
          exact this
      have hup := GlobalTheory.UpperModel.upper E r X.toData Xa Fl 1 (fun _ => Xa.thp * Xa.w k ^ Xa.T)
        (fun _ => hb Xa.T) (by
          intro c hc
          funext q
          have hq : q = 0 := Subsingleton.elim _ _
          subst hq
          have := hc x1 hx1
          simp only [Fin.sum_univ_one, Pi.mul_apply, Pi.pow_apply] at this
          rcases mul_eq_zero.1 this with h' | h'
          · exact h'
          · exfalso
            exact mul_ne_zero h1 (pow_ne_zero _ hk) h')
      rw [h, zero_mul] at hup
      omega
    · exact h
  have hR : 2 ≤ r := by omega
  have hc1 : 1 ≤ X.Ψ.card := by
    have := GlobalTheory.ThetaRecordCompare.two_le_r hn
    by_contra hc
    have h0c : X.Ψ.card = 0 := by omega
    have := card_mul_le_nd X.toData
    have hnd : nd X.toData = X.Ψ.card * (Fintype.card {p : Fin r × Fin r // p.2 < p.1}) := by
      simp [nd, Fintype.card_prod, Fintype.card_coe]
    rw [h0c, zero_mul] at hnd
    omega
  have hsize := size_le X.Ψ.card (nd X.toData) r Xa.T hc1 hR hn (card_mul_le_nd X.toData) hT
  have hsize' : (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 2 * r) ≤ 2 * Xa.T := by exact_mod_cast hsize
  have hTr : (0 : ℝ) ≤ Xa.T := Nat.cast_nonneg _

  have e4 : (nd X.toData + 4) • Xa.L - 2 • deMul X.Ψ r X.p0 s - kapW X.toData - nd X.toData • Xa.L =
      4 • Xa.L - 2 • deMul X.Ψ r X.p0 s - kapW X.toData := by
    funext τ i
    simp only [Pi.sub_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have e3 : (nd X.toData + 4) • Xa.L - 2 • deMul X.Ψ r X.p0 s - kapW X.toData - (nd X.toData + 1) • Xa.L =
      3 • Xa.L - 2 • deMul X.Ψ r X.p0 s - kapW X.toData := by
    funext τ i
    simp only [Pi.sub_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have hmar : ∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X.toData x0 → ∀ z ∈ OmF X.toData x0, ∀ ξ : Fin (nd X.toData) → ℂ,
        m * leviRh X.toData x0 z ξ ≤
          leviO X.toData x0 (phla X.toData ((nd X.toData + 4) • Xa.L - 2 • deMul X.Ψ r X.p0 s)) z ξ -
            leviDens X.toData x0 z ξ - (nd X.toData : ℝ) * leviO X.toData x0 (phla X.toData Xa.L) z ξ := by
    refine ⟨4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1, (4 : ℕ) * (1.9 * Xa.T) - 2 * Xa.T - 2 * ((r : ℝ) - 1),
      by linarith, by push_cast; nlinarith, fun x0 ho z hz ξ => ?_⟩
    have h := (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X.toData
      (4 • Xa.L - 2 • deMul X.Ψ r X.p0 s - kapW X.toData) _ (block_fst X.toData hg 4 s)
      (block_snd X.toData hg 4 s) (cross X.toData hg hp 4 s hsT hr) x0 ho z hz ξ
    have e := IW.leviM_comb X.toData x0 ho hz ((nd X.toData + 4) • Xa.L - 2 • deMul X.Ψ r X.p0 s) Xa.L
      (nd X.toData) ξ
    rw [e4] at e
    have e' : leviO X.toData x0 (phla X.toData (4 • Xa.L - 2 • deMul X.Ψ r X.p0 s - kapW X.toData)) z ξ =
        leviM X.toData (phla X.toData (4 • Xa.L - 2 • deMul X.Ψ r X.p0 s - kapW X.toData)) x0 z ξ := rfl
    linarith
  have hstr : ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X.toData x0 → ∀ z ∈ OmF X.toData x0, ∀ ξ : Fin (nd X.toData) → ℂ,
      2 * η * leviO X.toData x0 (phla X.toData Xa.L) z ξ ≤
        leviO X.toData x0 (phla X.toData ((nd X.toData + 4) • Xa.L - 2 • deMul X.Ψ r X.p0 s)) z ξ -
          leviDens X.toData x0 z ξ - (nd X.toData : ℝ) * leviO X.toData x0 (phla X.toData Xa.L) z ξ := by
    refine ⟨1 / 2, by norm_num, fun x0 ho z hz ξ => ?_⟩
    have hc3 : ∀ (τ : X.Ψ) (i j : Fin r), (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) →
        (0 : ℝ) ≤ (((3 • Xa.L - 2 • deMul X.Ψ r X.p0 s - kapW X.toData) τ j : ℤ) : ℝ) -
          (((3 • Xa.L - 2 • deMul X.Ψ r X.p0 s - kapW X.toData) τ i : ℤ) : ℝ) := by
      intro τ i j hi hj
      have := cross X.toData hg hp 3 s hsT hr τ i j hi hj
      push_cast at this
      nlinarith
    have h := (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X.toData
      (3 • Xa.L - 2 • deMul X.Ψ r X.p0 s - kapW X.toData) 0 (block_fst X.toData hg 3 s)
      (block_snd X.toData hg 3 s) hc3 x0 ho z hz ξ
    have e := IW.leviM_comb X.toData x0 ho hz ((nd X.toData + 4) • Xa.L - 2 • deMul X.Ψ r X.p0 s) Xa.L
      (nd X.toData + 1) ξ
    rw [e3] at e
    have e' : leviO X.toData x0 (phla X.toData (3 • Xa.L - 2 • deMul X.Ψ r X.p0 s - kapW X.toData)) z ξ =
        leviM X.toData (phla X.toData (3 • Xa.L - 2 • deMul X.Ψ r X.p0 s - kapW X.toData)) x0 z ξ := rfl
    push_cast at e
    linarith
  have hcusp : ∀ P, X.toData.IsBddSec ((nd X.toData + 4) • Xa.L - 2 • deMul X.Ψ r X.p0 s) P →
      P ∈ X.toData.SS ((nd X.toData + 4) • Xa.L - 2 • deMul X.Ψ r X.p0 s) := fun P hP =>
    GlobalTheory.ThetaRecordCompare.cusp_of_gaps hn h0 hr (gaps_G X.toData hg _ s)
      (pair_G X.toData hp _ s (by omega) hsT hT1 h0 hr) hP
  obtain ⟨F, hF, hv⟩ := GlobalTheory.InterpWeight.interp_weight (E := E)
    ⟨normFactor_rightBorel_holds, normFactor_leftAction_holds, pointwiseNorm_invariance_holds⟩ poin_holds extFStatement_holds measInv_holds
    vanishAtS_holds KapPf.kappa_statement_holds r X.toData Xa Fl _ (GlobalTheory.ClosedDiscontinuity.propDisc_closed _ _)
    hmar hstr hcusp (fun _ => 1)
  exact ⟨F, hF.1.1, Fl.xs ⟨0, hδ⟩, Fl.xs_mem _, by rw [hv]; exact one_ne_zero⟩

end GlobalTheory.ShareSection
