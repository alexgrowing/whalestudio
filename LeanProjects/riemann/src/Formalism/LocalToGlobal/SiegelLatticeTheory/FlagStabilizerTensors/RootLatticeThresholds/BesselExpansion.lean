import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants

noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.RotatedPoints Formalism.MainNotions.S.Pv.Frames

def BesselExpansionRotated : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ (C1 C2 Cg₀ : ℝ), 2 ≤ Cg₀ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7, ∃ (dist' : ℝ) (A : ℕ),
    QExpAtR D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) dist' A C1 5
        (Aw * ((D.R.rS : ℝ) + 1) ^ 2) ∧
      BpRealR D Ch Cg dist' A C2 5

section Loc

variable (D : D7)

def PlaceOKS (Ch Cg : ℝ) (T T' : ℕ) (b dist dinf : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : Prop :=
  PlaceOKR D Ch Cg T T' b dist v L f μsec ∧ ∀ s, |L.lam s - lamSH D.R (D.hc v) s| ≤ dinf

def BpLocS (Ch Cg dist dinf : ℝ) (A : ℕ) (C : ℝ) (e : ℕ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), PlaceOKS D Ch Cg T T' b dist dinf v L f μsec →
    ∀ p : Point ℂ (D.R.rS + 1), Gpt (T : ℝ) (T' : ℝ) p ≠ 0 →
      ENNReal.ofReal (ptWeight D.R.k D.R.rS (T : ℝ) (T' : ℝ) p) * orbSq L f p ≤
        ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) * max 1 (1 / Gpt (T : ℝ) (T' : ℝ) p) ^ A) *
          jNorm2 L f μsec

def BpRealS (Ch Cg dist dinf : ℝ) (A : ℕ) (C : ℝ) (e : ℕ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), PlaceOKS D Ch Cg T T' b dist dinf v L f μsec →
    ∀ γ : Point D.host.E (D.R.rS + 1), IsBPt D T T' γ →
      ENNReal.ofReal (nLoc D T T' v γ) * orbSq L f (turnPt (ptLoc D v γ)) ≤
        ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) * max 1 (1 / absV D v (Gglob D T T' γ)) ^ A) *
          jNorm2 L f μsec

def QExpAtS (Ch Cg dist : ℝ) (P : ∀ (T T' : ℕ) (b : ℝ), BData D Ch Cg T T' b dist → Prop) (dist' dinf' : ℝ) (A : ℕ)
    (C : ℝ) (e : ℕ) (p : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b dist), P T T' b X →
    ∀ γ : Point D.host.E (D.R.rS + 1), IsBPt D T T' γ → ∀ v,
    ∃ (n : ℕ) (a : Fin n → ℝ) (L' : Fin n → LocBessel D.R.k D.R.rS)
      (f' : ∀ i, Mx D.R.k D.R.rS → ((L' i).Wq →L[ℂ] (L' i).Wp))
      (μ' : Fin n → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ),
      (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) ∧
      (∀ i, PlaceOKS D Ch Cg T T' b dist' dinf' v (L' i) (f' i) (μ' i)) ∧
      (∀ i, jNorm2 (L' i) (f' i) (μ' i) ≤ jNorm2 (X.L v) (X.f v) (X.μsec v)) ∧
      ENNReal.ofReal (wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p) *
          orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ)) ≤
        (∑ i, ENNReal.ofReal (a i) *
          (ENNReal.ofReal (nLoc D T T' v γ) * orbSq (L' i) (f' i) (turnPt (ptLoc D v γ))) ^ ((1 : ℝ) / 2)) ^ 2

variable {D}

theorem max_one_div_mul_le (α g : ℝ) (hα : 0 < α) (hg : 0 < g) :
    max 1 (1 / (α * g)) ≤ max 1 α⁻¹ * max 1 (1 / g) := by
  refine max_le ?_ ?_
  · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  · have e1 : 1 / (α * g) = α⁻¹ * (1 / g) := by field_simp
    rw [e1]
    exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (by positivity) (le_trans zero_le_one (le_max_left _ _))

theorem frame_bounds {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} {v : D.what₂.Tau} {L : LocBessel D.R.k D.R.rS}
    {f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)} {μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hCg : 2 ≤ Cg) (hok : PlaceOKR D Ch Cg T T' b dist v L f μsec) :
    2 ≤ b ∧ 1 ≤ b ^ (3 + Ch) ∧ D.host.rdE ≤ b ^ (3 + Ch) := by
  obtain ⟨⟨hk, -, -, -, -, hStd, -, -⟩, -⟩ := hok
  have hb2 : 2 ≤ b := by
    have h1 := b_ge_of_StdHyp0 hk hStd.to0
    have h2 : (1 : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1))
    nlinarith
  have hka : 0 < kaRe D := hStd.2.2.2.1
  have hk1 : kaRe D ≤ b ^ Ch := hStd.2.2.2.2.1
  have hk2 : (kaRe D)⁻¹ ≤ b ^ Ch := hStd.2.2.2.2.2.1
  have hbC : 1 ≤ b ^ Ch := by
    rcases le_total 1 (kaRe D) with h | h
    · exact h.trans hk1
    · exact ((one_le_inv₀ hka).2 h).trans hk2
  have hb0 : 0 < b := by linarith
  have hb3 : 1 ≤ b ^ (3 + Ch) := by
    rw [Real.rpow_add hb0]
    have : 1 ≤ b ^ (3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    nlinarith
  exact ⟨hb2, hb3, Formalism.MainNotions.TheoremBConstants.rdE_le D b Ch hb2 hka hk2⟩

theorem ch_nonneg {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} {v : D.what₂.Tau} {L : LocBessel D.R.k D.R.rS}
    {f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)} {μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hCg : 2 ≤ Cg) (hok : PlaceOKR D Ch Cg T T' b dist v L f μsec) : 0 ≤ Ch := by
  have hb2 := (frame_bounds hCg hok).1
  obtain ⟨⟨-, -, -, -, -, hStd, -, -⟩, -⟩ := hok
  have hka : 0 < kaRe D := hStd.2.2.2.1
  have hk1 : kaRe D ≤ b ^ Ch := hStd.2.2.2.2.1
  have hk2 : (kaRe D)⁻¹ ≤ b ^ Ch := hStd.2.2.2.2.2.1
  by_contra hc
  push_neg at hc
  have hlt : b ^ Ch < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hc
  rcases le_total 1 (kaRe D) with h | h
  · linarith
  · have := (one_le_inv₀ hka).2 h
    linarith

theorem bound_at {Ch Cg dist C : ℝ} {A e : ℕ} {T T' : ℕ} {b : ℝ} {v : D.what₂.Tau} {L : LocBessel D.R.k D.R.rS}
    {f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)} {μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hCg : 2 ≤ Cg) (hok : PlaceOKR D Ch Cg T T' b dist v L f μsec)
    (γ : Point D.host.E (D.R.rS + 1)) (hγ : IsBPt D T T' γ) (p : Point ℂ (D.R.rS + 1))
    (hGp : Gpt (T : ℝ) (T' : ℝ) p = Gpt (T : ℝ) (T' : ℝ) (ptLoc D v γ))
    (hwp : ptWeight D.R.k D.R.rS (T : ℝ) (T' : ℝ) p = nLoc D T T' v γ)
    (hB : Gpt (T : ℝ) (T' : ℝ) p ≠ 0 →
      ENNReal.ofReal (ptWeight D.R.k D.R.rS (T : ℝ) (T' : ℝ) p) * orbSq L f p ≤
        ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) * max 1 (1 / Gpt (T : ℝ) (T' : ℝ) p) ^ A) *
          jNorm2 L f μsec) :
    ENNReal.ofReal (nLoc D T T' v γ) * orbSq L f p ≤
      ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) *
          (((b ^ (3 + Ch)) ^ ((2 * D.R.rS + 2) ^ 2)) ^ A * max 1 (1 / absV D v (Gglob D T T' γ)) ^ A)) *
        jNorm2 L f μsec := by
  by_cases h0 : orbSq L f p = 0
  · simp [h0]
  obtain ⟨hb2, hR1, hRd⟩ := frame_bounds hCg hok
  obtain ⟨g, hg⟩ := exists_rep_of_orbSq L f p h0
  have hG0 := GPoint_nonneg_of_rep L p g hg
  rw [hok.2.2.2.2.1, hok.2.2.2.2.2] at hG0
  set α : ℝ := ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 with hαdef
  set gv : ℝ := Complex.normSq (plEmb D v (leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl)) -
    (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _))) with hgvdef
  have hGeq : Gpt (T : ℝ) (T' : ℝ) p = α * gv := by rw [hGp, GPoint_loc]
  have hα : 0 < α := by
    have := Finset.prod_pos (s := Finset.univ) (fun (i : Fin D.R.rS) _ => alf_pos D i)
    positivity
  have hgvC : plEmb D v (Gglob D T T' γ) = (gv : ℂ) := plEmb_Gglob D T T' v γ
  have hgv0 : gv ≠ 0 := by
    intro h
    apply (map_ne_zero (plEmb D v)).2 hγ.2.1
    rw [hgvC, h, Complex.ofReal_zero]
  have hGne : Gpt (T : ℝ) (T' : ℝ) p ≠ 0 := by rw [hGeq]; exact mul_ne_zero hα.ne' hgv0
  have hGpos : 0 < Gpt (T : ℝ) (T' : ℝ) p := lt_of_le_of_ne hG0 (Ne.symm hGne)
  have hgpos : 0 < gv := by
    by_contra hc
    push_neg at hc
    nlinarith
  have habs : absV D v (Gglob D T T' γ) = gv := by
    unfold absV
    rw [hgvC, Complex.norm_real, Real.norm_of_nonneg hgpos.le]
  have main := hB hGne
  rw [hwp] at main
  refine main.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  rw [habs, hGeq]
  have hb0 : 0 < b := by linarith
  have hm1 : max 1 α⁻¹ ≤ (b ^ (3 + Ch)) ^ ((2 * D.R.rS + 2) ^ 2) := by
    refine max_le (one_le_pow₀ hR1) ?_
    exact Formalism.MainNotions.TheoremBConstants.alfProd_inv_le D (b ^ (3 + Ch)) hR1 hRd D.R.rS (by omega)
  have hmax := max_one_div_mul_le α gv hα hgpos
  have hpow : max 1 (1 / (α * gv)) ^ A ≤
      ((b ^ (3 + Ch)) ^ ((2 * D.R.rS + 2) ^ 2)) ^ A * max 1 (1 / gv) ^ A := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) (hmax.trans ?_) A
    exact mul_le_mul_of_nonneg_right hm1 (le_trans zero_le_one (le_max_left _ _))
  have hbC : 0 ≤ b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) := Real.rpow_nonneg hb0.le _
  exact mul_le_mul_of_nonneg_left hpow hbC

theorem frame_cost {b Ch CA : ℝ} {A e r : ℕ} (hb : 1 ≤ b) (hCh : 0 ≤ Ch) (he : 4 ≤ e)
    (hA : (A : ℝ) ≤ CA * ((2 * r + 2 : ℕ) : ℝ) ^ 2) :
    ((b ^ (3 + Ch)) ^ ((2 * r + 2) ^ 2)) ^ A ≤ b ^ ((3 + Ch) * CA * ((2 * r + 2 : ℕ) : ℝ) ^ e) := by
  have hb0 : 0 < b := by linarith
  have hm1 : (1 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)
  have hCA : 0 ≤ CA := by
    by_contra hc
    push_neg at hc
    have h1 : CA * ((2 * r + 2 : ℕ) : ℝ) ^ 2 < 0 := mul_neg_of_neg_of_pos hc (by positivity)
    have h2 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    linarith
  have e1 : ((b ^ (3 + Ch)) ^ ((2 * r + 2) ^ 2)) ^ A =
      b ^ ((3 + Ch) * (((2 * r + 2 : ℕ) : ℝ) ^ 2 * (A : ℝ))) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
    congr 1
    push_cast
    ring
  rw [e1]
  refine Real.rpow_le_rpow_of_exponent_le hb ?_
  have h1 : ((2 * r + 2 : ℕ) : ℝ) ^ 2 * (A : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) ^ 2 * (CA * ((2 * r + 2 : ℕ) : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have h2 : ((2 * r + 2 : ℕ) : ℝ) ^ 4 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ e := pow_le_pow_right₀ hm1 he
  have h3 : ((2 * r + 2 : ℕ) : ℝ) ^ 2 * (CA * ((2 * r + 2 : ℕ) : ℝ) ^ 2) = CA * ((2 * r + 2 : ℕ) : ℝ) ^ 4 := by ring
  have h4 : CA * ((2 * r + 2 : ℕ) : ℝ) ^ 4 ≤ CA * ((2 * r + 2 : ℕ) : ℝ) ^ e := mul_le_mul_of_nonneg_left h2 hCA
  have h5 : ((2 * r + 2 : ℕ) : ℝ) ^ 2 * (A : ℝ) ≤ CA * ((2 * r + 2 : ℕ) : ℝ) ^ e := by linarith
  have h6 := mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤ 3 + Ch)
  linarith

theorem cost_step {b C Ch CA G : ℝ} {A e r : ℕ} (hb2 : 2 ≤ b) (hCh : 0 ≤ Ch) (he : 4 ≤ e)
    (hA : (A : ℝ) ≤ CA * ((2 * r + 2 : ℕ) : ℝ) ^ 2) :
    b ^ (C * ((2 * r + 2 : ℕ) : ℝ) ^ e) * (((b ^ (3 + Ch)) ^ ((2 * r + 2) ^ 2)) ^ A * max 1 (1 / G) ^ A) ≤
      b ^ ((C + (3 + Ch) * CA) * ((2 * r + 2 : ℕ) : ℝ) ^ e) * max 1 (1 / G) ^ A := by
  have hb0 : 0 < b := by linarith
  have hc := frame_cost (b := b) (r := r) (by linarith) hCh he hA
  have hM : 0 ≤ max 1 (1 / G) ^ A := pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  calc b ^ (C * ((2 * r + 2 : ℕ) : ℝ) ^ e) * (((b ^ (3 + Ch)) ^ ((2 * r + 2) ^ 2)) ^ A * max 1 (1 / G) ^ A)
      ≤ b ^ (C * ((2 * r + 2 : ℕ) : ℝ) ^ e) *
        (b ^ ((3 + Ch) * CA * ((2 * r + 2 : ℕ) : ℝ) ^ e) * max 1 (1 / G) ^ A) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hM) (Real.rpow_nonneg hb0.le _)
    _ = b ^ ((C + (3 + Ch) * CA) * ((2 * r + 2 : ℕ) : ℝ) ^ e) * max 1 (1 / G) ^ A := by
        rw [← mul_assoc, ← Real.rpow_add hb0]
        congr 2
        ring

theorem bpRealS_of_loc {Ch Cg dist dinf C CA : ℝ} {A e : ℕ} (hCg : 2 ≤ Cg) (he : 4 ≤ e)
    (hA : (A : ℝ) ≤ CA * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) (h : BpLocS D Ch Cg dist dinf A C e) :
    BpRealS D Ch Cg dist dinf A (C + (3 + Ch) * CA) e := by
  intro T T' b v L f μsec hok γ hγ
  have hb := bound_at (C := C) (A := A) (e := e) hCg hok.1 γ hγ (turnPt (ptLoc D v γ)) (GPoint_turnPt _ _ _)
    (by unfold nLoc; exact ptWeight_turnPt _ _ _ _ _) (h T T' b v L f μsec hok _)
  refine hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  exact cost_step (frame_bounds hCg hok.1).1 (ch_nonneg hCg hok.1) he hA

theorem onePlaceR_of_expS {Ch Cg dist dist' dinf' C1 C2 p : ℝ} {A e : ℕ}
    {P : ∀ (T T' : ℕ) (b : ℝ), BData D Ch Cg T T' b dist → Prop}
    (hCg : 2 ≤ Cg) (hQ : QExpAtS D Ch Cg dist P dist' dinf' A C1 e p) (hB : BpRealS D Ch Cg dist' dinf' A C2 e) :
    OnePlaceR D Ch Cg dist P A (2 * C1 + C2) e p := by
  intro T T' b X hP γ hγ v
  obtain ⟨n, a, L', f', μ', ha, hsum, hok, hJ, hexp⟩ := hQ T T' b X hP γ hγ v
  have hb := b_pos_of_dataR hCg X v
  set K : ENNReal := ENNReal.ofReal (b ^ (C2 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) *
    max 1 (1 / absV D v (Gglob D T T' γ)) ^ A) with hK
  set J : ENNReal := jNorm2 (X.L v) (X.f v) (X.μsec v) with hJdef
  have hterm : ∀ i, (ENNReal.ofReal (nLoc D T T' v γ) * orbSq (L' i) (f' i) (turnPt (ptLoc D v γ))) ^ ((1 : ℝ) / 2) ≤
      (K * J) ^ ((1 : ℝ) / 2) := by
    intro i
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    exact (hB T T' b v (L' i) (f' i) (μ' i) (hok i) γ hγ).trans (mul_le_mul_of_nonneg_left (hJ i) bot_le)
  have hsum' : ∑ i, ENNReal.ofReal (a i) *
      (ENNReal.ofReal (nLoc D T T' v γ) * orbSq (L' i) (f' i) (turnPt (ptLoc D v γ))) ^ ((1 : ℝ) / 2) ≤
      ENNReal.ofReal (∑ i, a i) * (K * J) ^ ((1 : ℝ) / 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ha i), Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hterm i) bot_le
  have hsq := pow_le_pow_left₀ bot_le hsum' 2
  rw [mul_pow, sqrt_sq_enn] at hsq
  have hA : ENNReal.ofReal (∑ i, a i) ^ 2 ≤ ENNReal.ofReal (b ^ (2 * C1 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e)) := by
    rw [← ENNReal.ofReal_pow (Finset.sum_nonneg fun i _ => ha i)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (∑ i, a i) ^ 2 ≤ (b ^ (C1 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e)) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => ha i) hsum 2
      _ = b ^ (2 * C1 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
          congr 1
          push_cast
          ring
  have hfin : ENNReal.ofReal (b ^ (2 * C1 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e)) * K =
      ENNReal.ofReal (b ^ ((2 * C1 + C2) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) *
        max 1 (1 / absV D v (Gglob D T T' γ)) ^ A) := by
    rw [hK, ← ENNReal.ofReal_mul (Real.rpow_nonneg hb.le _), ← mul_assoc, ← Real.rpow_add hb]
    congr 3
    ring
  calc _ ≤ _ := hexp
    _ ≤ ENNReal.ofReal (∑ i, a i) ^ 2 * (K * J) := hsq
    _ ≤ ENNReal.ofReal (b ^ (2 * C1 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e)) * (K * J) := mul_le_mul_of_nonneg_right hA bot_le
    _ = _ := by rw [← mul_assoc, hfin]

end Loc

def BesselExpansionLocal : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ (C1 C2 CA Cinf Cg₀ : ℝ), 2 ≤ Cg₀ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7,
    ∃ (dist' : ℝ) (A : ℕ), (A : ℝ) ≤ CA * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ∧
      QExpAtS D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) dist'
          (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C1 5 (Aw * ((D.R.rS : ℝ) + 1) ^ 2) ∧
        BpLocS D Ch Cg dist' (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C2 5

theorem uniformTheoremB_of_local (h : BesselExpansionLocal) : WeightedBoundRotatedUniform := by
  intro Aw Ch hAw
  obtain ⟨C1, C2, CA, Cinf, Cg₀, h2, H⟩ := h Aw Ch hAw
  refine ⟨2 * C1 + (C2 + (3 + Ch) * CA) + 6, Cg₀, fun Cg hCg D => ?_⟩
  obtain ⟨dist', A, hA, hQ, hB⟩ := H Cg hCg D
  have hCg2 : 2 ≤ Cg := le_trans h2 hCg
  exact weighted_bound_rotated_of_one_place hCg2 (onePlaceR_of_expS hCg2 hQ (bpRealS_of_loc hCg2 (by norm_num) hA hB))

end Formalism.L2.SG.Pf.BesselExpansion
