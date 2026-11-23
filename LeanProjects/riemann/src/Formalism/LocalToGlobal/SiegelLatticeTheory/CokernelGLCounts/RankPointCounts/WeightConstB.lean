import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence

noncomputable section

namespace Formalism.L2.SG.WConst

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.RealObj Formalism.MainNotions.S.LocalSplitGroups

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Blocks

def eSum {K : Type} (r : ℕ) : ℕ → List (ℕ × K) → ℕ
  | _, [] => 0
  | b, (s, _) :: rest => s * (2 * (r + 1 - (b + s - 1)) + s - 1) + eSum r (b + s) rest

theorem eSum_arith (s n : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ n) :
    s * (2 * (n - s) + s - 1) + (n - s) * (n - s - 1) = n * (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = k + 1 + m := ⟨n - (k + 1), by omega⟩
  have e0 : k + 1 + m - (k + 1) = m := by omega
  have e1 : 2 * m + (k + 1) - 1 = 2 * m + k := by omega
  have e2 : k + 1 + m - 1 = k + m := by omega
  rw [e0, e1, e2]
  rcases m with _ | m
  · simp only [Nat.zero_sub, mul_zero, zero_mul, add_zero]
    ring
  · rw [show m + 1 - 1 = m by omega]
    ring

theorem eSum_eq {K : Type} (r : ℕ) : ∀ (b : ℕ) (P : List (ℕ × K)), 1 ≤ b → (∀ c ∈ P, 1 ≤ c.1) →
    b + (P.map Prod.fst).sum = r + 2 → eSum r b P = (r + 2 - b) * (r + 1 - b)
  | b, [], hb, _, hs => by
    simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hs
    subst hs
    simp [eSum]
  | b, (s, t) :: rest, hb, hP, hs => by
    have h1 : 1 ≤ s := hP (s, t) (by simp)
    have hP' : ∀ c ∈ rest, 1 ≤ c.1 := fun c hc => hP c (by simp [hc])
    simp only [List.map_cons, List.sum_cons] at hs
    have ih := eSum_eq r (b + s) rest (by omega) hP' (by omega)
    simp only [eSum]
    rw [ih]
    have hsn : s ≤ r + 2 - b := by
      have : 0 ≤ (rest.map Prod.fst).sum := Nat.zero_le _
      omega
    have e1 : r + 1 - (b + s - 1) = (r + 2 - b) - s := by omega
    have e2 : r + 2 - (b + s) = (r + 2 - b) - s := by omega
    have e3 : r + 1 - (b + s) = (r + 2 - b) - s - 1 := by omega
    have e4 : r + 1 - b = (r + 2 - b) - 1 := by omega
    rw [e1, e2, e3, e4]
    exact eSum_arith s (r + 2 - b) h1 hsn

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem norm_phi_sign (v : InfinitePlace X.B.I.F) (k : ℕ) (t : D.host.E) :
    ‖X.B.I.φ v (X.ιE.symm ((-1) ^ k * t))‖ = ‖Formalism.MainNotions.S.embS D (X.pl v) t‖ := by
  rw [X.φ_eq, RingEquiv.apply_symm_apply, map_mul, map_pow, map_neg, map_one, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul]

theorem prod_norm_pl_sq (t : D.host.E) :
    ∏ v : InfinitePlace X.B.I.F, ‖Formalism.MainNotions.S.embS D (X.pl v) t‖ ^ 2 = ((|Algebra.norm ℚ t| : ℚ) : ℝ) := by
  rw [← prod_normSq_embS D t]
  exact Fintype.prod_equiv X.pl _ _ (fun v => rfl)

end Blocks

section Block

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem gNorm_pos : 0 < Formalism.L2.SG.DataInst.gNorm D := by
  unfold Formalism.L2.SG.DataInst.gNorm
  have hg : (0 : ℝ) < ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) := by exact_mod_cast Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D
  exact inv_pos.2 (pow_pos hg _)

theorem block_prod (b s : ℕ) (hs : 1 ≤ s) (k : ℕ) (t : D.host.E) :
    ∏ v : InfinitePlace X.B.I.F, ((D.host.rdE ^ (2 * (D.R.rS + 1) - b - (b + s - 1)))⁻¹ *
        ‖X.B.I.φ v (X.ιE.symm ((-1) ^ k * t))‖) ^ (2 * s * (2 * (D.R.rS + 1 - (b + s - 1)) + s - 1)) =
      (Formalism.L2.SG.DataInst.gNorm D)⁻¹ ^ (s * (2 * (D.R.rS + 1 - (b + s - 1)) + s - 1)) *
        (Formalism.L2.SG.DataInst.nrm (D := D) (nu D.R.rS b (b + s - 1)) t ^
          (s * (D.R.rS + 1 - (b + s - 1)) + s * (s - 1) / 2)) ^ 2 := by
  set X0 := D.R.rS + 1 - (b + s - 1) with hX0
  set ν := 2 * (D.R.rS + 1) - b - (b + s - 1) with hν
  set e := s * (2 * X0 + s - 1) with he
  have hnu : nu D.R.rS b (b + s - 1) = ν := rfl
  have hexp1 : 2 * s * (2 * X0 + s - 1) = 2 * e := by rw [he]; ring
  have hev : 2 * (s * (s - 1) / 2) = s * (s - 1) := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self s)
  have hexp2 : (s * X0 + s * (s - 1) / 2) * 2 = e := by
    have h3 : 2 * X0 + s - 1 = 2 * X0 + (s - 1) := by omega
    rw [he, h3]
    have : (s * X0 + s * (s - 1) / 2) * 2 = 2 * (s * X0) + 2 * (s * (s - 1) / 2) := by ring
    rw [this, hev]
    ring
  rw [hnu, hexp1, ← pow_mul, hexp2]
  have hn : ∀ v : InfinitePlace X.B.I.F, ((D.host.rdE ^ ν)⁻¹ * ‖X.B.I.φ v (X.ιE.symm ((-1) ^ k * t))‖) ^ (2 * e) =
      ((D.host.rdE ^ ν)⁻¹ ^ 2) ^ e * (‖Formalism.MainNotions.S.embS D (X.pl v) t‖ ^ 2) ^ e := by
    intro v
    rw [norm_phi_sign]
    ring
  rw [Finset.prod_congr rfl fun v _ => hn v, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    card_places X, Finset.prod_pow, prod_norm_pl_sq X t]
  unfold Formalism.L2.SG.DataInst.nrm
  have hg := (gNorm_pos (D := D)).ne'
  rw [mul_pow, mul_pow, ← mul_assoc, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hg, one_pow, one_mul]
  congr 1
  simp only [inv_pow, ← pow_mul]
  ring_nf

end Block

section Weight

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem nHead_prod : ∀ (b : ℕ) (P : List (ℕ × D.host.E)), (∀ c ∈ P, 1 ≤ c.1) →
    ∏ v : InfinitePlace X.B.I.F, nHead X v b ((Formalism.L2.SG.DataInst.signAux D.R.rS b P).map Prod.swap) =
      (Formalism.L2.SG.DataInst.gNorm D)⁻¹ ^ eSum D.R.rS b P *
        Formalism.L2.SG.DataInst.blockWeightPhi (D := D) (D.R.rS + 1) b P ^ 2
  | b, [], _ => by
    simp [nHead, Formalism.L2.SG.DataInst.signAux, eSum, Formalism.L2.SG.DataInst.blockWeightPhi]
  | b, (s, t) :: rest, hP => by
    have hs : 1 ≤ s := hP (s, t) (by simp)
    have ih := nHead_prod (b + s) rest (fun c hc => hP c (by simp [hc]))
    simp only [Formalism.L2.SG.DataInst.signAux, List.map_cons, Prod.swap_prod_mk, nHead, eSum,
      Formalism.L2.SG.DataInst.blockWeightPhi]
    rw [Finset.prod_mul_distrib, ih, block_prod X b s hs]
    ring

theorem nW_eq (u u' : D.what₂.Word) (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1))
    (hp : Formalism.L2.SG.DataInst.ptOfList (D := D) (D.R.rS + 1) p = some w) (hγ : ∃ γ, IsPtRep X u u' w γ)
    (hT : TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w)) {c : ℝ} (hc : 0 < c) :
    nW X u u' w = Formalism.L2.SG.MassDataConc.ngFac D / (Formalism.L2.SG.MassDataConc.kapN D * c) *
      (n0 c (D.mem u).A.T (D.mem u').A.T w * Formalism.L2.SG.DataInst.phi (D := D) (D.R.rS + 1) p ^ 2) := by

  unfold Formalism.L2.SG.DataInst.ptOfList at hp
  split_ifs at hp with hL
  obtain rfl := Option.some_injective _ hp
  have hw : ((Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1)).symm ⟨Formalism.L2.SG.DataInst.signPt D.R.rS p, hL⟩).1 =
      (Formalism.L2.SG.DataInst.signAux D.R.rS 1 p).map Prod.swap := rfl
  have hP : ∀ c ∈ p, 1 ≤ c.1 ∧ c.2 ≠ 0 := (Formalism.L2.SG.DataInst.sign_list_mem_nonzero D.R.rS 1 p).1 hL.2
  have hsum : (p.map Prod.fst).sum = D.R.rS + 1 := by
    have := hL.1
    unfold Formalism.L2.SG.DataInst.signPt at this
    rwa [Formalism.L2.SG.DataInst.sign_list_fst] at this
  set w := (Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1)).symm ⟨Formalism.L2.SG.DataInst.signPt D.R.rS p, hL⟩ with hwdef

  have hnW : nW X u u' w = (∏ v, GX X u u' D.host.rdE (gamW X u u' w) v) ^ (D.R.k - 1) *
      ∏ v : InfinitePlace X.B.I.F, nHead X v 1 w.1 := by
    unfold nW
    rw [Finset.prod_mul_distrib, Finset.prod_pow]
  rw [hnW, prod_GX_gamW X u u' w hγ hT, hw, nHead_prod X 1 p (fun c hc => (hP c hc).1),
    eSum_eq D.R.rS 1 p le_rfl (fun c hc => (hP c hc).1) (by rw [hsum]; ring)]

  unfold n0 Formalism.L2.SG.MassDataConc.ngFac Formalism.L2.SG.MassDataConc.kapN Formalism.L2.SG.DataInst.gNorm Formalism.L2.SG.DataInst.phi
  have hgpos : 0 < Formalism.MainNotions.S.Lat.gS D := Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D
  have hg : (0 : ℝ) < ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) := by exact_mod_cast hgpos
  have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
  set gE : D.host.E := (Nat.cast (Formalism.MainNotions.S.Lat.gS D) : D.host.E) ^ D.R.m with hgEdef
  have hgE : gE ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hgpos.ne')
  have hNgE : Algebra.norm ℚ gE ≠ 0 := (Algebra.norm_ne_zero_iff).2 hgE
  set G := Gpt (D.mem u).A.T (D.mem u').A.T w with hGdef
  have hnd : Algebra.norm ℚ (G / gE) = Algebra.norm ℚ G / Algebra.norm ℚ gE := by
    rw [eq_div_iff hNgE, ← map_mul, div_mul_cancel₀ _ hgE]
  have hB : (0 : ℝ) < |((Algebra.norm ℚ gE : ℚ) : ℝ)| := abs_pos.2 (by exact_mod_cast hNgE)
  have hsq : Real.sqrt |((Algebra.norm ℚ (G / gE) : ℚ) : ℝ)| =
      Real.sqrt |((Algebra.norm ℚ G : ℚ) : ℝ)| / Real.sqrt |((Algebra.norm ℚ gE : ℚ) : ℝ)| := by
    rw [hnd, Rat.cast_div, abs_div, Real.sqrt_div' _ hB.le]
  have hcast : ((|Algebra.norm ℚ G| : ℚ) : ℝ) = |((Algebra.norm ℚ G : ℚ) : ℝ)| := Rat.cast_abs _
  rw [hsq, hcast, inv_inv]
  have e1 : (D.R.rS + 2 - 1) * (D.R.rS + 1 - 1) = (D.R.rS + 1) * D.R.rS := by
    rw [show D.R.rS + 2 - 1 = D.R.rS + 1 by omega, show D.R.rS + 1 - 1 = D.R.rS by omega]
  rw [e1]
  have hSB : 0 < Real.sqrt |((Algebra.norm ℚ gE : ℚ) : ℝ)| := Real.sqrt_pos.2 hB
  have h1 : Real.sqrt |((Algebra.norm ℚ gE : ℚ) : ℝ)| ^ (D.R.k - 1) ≠ 0 := pow_ne_zero _ hSB.ne'
  have h2 : D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) * D.R.f) ≠ 0 := pow_ne_zero _ hrd.ne'
  have h3 : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (2 * D.R.f * D.R.rS * (D.R.rS + 1)) ≠ 0 := pow_ne_zero _ hg.ne'
  have h4 : D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1)) ≠ 0 := pow_ne_zero _ hrd.ne'
  rw [div_pow, mul_pow]
  simp only [inv_pow]
  have h5 : ((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f) ^ (D.R.k - 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ h4)
  field_simp
  ring

end Weight

section Const

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

def EligTotPos : Prop :=
  ∀ (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)),
    Formalism.L2.SG.DataInst.Elig t → t.atPt w → TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w)

theorem isPtL_of_ptOfList {p : Formalism.FourierDecayAlt.TB.Pt D.host.E} {w : Point D.host.E (D.R.rS + 1)}
    (hp : Formalism.L2.SG.DataInst.ptOfList (D := D) (D.R.rS + 1) p = some w) : Formalism.L2.S.IsPtL p (D.R.rS + 1) := by
  unfold Formalism.L2.SG.DataInst.ptOfList at hp
  split at hp
  · next h => exact (Formalism.L2.SG.DataInst.isPtL_signPt _ _ _).mp h
  · exact absurd hp (by simp)

theorem ne_zero_of_totPos {x : D.host.E} (h : TotPos x) : x ≠ 0 := by
  intro hx
  have hne : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]
    exact Formalism.MainNotions.InterlacingSignCuts.f_pos D
  obtain ⟨τ⟩ := hne
  have h1 := h τ
  rw [hx, map_zero] at h1
  simp at h1

theorem weightConstC_of {sc : ℝ} {i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k} (c : ℝ)
    (hPR : PtRepExists X u u' sc i0 i0') (hE : EligTotPos X Y u u') :
    Formalism.L2.SG.Pf.RowForm.WeightConstC X Y u u' c := by
  intro hc p w hp ht
  obtain ⟨t, hEl, hat⟩ := ht
  have hT := hE t w hEl hat
  have hγ : ∃ γ, IsPtRep X u u' w γ := by
    obtain ⟨γ, h1, -⟩ := hPR w (fun v => by rw [Gv_zhatO, Gv_ptC]; exact hT (X.pl v))
    exact ⟨γ, h1⟩
  exact ⟨Formalism.L2.SG.DataInst.phi_pos (isPtL_of_ptOfList hp), Formalism.L2.SG.Pf.n0_pos hc (ne_zero_of_totPos hT),
    nW_eq X u u' p w hp hγ hT hc⟩

end Const

end Formalism.L2.SG.WConst
