import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BesselShellMomentBounds Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.L2.SG.RowsConc

namespace Formalism.L2.SG.NGCut.LeadingMinorIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pt

variable {K : Type} [Field K]

private theorem sub_mul_lemma {R : Type*} [CommRing R] {d : ℕ} (A B : Matrix (Fin d) (Fin d) R) (q : ℕ)
    (h : ∀ i j k : Fin d, (i : ℕ) < q → (j : ℕ) < q → q ≤ (k : ℕ) → A i k * B k j = 0) :
    (A * B).submatrix (fun i : {i : Fin d // (i : ℕ) < q} => i.1) (fun i : {i : Fin d // (i : ℕ) < q} => i.1) =
      A.submatrix (fun i : {i : Fin d // (i : ℕ) < q} => i.1) (fun i : {i : Fin d // (i : ℕ) < q} => i.1) *
        B.submatrix (fun i : {i : Fin d // (i : ℕ) < q} => i.1) (fun i : {i : Fin d // (i : ℕ) < q} => i.1) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hz : ∑ k : {x : Fin d // ¬ (x : ℕ) < q}, A i.1 k.1 * B k.1 j.1 = 0 :=
    Finset.sum_eq_zero (fun k _ => h _ _ _ i.2 j.2 (not_lt.mp k.2))
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k : Fin d => (k : ℕ) < q), hz, add_zero]

private theorem det_lo_lemma_2 {R : Type*} [CommRing R] {d : ℕ} (L : Matrix (Fin d) (Fin d) R)
    (hL : ∀ i j : Fin d, (i < j → L i j = 0) ∧ (i = j → L i j = 1)) (q : ℕ) :
    (L.submatrix (fun i : {i : Fin d // (i : ℕ) < q} => i.1) (fun i : {i : Fin d // (i : ℕ) < q} => i.1)).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun i j hij => (hL i.1 j.1).1 (OrderDual.toDual_lt_toDual.mp hij))]
  exact Finset.prod_eq_one (fun i _ => (hL i.1 i.1).2 rfl)

private theorem det_up_lemma_3 {R : Type*} [CommRing R] {d : ℕ} (U : Matrix (Fin d) (Fin d) R)
    (hU : ∀ i j : Fin d, (j < i → U i j = 0) ∧ (i = j → U i j = 1)) (q : ℕ) :
    (U.submatrix (fun i : {i : Fin d // (i : ℕ) < q} => i.1) (fun i : {i : Fin d // (i : ℕ) < q} => i.1)).det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => (hU i.1 j.1).1 hij)]
  exact Finset.prod_eq_one (fun i _ => (hU i.1 i.1).2 rfl)

theorem lead_cell {d : ℕ} (Z : Matrix (Fin d) (Fin d) K) (w : Point K d) (h : IsInCell Z w) (q : ℕ) :
    leadingPrincipalMinor (ptMat w) q = leadingPrincipalMinor Z q := by
  obtain ⟨L, U, hL, hU, rfl⟩ := h
  unfold leadingPrincipalMinor
  rw [sub_mul_lemma (L * ptMat w) U q ?_, sub_mul_lemma L (ptMat w) q ?_, Matrix.det_mul, Matrix.det_mul,
    det_lo_lemma_2 L hL q, det_up_lemma_3 U hU q, one_mul, mul_one]
  · intro i j k _ _ hk
    rw [(hL i k).1 (show (i : ℕ) < (k : ℕ) by omega), zero_mul]
  · intro i j k _ hj hk
    rw [(hU k j).1 (show (j : ℕ) < (k : ℕ) by omega), mul_zero]

theorem endMin_eq {r : ℕ} (w : Point K (r + 1)) (a : Fin (toPts w).1.length) :
    endMin (toPts w) a = leadingPrincipalMinor (ptMat w) (endIdx (toPts w) a) := by
  unfold endMin endIdx
  rw [ptMat_eq]
  exact E5minor_eq (toComp w) (toT w) a

theorem dlast_eq {r : ℕ} (w : Point K (r + 1)) : DlastPt (toPts w) = leadingPrincipalMinor (ptMat w) (r + 1) := by
  have hl : 0 < (toPts w).1.length := Composition.length_pos_of_pos (toPts w).1 (Nat.succ_pos r)
  unfold DlastPt
  rw [dif_pos hl, endMin_eq]
  congr 1
  show (toPts w).1.sizeUpTo ((toPts w).1.length - 1 + 1) = r + 1
  rw [Nat.sub_add_cancel hl, Composition.sizeUpTo_length]

theorem dr_eq {r : ℕ} (w : Point K (r + 1)) : DrPt (toPts w) = leadingPrincipalMinor (ptMat w) r := by
  have hlen : 0 < (toPts w).1.length := (toPts w).1.length_pos_of_pos (Nat.succ_pos r)
  have hsum := (toPts w).1.sizeUpTo_succ' ⟨(toPts w).1.length - 1, by omega⟩
  simp only [Nat.sub_add_cancel hlen, Composition.sizeUpTo_length] at hsum
  unfold DrPt
  rw [dif_pos hlen]
  split_ifs with h1 h2
  · rw [endMin_eq]
    congr 1
    show (toPts w).1.sizeUpTo (((toPts w).1.length - 2) + 1) = r
    have e : (toPts w).1.length - 2 + 1 = (toPts w).1.length - 1 := by omega
    rw [e]
    omega
  · have hl1 : (toPts w).1.length = 1 := by omega
    have h0 : (toPts w).1.sizeUpTo ((toPts w).1.length - 1) = 0 := by
      rw [hl1]; exact Composition.sizeUpTo_zero _
    have hr : r = 0 := by omega
    subst hr
    unfold leadingPrincipalMinor
    have : IsEmpty {i : Fin 1 // (i : ℕ) < 0} := ⟨fun i => Nat.not_lt_zero _ i.2⟩
    rw [Matrix.det_isEmpty]
  · symm
    rw [ptMat_eq]
    refine Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aVanish K (r + 1) (toComp w) (toT w) r (by omega) fun p hp => ?_
    have hb := (toPts w).1.one_le_blocksFun ⟨(toPts w).1.length - 1, by omega⟩
    have hb2 : 2 ≤ (toPts w).1.blocksFun ⟨(toPts w).1.length - 1, by omega⟩ := by omega
    by_cases hpl : (toPts w).1.length ≤ p
    · have := Composition.sizeUpTo_ofLength_le (toComp w) p hpl
      omega
    · have hmono := (toComp w).monotone_sizeUpTo (show p ≤ (toPts w).1.length - 1 by omega)
      have e : (toComp w).sizeUpTo ((toPts w).1.length - 1) = (toPts w).1.sizeUpTo ((toPts w).1.length - 1) := rfl
      omega

end Pt

section Minors

variable {D : D7}

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

theorem leadingMinor_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ} (M : Matrix (Fin d) (Fin d) R)
    (q : ℕ) : leadingPrincipalMinor (M.map f) q = f (leadingPrincipalMinor M q) := by
  unfold leadingPrincipalMinor
  rw [RingHom.map_det]
  rfl

theorem frame_smul_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (hz : F.fl.z ∈ Λ) (hX : XLam Λ F = XS D F.fl) (a : Fin (D.R.rS + 1)) :
    ∀ x ∈ (((dI D ^ (D.R.rS - (a : ℕ)) : Ideal (𝓞 D.host.E)) : FI))⁻¹, x • frame F a ∈ Λ := by
  induction a using Fin.lastCases with
  | last =>
    intro x hx
    simp only [Fin.val_last, Nat.sub_self, pow_zero, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top,
      inv_one] at hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    rw [Formalism.MainNotions.LatticeGluingRadicals.a_frame_last, algebraMap_smul]
    exact Λ.smul_mem o hz
  | cast a =>
    intro x hx
    rw [Formalism.MainNotions.LatticeGluingRadicals.a_frame_castSucc]
    have ha : (a : ℕ) ≤ D.R.rS := a.2.le
    have hx' : x ∈ ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) := by
      have e : -((D.R.rS : ℤ) - (a : ℕ)) = -(((D.R.rS - (a : ℕ) : ℕ) : ℤ)) := by
        push_cast [Nat.cast_sub ha]; ring
      rw [e, zpow_neg, zpow_natCast,
        show ddS D = ((dI D : Ideal (𝓞 D.host.E)) : FI) from rfl, ← FractionalIdeal.coeIdeal_pow]
      simpa using hx
    have h : x • F.fl.e a ∈ XLam Λ F := by
      rw [hX]; exact Submodule.subset_span ⟨a, x, hx', rfl⟩
    exact h.1

theorem zhatOM_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (hz : F.fl.z ∈ Λ) (hX : XLam Λ F = XS D F.fl) (hz' : F'.fl.z ∈ Λ) (hX' : XLam Λ F' = XS D F'.fl)
    (a b : Fin (D.R.rS + 1)) :
    ∃ o ∈ dI D ^ ((D.R.rS - (a : ℕ)) + (D.R.rS - (b : ℕ))), (o : D.host.E) = ZhatOM (ZhatL F F') a b := by
  obtain ⟨o, ho, e⟩ := hT_mem hun _ _ (frame F a) (frame F' b) (frame_smul_mem F hz hX a)
    (frame_smul_mem F' hz' hX' b)
  refine ⟨(-1) ^ (D.R.rS - (b : ℕ)) * o, Ideal.mul_mem_left _ _ ho, ?_⟩
  have hZ : ZhatL F F' a b = (VS D).hT (frame F a) (frame F' b) := rfl
  show _ = (-1 : D.host.E) ^ (D.R.rS - b.val) * ZhatL F F' a b
  rw [hZ, ← e]
  push_cast
  rfl

private theorem gauss_lemma_5 (r q : ℕ) (hq : q ≤ r + 1) :
    2 * ∑ i ∈ Finset.range q, (r - i) = q * (2 * r + 1 - q) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, mul_add, ih (by omega)]
    obtain ⟨k, rfl⟩ : ∃ k, r = q + k := ⟨r - q, by omega⟩
    rw [show 2 * (q + k) + 1 - q = q + 2 * k + 1 by omega, show q + k - q = k by omega,
      show 2 * (q + k) + 1 - (q + 1) = q + 2 * k by omega]
    ring

private theorem e4_cast_lemma_6 {R : Type*} [CommRing R] {N : ℕ} (A : Matrix (Fin N) (Fin N) R) (q : ℕ) (hq : q ≤ N) :
    leadingPrincipalMinor A q = (A.submatrix (Fin.castLE hq) (Fin.castLE hq)).det := by
  unfold leadingPrincipalMinor
  let e : Fin q ≃ {i : Fin N // (i : ℕ) < q} :=
    { toFun := fun k => ⟨Fin.castLE hq k, k.2⟩, invFun := fun i => ⟨i.1, i.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem lead_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (hz : F.fl.z ∈ Λ) (hX : XLam Λ F = XS D F.fl) (hz' : F'.fl.z ∈ Λ) (hX' : XLam Λ F' = XS D F'.fl)
    (q : ℕ) (hq : q ≤ D.R.rS + 1) :
    ∃ o ∈ dI D ^ (q * (2 * D.R.rS + 1 - q)), (o : D.host.E) = leadingPrincipalMinor (ZhatOM (ZhatL F F')) q := by
  choose O hO hOe using fun a b => zhatOM_mem hun F F' hz hX hz' hX' a b
  refine ⟨leadingPrincipalMinor (Matrix.of O) q, ?_, ?_⟩
  · rw [e4_cast_lemma_6 _ q hq, Matrix.det_apply']
    refine Ideal.sum_mem _ (fun σ _ => ?_)
    have hp := Ideal.prod_mem_prod (s := Finset.univ)
      (I := fun i : Fin q => dI D ^ ((D.R.rS - ((σ i : Fin q) : ℕ)) + (D.R.rS - (i : ℕ))))
      (x := fun i : Fin q => O (Fin.castLE hq (σ i)) (Fin.castLE hq i))
      (fun i _ => by
        have h0 := hO (Fin.castLE hq (σ i)) (Fin.castLE hq i)
        simpa only [Fin.coe_castLE] using h0)
    rw [Finset.prod_pow_eq_pow_sum] at hp
    have he : ∑ i : Fin q, ((D.R.rS - ((σ i : Fin q) : ℕ)) + (D.R.rS - (i : ℕ))) = q * (2 * D.R.rS + 1 - q) := by
      rw [Finset.sum_add_distrib, Equiv.sum_comp σ (fun i : Fin q => D.R.rS - (i : ℕ)), ← two_mul,
        Fin.sum_univ_eq_sum_range (fun i => D.R.rS - i) q]
      exact gauss_lemma_5 _ _ hq
    rw [he] at hp
    exact Ideal.mul_mem_left _ _ hp
  · show algebraMap (𝓞 D.host.E) D.host.E (leadingPrincipalMinor (Matrix.of O) q) = _
    rw [← leadingMinor_map]
    congr 1
    ext a b
    exact hOe a b

private theorem e4_lm_lemma_4 {N : ℕ} (A : Matrix (Fin N) (Fin N) D.host.E) (q : ℕ) (hq : q ≤ N) :
    leadingPrincipalMinor A q = leadMinorE A q := by
  unfold leadingPrincipalMinor leadMinorE
  rw [dif_pos hq]
  let e : Fin q ≃ {i : Fin N // (i : ℕ) < q} :=
    { toFun := fun k => ⟨Fin.castLE hq k, k.2⟩, invFun := fun i => ⟨i.1, i.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem lead_ZhatOM {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) D.host.E) (q : ℕ) (hq : q ≤ r + 1) :
    leadingPrincipalMinor (ZhatOM Z) q = (∏ b : Fin q, (-1 : D.host.E) ^ (r - (b : ℕ))) * leadMinorE Z q := by
  rw [e4_lm_lemma_4 _ q hq]
  unfold leadMinorE
  rw [dif_pos hq, dif_pos hq]
  have hM : (ZhatOM Z).submatrix (Fin.castLE hq) (Fin.castLE hq) =
      Z.submatrix (Fin.castLE hq) (Fin.castLE hq) * Matrix.diagonal (fun b : Fin q => (-1 : D.host.E) ^ (r - (b : ℕ))) := by
    ext a b
    simp [ZhatOM, Matrix.mul_diagonal, mul_comm]
  rw [hM, Matrix.det_mul, Matrix.det_diagonal, mul_comm]

theorem sign_mul_star {r q : ℕ} :
    (∏ b : Fin q, (-1 : D.host.E) ^ (r - (b : ℕ))) * star (∏ b : Fin q, (-1 : D.host.E) ^ (r - (b : ℕ))) = 1 := by
  rw [star_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (fun b _ => by rw [star_pow, star_neg, star_one, ← mul_pow, neg_one_mul, neg_neg, one_pow])

theorem gpt_eq {T T' : ℕ} (F : LFlag (VS D) D.R.rS (T : D.host.E)) (F' : LFlag (VS D) D.R.rS (T' : D.host.E))
    (w : Point D.host.E (D.R.rS + 1)) (h : IsInCell (ZhatOM (ZhatL F F')) w) :
    GPt (T * T') (toPts w) = Gval F F' := by
  have h1 : DlastPt (toPts w) =
      (∏ b : Fin (D.R.rS + 1), (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * leadMinorE (ZhatL F F') (D.R.rS + 1) := by
    rw [dlast_eq w, lead_cell _ w h (D.R.rS + 1), lead_ZhatOM _ (D.R.rS + 1) le_rfl]
  have h2 : DrPt (toPts w) =
      (∏ b : Fin D.R.rS, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * leadMinorE (ZhatL F F') D.R.rS := by
    rw [dr_eq w, lead_cell _ w h D.R.rS, lead_ZhatOM _ D.R.rS (Nat.le_succ _)]
  have s1 := sign_mul_star (D := D) (r := D.R.rS) (q := D.R.rS + 1)
  have s2 := sign_mul_star (D := D) (r := D.R.rS) (q := D.R.rS)
  unfold GPt Gval Gflag Dl
  rw [h1, h2, star_mul', star_mul']
  push_cast
  linear_combination (leadMinorE (ZhatL F F') (D.R.rS + 1) * star (leadMinorE (ZhatL F F') (D.R.rS + 1))) * s1 -
    ((T : D.host.E) * T' * (leadMinorE (ZhatL F F') D.R.rS * star (leadMinorE (ZhatL F F') D.R.rS))) * s2

end Minors

section Bounds

variable {D : D7}

theorem one_le_NGPt (TT : ℕ) (γ : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS) (o : 𝓞 D.host.E)
    (ho : o ∈ dI D ^ (2 * D.R.rS * (D.R.rS + 1))) (hG : (o : D.host.E) = GPt TT γ) (h0 : GPt TT γ ≠ 0) :
    1 ≤ NGPt D.host.rdE TT γ := by
  unfold NGPt
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Formalism.MainNotions.LatticeGluingRadicals.d_card D]
  have hsq := prod_sq_ge _ o ho (by rw [hG]; exact h0)
  rw [hG, Finset.prod_pow] at hsq
  have hP0 : 0 ≤ ∏ w : InfinitePlace D.host.E, w (GPt TT γ) := Finset.prod_nonneg fun w _ => w.1.nonneg _
  have hrd := rd_pos (D := D)
  have hX : (D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1)) ≤ ∏ w : InfinitePlace D.host.E, w (GPt TT γ) := by
    refine (pow_le_pow_iff_left₀ (by positivity) hP0 two_ne_zero).1 ?_
    rw [← pow_mul, mul_comm _ 2]
    exact hsq
  have e : (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f = (D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1)) := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [inv_pow, ← div_eq_inv_mul, one_le_div (by positivity), e]
  exact hX

theorem one_le_NDPt (γ : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS)
    (hmin : ∀ a, ∃ o ∈ dI D ^ (endIdx γ a * (2 * D.R.rS + 1 - endIdx γ a)),
      (o : D.host.E) = endMin γ a ∧ endMin γ a ≠ 0) :
    1 ≤ NDPt D.host.rdE γ := by
  unfold NDPt
  rw [← Finset.prod_const_one (s := (Finset.univ : Finset (Fin γ.1.length)))]
  refine Finset.prod_le_prod (fun _ _ => zero_le_one) fun a _ => ?_
  obtain ⟨o, ho, e, h0⟩ := hmin a
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Formalism.MainNotions.LatticeGluingRadicals.d_card D]
  have hsq := prod_sq_ge _ o ho (by rw [e]; exact h0)
  rw [e] at hsq
  have hrd := rd_pos (D := D)
  have e2 : (D.host.rdE ^ (2 * (endIdx γ a * (2 * D.R.rS + 1 - endIdx γ a)))) ^ D.R.f =
      (D.host.rdE ^ D.R.f) ^ (2 * (endIdx γ a * (2 * D.R.rS + 1 - endIdx γ a))) := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [inv_pow, ← div_eq_inv_mul, one_le_div (by positivity), e2]
  exact hsq

end Bounds

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGCut in

theorem stepNormOne_of
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepNormOne := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ νL νB ng γ hγ => ?_⟩
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := hγ
  have hG : t.toTerm.G ≠ 0 := by
    intro h
    apply ht.1
    show Gt t = 0
    have h' : t.G = 0 := h
    simp [Gt, h']
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := hOV D X Y u u' t hr
    show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := hAt D X Y u u' t.toTerm hG hrel
  have hat := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  obtain ⟨F', ⟨hP, -⟩, hGv, hcell⟩ := hat
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hun := hrow.2.1.2.1
  have hz := hrow.2.1.2.2.1.1
  have hX := hrow.2.2
  have hz' := hP.1.1
  have hX' := hP.2.2.2
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam := PtPf.frame_mem _ hz hX
  have hF' : ∀ b, frame F' b ∈ t.toTerm.lam := PtPf.frame_mem _ hz' hX'
  rw [← hpt]
  show 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) ∧
    1 ≤ NDPt D.host.rdE (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm))
  have hlead : ∀ q, q ≤ D.R.rS + 1 → ∃ o ∈ dI D ^ (q * (2 * D.R.rS + 1 - q)),
      (o : D.host.E) = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) q := fun q hq => by
    obtain ⟨o, ho, e⟩ := lead_mem hun (lf D (X.Fu u)) F' hz hX hz' hX' q hq
    exact ⟨o, ho, e.trans (lead_cell _ _ hcell q).symm⟩
  constructor
  · have hGeq := gpt_eq (T := Tu D u) (T' := Tu D u') (lf D (X.Fu u)) F' _ hcell
    obtain ⟨o1, ho1, e1⟩ := hlead (D.R.rS + 1) le_rfl
    obtain ⟨o0, ho0, e0⟩ := hlead D.R.rS (Nat.le_succ _)
    obtain ⟨o1', ho1', e1'⟩ := star_mem_pow _ o1 ho1
    obtain ⟨o0', ho0', e0'⟩ := star_mem_pow _ o0 ho0
    have ex1 : (D.R.rS + 1) * (2 * D.R.rS + 1 - (D.R.rS + 1)) + (D.R.rS + 1) * (2 * D.R.rS + 1 - (D.R.rS + 1)) =
        2 * D.R.rS * (D.R.rS + 1) := by
      rw [show 2 * D.R.rS + 1 - (D.R.rS + 1) = D.R.rS by omega]; ring
    have ex0 : D.R.rS * (2 * D.R.rS + 1 - D.R.rS) + D.R.rS * (2 * D.R.rS + 1 - D.R.rS) =
        2 * D.R.rS * (D.R.rS + 1) := by
      rw [show 2 * D.R.rS + 1 - D.R.rS = D.R.rS + 1 by omega]; ring
    have hm1 : o1 * o1' ∈ dI D ^ (2 * D.R.rS * (D.R.rS + 1)) := by
      rw [← ex1, pow_add]; exact Ideal.mul_mem_mul ho1 ho1'
    have hm0 : o0 * o0' ∈ dI D ^ (2 * D.R.rS * (D.R.rS + 1)) := by
      rw [← ex0, pow_add]; exact Ideal.mul_mem_mul ho0 ho0'
    refine one_le_NGPt _ _ (o1 * o1' - (((Tu D u : ℕ) * (Tu D u' : ℕ) : ℕ) : 𝓞 D.host.E) * (o0 * o0'))
      (Ideal.sub_mem _ hm1 (Ideal.mul_mem_left _ _ hm0)) ?_ (by rw [hGeq]; exact hGv)
    have e1a : algebraMap (𝓞 D.host.E) D.host.E o1 = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) (D.R.rS + 1) := e1
    have e0a : algebraMap (𝓞 D.host.E) D.host.E o0 = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) D.R.rS := e0
    have e1b : algebraMap (𝓞 D.host.E) D.host.E o1' = star (algebraMap (𝓞 D.host.E) D.host.E o1) := e1'
    have e0b : algebraMap (𝓞 D.host.E) D.host.E o0' = star (algebraMap (𝓞 D.host.E) D.host.E o0) := e0'
    show algebraMap (𝓞 D.host.E) D.host.E _ = _
    unfold GPt
    rw [dlast_eq, dr_eq, map_sub, map_mul, map_mul, map_mul, map_natCast, e1b, e0b, e1a, e0a]
  · refine one_le_NDPt _ fun a => ?_
    have hj : endIdx (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) a ≤ D.R.rS + 1 :=
      (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)).1.sizeUpTo_le _
    obtain ⟨o, ho, e⟩ := hlead _ hj
    have hE := PtPf.blockEndMinors_of_cell _ (PtPf.zhatOM_isIntegral _ _ hun hF hF') _ hcell
    exact ⟨o, ho, by rw [e, endMin_eq], (hE a).2⟩

open Formalism.L2.SG.TermOp.Vanish in

theorem stepNormOne_of_leaves (hA : AvgCore) (hU : GinfUnimod) (hN : NLamNinf) (hC : ChiTrivialC) (hG : PsiInfChar)
    (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC) (h4 : NonRelCharC)
    (hAt : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    Formalism.L2.SG.NGCut.StepNormOne :=
  stepNormOne_of (fun _ _ Y _ _ t ht => ooVanish_of hA hU hN hC hG h1 h2 h3 h4 Y t ht) hAt

end Formalism.L2.SG.NGCut.LeadingMinorIntegrality
