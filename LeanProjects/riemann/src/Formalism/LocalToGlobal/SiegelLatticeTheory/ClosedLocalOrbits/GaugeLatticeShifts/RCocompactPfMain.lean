import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfConj

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Full

section Asm

variable {D : D7} (X : HidaSetting D)

theorem rcm_gr_mul (A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : Gr X A * Gr X B = Gr X (A * B) := by
  simp only [Gr, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Bm X) (Bm' X), Bm_mul_Bm', Matrix.one_mul]

theorem rcm_gr_one : Gr X 1 = 1 := by
  rw [Gr, Matrix.mul_one, Bm'_mul_Bm]

theorem rcm_gr_inv_mul (M : GL (Fin X.B.I.n) X.B.I.E) :
    Gr X (↑M⁻¹ : Matrix _ _ _) * Gr X (M : Matrix _ _ _) = 1 := by
  rw [rcm_gr_mul, Units.inv_mul, rcm_gr_one]

theorem rcm_gr_mul_inv (M : GL (Fin X.B.I.n) X.B.I.E) :
    Gr X (M : Matrix _ _ _) * Gr X (↑M⁻¹ : Matrix _ _ _) = 1 := by
  rw [rcm_gr_mul, Units.mul_inv, rcm_gr_one]

theorem rcm_ninf_iff (u : D.what₂.Word) (s : X.B.I.Ginf) :
    s ∈ X.NinfU u ↔ ∀ v, InPat (lvk X) 1 (Mv X v s - 1) :=
  ⟨fun hs v => pat_of_mem X u v hs, fun h v => inN_of_pat X u v (uMat (s v)) (h v)⟩

private theorem rcm_P_mul_inv_lemma (v : InfinitePlace X.B.I.F) : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := by
  have hB : (Bm X).map (X.B.I.φ v) * (Bm' X).map (X.B.I.φ v) = 1 := by
    rw [← Matrix.map_mul, Bm_mul_Bm']
    simp
  have h1 := Bv_mul_Bv' X v
  unfold Bv Bv' at h1
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((Bm X).map (X.B.I.φ v)), hB, Matrix.one_mul] at h1
  exact mul_eq_one_comm.mp h1

theorem rcm_mv_rat {x : X.B.I.Ginf} {M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E}
    (hx : ∀ v, uMat (x v) = (X.B.I.P v)⁻¹ * M.map (X.B.I.φ v) * X.B.I.P v) (v : InfinitePlace X.B.I.F) :
    Mv X v x = (Gr X M).map (X.B.I.φ v) := by
  have hP := rcm_P_mul_inv_lemma X v
  unfold Mv Gr Bv Bv'
  rw [hx v]
  simp only [Matrix.map_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (X.B.I.P v) ((X.B.I.P v)⁻¹), hP, Matrix.one_mul,
    ← Matrix.mul_assoc (X.B.I.P v) ((X.B.I.P v)⁻¹), hP, Matrix.one_mul]

def rcm_mkPt (C : ∀ v : InfinitePlace X.B.I.F, Matrix (Kap X) (Kap X) ℂ)
    (hC : ∀ v, (C v)ᴴ * JBv X v * C v = JBv X v) : X.B.I.Ginf := fun v =>
  ⟨⟨Bv X v * C v * Bv' X v, Bv X v * Formalism.L2.SG.Pf.Unip.sharp (JBv X v) (JBv' X v) (C v) * Bv' X v, by
      calc Bv X v * C v * Bv' X v * (Bv X v * Formalism.L2.SG.Pf.Unip.sharp (JBv X v) (JBv' X v) (C v) * Bv' X v)
          = Bv X v * (C v * (Bv' X v * Bv X v) * Formalism.L2.SG.Pf.Unip.sharp (JBv X v) (JBv' X v) (C v)) * Bv' X v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [Bv'_mul_Bv, Matrix.mul_one, self_mul_sharp (JBv'_mul X v) (hC v), Matrix.mul_one,
            Bv_mul_Bv'],
    by
      calc Bv X v * Formalism.L2.SG.Pf.Unip.sharp (JBv X v) (JBv' X v) (C v) * Bv' X v * (Bv X v * C v * Bv' X v)
          = Bv X v * (Formalism.L2.SG.Pf.Unip.sharp (JBv X v) (JBv' X v) (C v) * (Bv' X v * Bv X v) * C v) * Bv' X v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [Bv'_mul_Bv, Matrix.mul_one, sharp_mul_self (JBv'_mul X v) (hC v), Matrix.mul_one,
            Bv_mul_Bv']⟩, by
    show (Bv X v * C v * Bv' X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Bv X v * C v * Bv' X v) = Formalism.REAL.Jm (X.B.I.ε v)
    have hg := Bv_gram X v
    calc (Bv X v * C v * Bv' X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Bv X v * C v * Bv' X v)
        = (Bv' X v)ᴴ * ((C v)ᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) * C v) * Bv' X v := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (Bv' X v)ᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) * Bv' X v := by rw [hg, hC v]
      _ = (Bv X v * Bv' X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Bv X v * Bv' X v) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (X.B.I.ε v) := by rw [Bv_mul_Bv']; simp⟩

theorem rcm_mv_mkPt (C : ∀ v : InfinitePlace X.B.I.F, Matrix (Kap X) (Kap X) ℂ)
    (hC : ∀ v, (C v)ᴴ * JBv X v * C v = JBv X v) (v : InfinitePlace X.B.I.F) : Mv X v (rcm_mkPt X C hC) = C v := by
  unfold Mv
  show Bv' X v * (Bv X v * C v * Bv' X v) * Bv X v = C v
  simp only [Matrix.mul_assoc]
  rw [Bv'_mul_Bv, Matrix.mul_one, ← Matrix.mul_assoc, Bv'_mul_Bv, Matrix.one_mul]

end Asm

section Asm2

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

private theorem rcm_mv_mul_lemma (a b : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    Mv X v (a * b) = Mv X v a * Mv X v b := by
  unfold Mv
  show Bv' X v * (uMat (a v) * uMat (b v)) * Bv X v =
    Bv' X v * uMat (a v) * Bv X v * (Bv' X v * uMat (b v) * Bv X v)
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Bv X v) (Bv' X v), Bv_mul_Bv', Matrix.one_mul]

theorem rcm_mv_inv_rat {x : X.B.I.Ginf} {M : GL (Fin X.B.I.n) X.B.I.E}
    (hx : ∀ v, uMat (x v) = (X.B.I.P v)⁻¹ * (M : Matrix _ _ _).map (X.B.I.φ v) * X.B.I.P v) (v : InfinitePlace X.B.I.F) :
    Mv X v x⁻¹ = (Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) := by
  have h1 : Mv X v (1 : X.B.I.Ginf) = 1 := by
    unfold Mv
    show Bv' X v * 1 * Bv X v = 1
    rw [Matrix.mul_one, Bv'_mul_Bv]
  have hA : Mv X v x⁻¹ * Mv X v x = 1 := by
    rw [← rcm_mv_mul_lemma, inv_mul_cancel, h1]
  rw [rcm_mv_rat X hx v] at hA
  have hC : (Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) * (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v) = 1 := by
    rw [← Matrix.map_mul, rcm_gr_inv_mul]
    simp
  have hC' := mul_eq_one_comm.mp hC
  calc Mv X v x⁻¹ = Mv X v x⁻¹ * ((Gr X (M : Matrix _ _ _)).map (X.B.I.φ v) *
        (Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v)) := by rw [hC', Matrix.mul_one]
    _ = (Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) := by rw [← Matrix.mul_assoc, hA, Matrix.one_mul]

theorem rcm_mv_conj {x : X.B.I.Ginf} {M : GL (Fin X.B.I.n) X.B.I.E}
    (hx : ∀ v, uMat (x v) = (X.B.I.P v)⁻¹ * (M : Matrix _ _ _).map (X.B.I.φ v) * X.B.I.P v) (r : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) :
    Mv X v (x⁻¹ * r * x) = (Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) * Mv X v r *
      (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v) := by
  rw [rcm_mv_mul_lemma, rcm_mv_mul_lemma, rcm_mv_inv_rat hx, rcm_mv_rat X hx]

theorem rcm_rset_iff (t : GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') {M : GL (Fin X.B.I.n) X.B.I.E}
    (hx : ∀ v, uMat (t.pt.1 v) = (X.B.I.P v)⁻¹ * (M : Matrix _ _ _).map (X.B.I.φ v) * X.B.I.P v) (r : X.B.I.Ginf) :
    r ∈ Rset t ↔ ∀ v, InPat (lvk X) 1 (Mv X v r - 1) ∧
      InPat (lvk X) 1 ((Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) * Mv X v r *
        (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v) - 1) := by
  show (r ∈ X.NinfU u ∧ t.pt.1⁻¹ * r * t.pt.1 ∈ X.NinfU u') ↔ _
  rw [rcm_ninf_iff, rcm_ninf_iff]
  simp only [rcm_mv_conj hx r]
  exact ⟨fun h v => ⟨h.1 v, h.2 v⟩, fun h => ⟨fun v => (h v).1, fun v => (h v).2⟩⟩

private theorem rcm_inPat_mul_lemma {A B : Matrix (Kap X) (Kap X) ℂ} (hA : InPat (lvk X) 1 (A - 1))
    (hB : InPat (lvk X) 1 (B - 1)) : InPat (lvk X) 1 (A * B - 1) := by
  intro i j hij
  have e : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply, hA i j hij, hB i j hij]
  simp only [add_zero]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases h : lvk X m < lvk X i + 1
  · rw [hA i m h, zero_mul]
  · rw [hB m j (by omega), mul_zero]

theorem rcm_rset_mul (t : GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') {a b : X.B.I.Ginf} (ha : a ∈ Rset t)
    (hb : b ∈ Rset t) : a * b ∈ Rset t := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  show a * b ∈ X.NinfU u ∧ t.pt.1⁻¹ * (a * b) * t.pt.1 ∈ X.NinfU u'
  refine ⟨?_, ?_⟩
  · rw [rcm_ninf_iff] at ha1 hb1 ⊢
    intro v
    rw [rcm_mv_mul_lemma]
    exact rcm_inPat_mul_lemma (ha1 v) (hb1 v)
  · have e : t.pt.1⁻¹ * (a * b) * t.pt.1 = (t.pt.1⁻¹ * a * t.pt.1) * (t.pt.1⁻¹ * b * t.pt.1) := by group
    rw [e]
    rw [rcm_ninf_iff] at ha2 hb2 ⊢
    intro v
    rw [rcm_mv_mul_lemma]
    exact rcm_inPat_mul_lemma (ha2 v) (hb2 v)

private theorem rcm_inPat_inv_lemma {A B : Matrix (Kap X) (Kap X) ℂ} (hA : InPat (lvk X) 1 (A - 1))
    (hBA : B * A = 1) : InPat (lvk X) 1 (B - 1) := by
  have e : B - 1 = -(B * (A - 1)) := by
    rw [mul_sub, hBA, mul_one]
    abel
  have key : ∀ n, ∀ i j, lvk X j = n → lvk X j < lvk X i + 1 → (B - 1) i j = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih i j hj hij
    rw [e, Matrix.neg_apply, Matrix.mul_apply, neg_eq_zero]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : lvk X j < lvk X m + 1
    · rw [hA m j hm, mul_zero]
    · have h1 : (B - 1) i m = 0 := ih (lvk X m) (by omega) i m rfl (by omega)
      have h2 : B i m = (1 : Matrix (Kap X) (Kap X) ℂ) i m := by
        rw [Matrix.sub_apply] at h1
        exact sub_eq_zero.mp h1
      rw [h2]
      by_cases him : i = m
      · subst him
        rw [hA i j hij, mul_zero]
      · rw [Matrix.one_apply_ne him, zero_mul]
  intro i j hij
  exact key _ i j rfl hij

theorem rcm_rset_inv (t : GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') {a : X.B.I.Ginf} (ha : a ∈ Rset t) :
    a⁻¹ ∈ Rset t := by
  have h1 : ∀ v, Mv X v (1 : X.B.I.Ginf) = 1 := fun v => by
    unfold Mv
    show Bv' X v * 1 * Bv X v = 1
    rw [Matrix.mul_one, Bv'_mul_Bv]
  have hI : ∀ (y : X.B.I.Ginf) v, Mv X v y⁻¹ * Mv X v y = 1 := fun y v => by
    rw [← rcm_mv_mul_lemma, inv_mul_cancel, h1]
  obtain ⟨ha1, ha2⟩ := ha
  show a⁻¹ ∈ X.NinfU u ∧ t.pt.1⁻¹ * a⁻¹ * t.pt.1 ∈ X.NinfU u'
  refine ⟨?_, ?_⟩
  · rw [rcm_ninf_iff] at ha1 ⊢
    exact fun v => rcm_inPat_inv_lemma (ha1 v) (hI a v)
  · have e : t.pt.1⁻¹ * a⁻¹ * t.pt.1 = (t.pt.1⁻¹ * a * t.pt.1)⁻¹ := by group
    rw [e]
    rw [rcm_ninf_iff] at ha2 ⊢
    exact fun v => rcm_inPat_inv_lemma (ha2 v) (hI _ v)

theorem rcm_cay_mem_rset (t : GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') {M : GL (Fin X.B.I.n) X.B.I.E}
    (hx : ∀ v, uMat (t.pt.1 v) = (X.B.I.P v)⁻¹ * (M : Matrix _ _ _).map (X.B.I.φ v) * X.B.I.P v)
    (Z : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ) (hZ : ∀ v, InPat (lvk X) 1 (Z v))
    (hZc : ∀ v, InPat (lvk X) 1 ((Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) * Z v *
      (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v)))
    (N : ℕ) (s : X.B.I.Ginf) (hs : ∀ v, Mv X v s = Formalism.L2.SG.Pf.Unip.cay N (Z v)) : s ∈ Rset t := by
  rw [rcm_rset_iff t hx]
  intro v
  have hGG : (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v) * (Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) = 1 := by
    rw [← Matrix.map_mul, rcm_gr_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hs v, conj_cay hGG]
  exact ⟨cay_sub_one N (hZ v), cay_sub_one N (hZc v)⟩

end Asm2

section Main

def rcm_Sset {D : D7} (X : HidaSetting D) (C : ℝ) : Set X.B.I.Ginf :=
  Set.univ.pi fun v => (fun g : Formalism.REAL.UJ (X.B.I.ε v) => uMat g) ⁻¹'
    ((fun Z : Matrix (Kap X) (Kap X) ℂ => Bv X v * Formalism.L2.SG.Pf.Unip.cay (2 * D.R.rS + 2) Z * Bv' X v) ''
      (Set.univ.pi fun _ : Kap X => Set.univ.pi fun _ : Kap X => Metric.closedBall (0 : ℂ) C :
        Set (Matrix (Kap X) (Kap X) ℂ)))

theorem rcm_sset_compact {D : D7} (X : HidaSetting D) (C : ℝ) : IsCompact (rcm_Sset X C) :=
  isCompact_univ_pi fun v => ((Formalism.REAL.uJEmb X.B.I.n (X.B.I.ε v)).1).isCompact_preimage
    ((isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) C).image
      ((continuous_const.matrix_mul (cay_continuous (2 * D.R.rS + 2))).matrix_mul continuous_const))

theorem rCocompactC_of (h1 : RatApprox) (h2 : RatMem) : RCocompactC := by
  intro D X Y u u' t
  obtain ⟨M, hMU, hMx, -, hMc⟩ := t.rep.2.1
  have hx : ∀ v, uMat (t.pt.1 v) = (X.B.I.P v)⁻¹ * (M : Matrix _ _ _).map (X.B.I.φ v) * X.B.I.P v := hMx
  obtain ⟨d, hd, hmem⟩ := h2 D X Y u u' t M hMU hMc
  choose C hC using fun k : ℕ => h1 D X M hMU (k + 1) (by omega) d hd
  have hGG : ∀ v, (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v) * (Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) = 1 :=
    fun v => by rw [← Matrix.map_mul, rcm_gr_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hGu : ∀ v, ((Gr X (M : Matrix _ _ _)).map (X.B.I.φ v))ᴴ * JBv X v * (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v) =
      JBv X v := fun v => by rw [← rcm_mv_rat X hx v]; exact Mv_unitary X v _
  let R : ℕ → Set X.B.I.Ginf := fun k => {r | r ∈ Rset t ∧ ∀ v, InPat (lvk X) (k + 1) (Mv X v r - 1)}
  have hm : ∀ x ∈ R (2 * D.R.rS + 1), x = 1 := by
    intro x hxR
    funext v
    have h0 : Mv X v x - 1 = 0 :=
      eq_zero_of_inPat (L := 2 * D.R.rS + 1 + 1) (fun i => by have := lvk_le X i; omega) (hxR.2 v)
    have hu : uMat (x v) = 1 := by rw [uMat_eq X v x, sub_eq_zero.1 h0, Matrix.mul_one, Bv_mul_Bv']
    exact Subtype.ext (Units.ext (by simpa using hu))
  have hstep : ∀ k < 2 * D.R.rS + 1, ∀ x ∈ R k, ∃ γ ∈ ROinf t, ∃ y ∈ R (k + 1), ∃ s ∈ rcm_Sset X (C k),
      x = γ * y * s := by
    intro k _ x hxk
    obtain ⟨hxR, hxl⟩ := hxk
    have hx1 := (rcm_rset_iff t hx x).1 hxR
    let P : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ :=
      fun v => Formalism.L2.SG.Pf.Unip.proj (JBv X v) (JBv' X v) (Mv X v x - 1)
    have hPk : ∀ v, InPat (lvk X) (k + 1) (P v) := fun v => inPat_proj (JBv_graded X v) (JBv'_graded X v) (hxl v)
    have hPs : ∀ v, (P v)ᴴ * JBv X v = -(JBv X v * P v) :=
      fun v => proj_skew (JBv_herm X v) (JBv'_herm X v) (JBv'_mul X v) (JBv_mul X v) _
    have hPc : ∀ v, InPat (lvk X) 1 ((Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) * P v *
        (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v)) := by
      intro v
      show InPat (lvk X) 1 (_ * Formalism.L2.SG.Pf.Unip.proj (JBv X v) (JBv' X v) (Mv X v x - 1) * _)
      rw [conj_proj (JBv_herm X v) (JBv'_herm X v) (JBv'_mul X v) (JBv_mul X v) (hGu v) (hGG v)]
      have e : (Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) * (Mv X v x - 1) * (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v) =
          (Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) * Mv X v x * (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v) - 1 := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mul_comm_one (hGG v)]
      rw [e]
      exact inPat_proj (JBv_graded X v) (JBv'_graded X v) (hx1 v).2
    obtain ⟨Yr, hYk, hYc, hYs, hYd, hYC⟩ := hC k P fun v => ⟨hPk v, hPc v, hPs v⟩
    obtain ⟨g, hg, hgM⟩ := hmem Yr (inPat_mono (by omega) hYk) hYc hYs hYd
    have hYvk : ∀ v, InPat (lvk X) (k + 1) (Yr.map (X.B.I.φ v)) := fun v => inPat_map _ hYk
    have hYvs : ∀ v, (Yr.map (X.B.I.φ v))ᴴ * JBv X v = -(JBv X v * Yr.map (X.B.I.φ v)) := by
      intro v
      rw [map_conjTranspose, show JBv X v = (JB X).map (X.B.I.φ v) from rfl, ← Matrix.map_mul, ← Matrix.map_mul, hYs,
        Matrix.map_neg _ (fun a => map_neg _ a)]
    have hYvc : ∀ v, InPat (lvk X) 1 ((Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) * Yr.map (X.B.I.φ v) *
        (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v)) := by
      intro v
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      exact inPat_map _ hYc
    let Z : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ := fun v => P v - Yr.map (X.B.I.φ v)
    have hZk : ∀ v, InPat (lvk X) (k + 1) (Z v) := fun v => inPat_sub (hPk v) (hYvk v)
    have hZs : ∀ v, (Z v)ᴴ * JBv X v = -(JBv X v * Z v) := by
      intro v
      show (P v - Yr.map (X.B.I.φ v))ᴴ * JBv X v = -(JBv X v * (P v - Yr.map (X.B.I.φ v)))
      rw [conjTranspose_sub, Matrix.sub_mul, hPs, hYvs, Matrix.mul_sub]
      abel
    have hZc : ∀ v, InPat (lvk X) 1 ((Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) * Z v *
        (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v)) := by
      intro v
      show InPat (lvk X) 1 (_ * (P v - Yr.map (X.B.I.φ v)) * _)
      rw [Matrix.mul_sub, Matrix.sub_mul]
      exact inPat_sub (hPc v) (hYvc v)
    have hnil : ∀ v, ((⅟2 : ℂ) • Z v) ^ (2 * D.R.rS + 2) = 0 := fun v =>
      pow_eq_zero_of_inPat (k := k + 1) (by omega) (fun i => by have := lvk_le X i; omega) (inPat_smul _ (hZk v))
    have hZu : ∀ v, (Formalism.L2.SG.Pf.Unip.cay (2 * D.R.rS + 2) (Z v))ᴴ * JBv X v *
        Formalism.L2.SG.Pf.Unip.cay (2 * D.R.rS + 2) (Z v) = JBv X v := fun v => cay_unitary (hZs v) (hnil v)
    let c := rcm_mkPt X (fun v => Formalism.L2.SG.Pf.Unip.cay (2 * D.R.rS + 2) (Z v)) hZu
    have hcM : ∀ v, Mv X v c = Formalism.L2.SG.Pf.Unip.cay (2 * D.R.rS + 2) (Z v) := rcm_mv_mkPt X _ hZu
    have hgM' : ∀ v, Mv X v g = Formalism.L2.SG.Pf.Unip.cay (2 * D.R.rS + 2) (Yr.map (X.B.I.φ v)) :=
      fun v => by rw [hgM v, cay_map]
    have hgR : g ∈ Rset t :=
      rcm_cay_mem_rset t hx (fun v => Yr.map (X.B.I.φ v)) (fun v => inPat_mono (by omega) (hYvk v)) hYvc _ g hgM'
    have hcR : c ∈ Rset t := rcm_cay_mem_rset t hx Z (fun v => inPat_mono (by omega) (hZk v)) hZc _ c hcM
    refine ⟨g, hg, g⁻¹ * x * c⁻¹, ⟨rcm_rset_mul t (rcm_rset_mul t (rcm_rset_inv t hgR) hxR) (rcm_rset_inv t hcR), fun v => ?_⟩, c,
      ?_, by group⟩
    · rw [Mv_mul, Mv_mul, Mv_inv, Mv_inv, hgM' v, hcM v]
      have := step_mat (JBv_graded X v) (JBv'_graded X v) (JBv_herm X v) (JBv'_herm X v) (JBv'_mul X v)
        (JBv_mul X v) (2 * D.R.rS + 1) (Mv_unitary X v x) (hxl v) (hYvk v) (hYvs v)
      exact inPat_mono (by omega) this
    · intro v _
      refine ⟨Z v, ?_, rfl⟩
      refine Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      have := hYC v i j
      show ‖(P v - Yr.map (X.B.I.φ v)) i j‖ ≤ C k
      rw [Matrix.sub_apply] at this ⊢
      rwa [norm_sub_rev]
  obtain ⟨K, hK, hcov⟩ := cover_of_steps (ROinf t)
    (fun a ha b hb => (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin).mul_mem ha hb)
    (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin).one_mem R (2 * D.R.rS + 1) hm (fun k => rcm_Sset X (C k))
    (fun k => rcm_sset_compact X (C k)) hstep
  refine ⟨K, hK, fun r hr => ?_⟩
  obtain ⟨γ, hγ, c, hc, e⟩ := hcov r ⟨hr, fun v => ((rcm_rset_iff t hx r).1 hr v).1⟩
  refine ⟨γ⁻¹, (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin).inv_mem hγ, ?_⟩
  rw [e, ← mul_assoc, inv_mul_cancel, one_mul]
  exact hc

end Main

end Formalism.L2.SG.TermOp.Vanish
