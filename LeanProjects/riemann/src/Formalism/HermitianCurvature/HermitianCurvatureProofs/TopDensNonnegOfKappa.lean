import Formalism.HermitianCurvature.TopDensNonnegOfKappa
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo

open Matrix MeasureTheory
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

namespace WordTransvectionCongruences

section Frames

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem ofWord_x_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hx : st'.x = st.x) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st' w).x = (Fr.ofWord L st w).x := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hx]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hx]

theorem ofWord_q_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hq : st'.q = st.q) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st' w).q = (Fr.ofWord L st w).q := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hq]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hq]

theorem ofWord_xi_congr (L : R.LevelData A r) (st st' : Fr.Start A) (w : List (Letter ℂ S)) (Y : ℂ)
    (hY : st'.xi Y = st.xi Y) : (Fr.ofWord L st' w).xi Y = (Fr.ofWord L st w).xi Y := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hY]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hY]

theorem ofWord_N (L : R.LevelData A r) (st : Fr.Start A) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st w).N = w.length := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih]

theorem ofWord_c_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hx : st'.x = st.x) (hq : st'.q = st.q)
    (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, st'.xi (l.pt + 1) = st.xi (l.pt + 1) ∧ st'.xi (l.pt - 1) = st.xi (l.pt - 1)) :
    (Fr.ofWord L st' w).c = (Fr.ofWord L st w).c := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hx, hq]
  | cons l w ih =>
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have hl := hw l List.mem_cons_self
    have hxw := ofWord_x_congr L st st' hx w
    have hqw := ofWord_q_congr L st st' hq w
    have hxi1 := ofWord_xi_congr L st st' w (l.pt + 1) hl.1
    have hxi2 := ofWord_xi_congr L st st' w (l.pt - 1) hl.2
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih', hxw, hqw, hxi1, hxi2]

end Frames

section Act

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_diagonal (D : Ix S → Pr (RadSp k r z z' π π')) (x : Ix S → RadSp k r z z' π π') (a : Ix S) :
    act (Matrix.diagonal D) x a = (D a).1 (x a) := by
  unfold act
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.diagonal_apply_eq]
  · intro b _ hb
    simp only [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    first
      | rfl
      | simp [Pr]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem pow_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (n : ℕ) (Φ : RadSp k r z z' π π') (p : (Fin r → ℂ) × Mx k r)
    (hp : p ∈ DomR k r z z') :
    ((((L.ζ * L.ζb * L.GGi) ^ n).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) p.1 p.2 =
      (fnVal k r z z' 0 p.2 * fnVal k r z z' 2 p.2 * fnVal k r z z' 5 p.2) ^ n •
        (Φ : Fn k r (Wq →L[ℂ] Wp)) p.1 p.2 := by
  obtain ⟨-, -, -, -, -, -, hz, -, hzb, -, -, hgi, -⟩ := hAL
  induction n generalizing Φ with
  | zero => simp only [pow_zero, one_smul]; rfl
  | succ n ih =>
    rw [pow_succ, pr_fst_mul, Module.End.mul_apply, ih, pr_fst_mul, pr_fst_mul, Module.End.mul_apply,
      Module.End.mul_apply, hz, hzb, hgi]
    simp only [mkP]
    rw [X.fn_apply 0 _ p hp, X.fn_apply 2 _ p hp, X.fn_apply 5 _ p hp, smul_smul, smul_smul, smul_smul, pow_succ]
    ring_nf

end Act

theorem hsInner_zero_left {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (V : Wq →L[ℂ] Wp) : B.hsInner 0 V = 0 := by
  unfold B.hsInner
  have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
    unfold B.hsVec
    ext i
    simp
  rw [h0, inner_zero_right]

end WordTransvectionCongruences

open WordTransvectionCongruences in
theorem topDensNonnegOfKappa : TopDensNonnegOfKappa := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 K hD hl1 hlk hK
  obtain ⟨κ, hκx, hκxi, hκpos⟩ := hK
  obtain ⟨hPl, -, hAL, -, hq, -, -, -⟩ := hD
  intro w hw x _ c _ g

  let st' : Fr.Start (Pr (RadSp P.k P.r z z' π π')) :=
    { st with xi := fun Y => κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ }
  have hCD := (Formalism.FourierDecayAlt.P.c_diagonal (Pr (RadSp P.k P.r z z' π π')) S P.r L st' (M.Ty P) κ
    (fun ρ Y => M.x0 P l0 ρ Y) hκx (fun Y => rfl) w).2.2
  have hc : (Fr.ofWord L st w).c = Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    rw [← ofWord_c_congr L st st' rfl rfl w, hCD]
    · rw [← hq]
    · intro l hl
      have h := hw.1.2.2.1 l hl
      exact ⟨(hκxi _ h.2.1).symm, (hκxi _ h.2.2.1).symm⟩

  have hpos : ∀ (e : Ix S) (ρ : M.Ty P), 0 < Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    intro e ρ
    have h := Formalism.FourierDecayAlt.P.c_pos_truncated Formalism.FourierDecayAlt.P.interlacing_sign Formalism.FourierDecayAlt.P.q_positive_interlacing
      Formalism.FourierDecayAlt.P.q_positive_shift Formalism.FourierDecayAlt.P.cPos_true S P.k P.u P.u' (M.rho P ρ) l0 P.T P.T' w hl1 hlk
      (Formalism.FourierDecayAlt.P.types_interlace P hPl.1 ρ) hPl.1.T_pos hPl.1.T'_pos hw.2.1 hw.2.2 e
    rw [Complex.lt_def]
    exact ⟨h.1, h.2.symm⟩
  unfold topDens
  refine Finset.sum_nonneg fun e _ => ?_
  have hd : (Fr.ofWord L st w).d L = io ((L.ζ * L.ζb * L.GGi) ^ (Fr.ofWord L st w).N) *
      Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    rw [Fr.FrameData.d, hc, Fr.wt, io, io, map_pow]
  rw [act_mul, hd, act_mul, act_io, act_diagonal]
  set Φ := act (Fr.ofWord L st w).F x e
  by_cases hp : (c, g) ∈ DomR P.k P.r z z'
  · have := pow_apply X L hAL (Fr.ofWord L st w).N ((κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e).1 Φ) (c, g) hp
    simp only at this
    rw [this, hsInner_smul_left]
    refine mul_nonneg ?_ (hκpos _ (hpos e) Φ c g)
    obtain ⟨-, -, hGG⟩ := hp
    have hre : fnVal P.k P.r z z' 0 g * fnVal P.k P.r z z' 2 g * fnVal P.k P.r z z' 5 g =
        ((Complex.normSq (zetaL P.k P.r z z' (Fin.last P.r) g) * (GGl P.k P.r z z' g)⁻¹ : ℝ) : ℂ) := by
      simp only [fnVal, Complex.ofReal_mul, Complex.ofReal_inv, ← Complex.mul_conj]
      rfl
    rw [hre, ← Complex.ofReal_pow]
    exact Complex.zero_le_real.mpr (pow_nonneg (mul_nonneg (Complex.normSq_nonneg _) (inv_nonneg.mpr hGG.le)) _)
  · have h0 := ((((L.ζ * L.ζb * L.GGi) ^ (Fr.ofWord L st w).N).1
      ((κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e).1 Φ)).2).1 (c, g) hp
    simp only at h0
    rw [h0, hsInner_zero_left]

end Formalism.FourierDecayAlt.P5
