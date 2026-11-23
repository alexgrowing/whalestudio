import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGSlice

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
open scoped ComplexConjugate

theorem fsv_mul_fsv (a b t : ℂ) : P5.fsv a t * P5.fsv b t = P5.fsv (a + b) t := by
  unfold P5.fsv
  rw [← Complex.exp_add]
  congr 1
  simp only [map_add]
  ring

section wave

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem uInv_cons_apply (s : ℂ) (l : C.Letter) (w : List C.Letter)
    (x : Wd.Ix (Fin (w.length + 1)) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (e : Wd.Ix (Fin (w.length + 1))) :
    KB.uInv s (l :: w) x e =
      if e 0 = 0 then KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)
      else KB.uInv s w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
        (if l.1 then s else conj s) • KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ) :=
  rfl

theorem uInv_cons0 (s : ℂ) (l : C.Letter) (w : List C.Letter)
    (x : Wd.Ix (Fin (w.length + 1)) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    (fun e' => KB.uInv s (l :: w) x (Fin.cons (0 : Fin 2) e')) = KB.uInv s w (fun e' => x (Fin.cons 0 e')) := by
  funext e'
  rw [uInv_cons_apply, if_pos (by simp)]
  simp

theorem uInv_cons1 (s : ℂ) (l : C.Letter) (w : List C.Letter)
    (x : Wd.Ix (Fin (w.length + 1)) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    (fun e' => KB.uInv s (l :: w) x (Fin.cons (1 : Fin 2) e')) =
      KB.uInv s w (fun e' => x (Fin.cons 1 e')) + (if l.1 then s else conj s) • KB.uInv s w (fun e' => x (Fin.cons 0 e')) := by
  funext e'
  rw [uInv_cons_apply, if_neg (by simp)]
  simp only [Fin.cons_succ, Pi.add_apply, Pi.smul_apply]

theorem uInv_comp (s σ : ℂ) : ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
    KB.uInv s w (KB.uInv σ w x) = KB.uInv (s + σ) w x
  | [], x => rfl
  | l :: w, x => by
    funext e
    rw [uInv_cons_apply, uInv_cons0, uInv_cons1, uInv_cons_apply (s + σ), Formalism.FourierDecayAlt.P.PBG.uInv_add_smul,
      uInv_comp s σ w, uInv_comp s σ w]
    split_ifs with h0 hl
    · rfl
    · simp only [Pi.add_apply, Pi.smul_apply]
      rw [add_assoc, ← add_smul, add_comm σ s]
    · simp only [Pi.add_apply, Pi.smul_apply, map_add]
      rw [add_assoc, ← add_smul, add_comm (conj σ) (conj s)]

theorem uInv_smulFun (s : ℂ) (φ : B.Mat k ρ → ℂ) : ∀ (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
    KB.uInv s w (fun e g => φ g • x e g) = fun e g => φ g • KB.uInv s w x e g
  | [], x => rfl
  | l :: w, x => by
    funext e g
    rw [uInv_cons_apply, uInv_cons_apply]
    have h0 : (fun e' => (fun e g => φ g • x e g) (Fin.cons (0 : Fin 2) e')) =
        fun e' g => φ g • (fun e' => x (Fin.cons (0 : Fin 2) e')) e' g := rfl
    have h1 : (fun e' => (fun e g => φ g • x e g) (Fin.cons (1 : Fin 2) e')) =
        fun e' g => φ g • (fun e' => x (Fin.cons (1 : Fin 2) e')) e' g := rfl
    rw [h0, h1, uInv_smulFun s φ w, uInv_smulFun s φ w]
    split_ifs
    · rfl
    · simp only [Pi.add_apply, Pi.smul_apply, smul_add]
      rw [smul_comm]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_add]
      rw [smul_comm]

theorem waveG_comp (Bs : B.RealPlaceData k ρ Wp Wq) (s σ : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    KB.waveG Bs s w (KB.waveG Bs σ w x) = KB.waveG Bs (s + σ) w x := by
  have e : KB.waveG Bs σ w x = fun e g => P5.fsv σ (Dmin k ρ Bs.z Bs.z' g ⟨1, by omega⟩) • KB.uInv σ w x e g := rfl
  funext e' g
  rw [e]
  show P5.fsv s (Dmin k ρ Bs.z Bs.z' g ⟨1, by omega⟩) •
      KB.uInv s w (fun e g => P5.fsv σ (Dmin k ρ Bs.z Bs.z' g ⟨1, by omega⟩) • KB.uInv σ w x e g) e' g =
    P5.fsv (s + σ) (Dmin k ρ Bs.z Bs.z' g ⟨1, by omega⟩) • KB.uInv (s + σ) w x e' g
  rw [uInv_smulFun, uInv_comp, smul_smul, fsv_mul_fsv]

theorem onOld_eq_self {w : List C.Letter}
    (M : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) → Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp))
    (hM : ∀ x, M x = x) :
    ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)), KB.onOld M ys x = x
  | [], x => hM x
  | _ :: ys, x => by
    funext e
    show KB.onOld M ys (fun e' => x (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) (fun a => e a.succ) = x e
    rw [onOld_eq_self M hM ys]
    exact congrArg x (Fin.cons_self_tail e)

theorem mDiff_eq (Bs : B.RealPlaceData k ρ Wp Wq) (σ : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    mDiff Bs σ w x = KB.waveG Bs (3 * σ) w x - (3 : ℂ) • KB.waveG Bs (2 * σ) w x +
      (3 : ℂ) • KB.waveG Bs σ w x - x := by
  have hV : ∀ y, waveL Bs σ w y = KB.waveG Bs σ w y := fun _ => rfl
  have e2 : KB.waveG Bs σ w (KB.waveG Bs σ w x) = KB.waveG Bs (2 * σ) w x := by
    rw [waveG_comp]; congr 1; ring
  have e3 : KB.waveG Bs σ w (KB.waveG Bs (2 * σ) w x) = KB.waveG Bs (3 * σ) w x := by
    rw [waveG_comp]; congr 1; ring
  simp only [mDiff, pow_succ, pow_zero, one_mul, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    map_sub, hV]
  rw [e2, e3]
  module

end wave

section forms

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem mDiff_apply_eq (Bs : B.RealPlaceData k ρ Wp Wq) (σ : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (e : Wd.Ix (Fin w.length)) :
    mDiff Bs σ w x e = KB.waveG Bs (3 * σ) w x e + (-3 : ℂ) • KB.waveG Bs (2 * σ) w x e +
      (3 : ℂ) • KB.waveG Bs σ w x e + (-1 : ℂ) • x e := by
  rw [mDiff_eq]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
  module

theorem mDiff_nice (Bs : B.RealPlaceData k ρ Wp Wq) (σ : ℂ) (w : List C.Letter) (ε : ℝ)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (hx : ∀ e, JC.NiceCoef Bs ε (x e)) :
    ∀ e, JC.NiceCoef Bs ε (mDiff Bs σ w x e) := by
  intro e
  rw [mDiff_apply_eq]
  have hw : ∀ t, JC.NiceCoef Bs ε (KB.waveG Bs t w x e) := fun t => Formalism.FourierDecayAlt.P.PBFV.waveG_nice Bs ε t w x hx e
  exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_add (Formalism.FourierDecayAlt.P.JCx2.mn_nice_add (Formalism.FourierDecayAlt.P.JCx2.mn_nice_add (hw _)
    (Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hw _))) (Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hw _)))
    (Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hx e))

end forms

section place

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem mDiff_cpt (hP : P5.ThmPActualCpt) (P : M.Par) (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r)
    (w : List C.Letter) (hw : KB.CutWord P p.l0 w) (σ : ℂ)
    (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hx : ∀ e, KB.CptCoef (p.T.bs j) (x e)) :
    ∀ e, KB.CptCoef (p.T.bs j) (mDiff (p.T.bs j) σ w x e) := by
  have hc : ∀ t e, KB.CptCoef (p.T.bs j) (KB.waveG (p.T.bs j) t w x e) := fun t =>
    (Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support hP Wp Wq P p j hj w hw t x x hx hx).1
  intro e
  rw [mDiff_apply_eq]
  exact Formalism.FourierDecayAlt.P.PBG.cpt_add_smul _ _ (Formalism.FourierDecayAlt.P.PBG.cpt_add_smul _ _
    (Formalism.FourierDecayAlt.P.PBG.cpt_add_smul _ _ (hc _ e) (hc _ e)) (hc _ e)) (hx e)

theorem form_wave_mDiff (P : M.Par) (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : ∀ e, KB.CptCoef (p.T.bs j) (x e)) (hy : ∀ e, KB.CptCoef (p.T.bs j) (y e)) (s σ : ℂ) :
    p.form j hj w (KB.waveG (p.T.bs j) s w (mDiff (p.T.bs j) σ w x)) y =
      p.form j hj w (KB.waveG (p.T.bs j) (s + 3 * σ) w x) y - 3 * p.form j hj w (KB.waveG (p.T.bs j) (s + 2 * σ) w x) y +
        3 * p.form j hj w (KB.waveG (p.T.bs j) (s + σ) w x) y - p.form j hj w (KB.waveG (p.T.bs j) s w x) y := by
  obtain ⟨ε, hε, hxn⟩ := nice_common (p.T.bs j) hx
  obtain ⟨ε', hε', hyn⟩ := nice_common (p.T.bs j) hy
  have hd : ∀ t, Formalism.FourierDecayAlt.P.PBG.DecV (KB.waveG (p.T.bs j) t w x) := fun t =>
    Formalism.FourierDecayAlt.P.PBG.decV_of_nice (Formalism.FourierDecayAlt.P.PBFV.waveG_nice (p.T.bs j) ε t w x hxn)
  have hdy : Formalism.FourierDecayAlt.P.PBG.DecV y := Formalism.FourierDecayAlt.P.PBG.decV_of_nice hyn
  have hV : ∀ z, waveL (p.T.bs j) s w z = KB.waveG (p.T.bs j) s w z := fun _ => rfl
  have hW : KB.waveG (p.T.bs j) s w (mDiff (p.T.bs j) σ w x) =
      KB.waveG (p.T.bs j) (s + 3 * σ) w x + (-3 : ℂ) • KB.waveG (p.T.bs j) (s + 2 * σ) w x +
        (3 : ℂ) • KB.waveG (p.T.bs j) (s + σ) w x + (-1 : ℂ) • KB.waveG (p.T.bs j) s w x := by
    rw [mDiff_eq]
    calc KB.waveG (p.T.bs j) s w (KB.waveG (p.T.bs j) (3 * σ) w x - (3 : ℂ) • KB.waveG (p.T.bs j) (2 * σ) w x +
          (3 : ℂ) • KB.waveG (p.T.bs j) σ w x - x)
        = waveL (p.T.bs j) s w (KB.waveG (p.T.bs j) (3 * σ) w x - (3 : ℂ) • KB.waveG (p.T.bs j) (2 * σ) w x +
          (3 : ℂ) • KB.waveG (p.T.bs j) σ w x - x) := rfl
      _ = waveL (p.T.bs j) s w (KB.waveG (p.T.bs j) (3 * σ) w x) -
            (3 : ℂ) • waveL (p.T.bs j) s w (KB.waveG (p.T.bs j) (2 * σ) w x) +
            (3 : ℂ) • waveL (p.T.bs j) s w (KB.waveG (p.T.bs j) σ w x) - waveL (p.T.bs j) s w x := by
          simp only [map_sub, map_add, map_smul]
      _ = _ := by
          simp only [hV, waveG_comp]
          module
  rw [hW]
  unfold KB.Pl.form
  set A3 := KB.waveG (p.T.bs j) (s + 3 * σ) w x
  set A2 := KB.waveG (p.T.bs j) (s + 2 * σ) w x
  set A1 := KB.waveG (p.T.bs j) (s + σ) w x
  set A0 := KB.waveG (p.T.bs j) s w x
  have d32 := Formalism.FourierDecayAlt.P.PBG.decV_add (hd (s + 3 * σ)) (Formalism.FourierDecayAlt.P.PBG.decV_smul (-3 : ℂ) (hd (s + 2 * σ)))
  have d321 := Formalism.FourierDecayAlt.P.PBG.decV_add d32 (Formalism.FourierDecayAlt.P.PBG.decV_smul (3 : ℂ) (hd (s + σ)))
  rw [Formalism.FourierDecayAlt.P.PBG.form_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w (A3 + (-3 : ℂ) • A2 + (3 : ℂ) • A1) A0 y
      (-1) d321 (hd s) hdy,
    Formalism.FourierDecayAlt.P.PBG.form_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w (A3 + (-3 : ℂ) • A2) A1 y 3 d32
      (hd (s + σ)) hdy,
    Formalism.FourierDecayAlt.P.PBG.form_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w A3 A2 y (-3) (hd (s + 3 * σ))
      (hd (s + 2 * σ)) hdy]
  ring

end place

end Formalism.FourierDecayAlt.P.PBO
