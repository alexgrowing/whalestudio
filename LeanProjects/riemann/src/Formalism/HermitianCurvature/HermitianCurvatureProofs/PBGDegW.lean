import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWave
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LagrangeExtraction

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section eqgv

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {S : Type}

theorem eqGV_refl (x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) : EqGV x x := fun _ _ _ => rfl

theorem eqGV_trans {x y z : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (h₁ : EqGV x y) (h₂ : EqGV y z) : EqGV x z :=
  fun a g hg => (h₁ a g hg).trans (h₂ a g hg)

theorem eqGV_add_smul {x x' y y' : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (c : ℂ) (h₁ : EqGV x x') (h₂ : EqGV y y') :
    EqGV (x + c • y) (x' + c • y') := fun a g hg => by
  simp only [Pi.add_apply, Pi.smul_apply]; rw [h₁ a g hg, h₂ a g hg]

end eqgv

section deg

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def SlicePoly {k r : ℕ} (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ r)
    (h : C.LPt) (hh : D.ptSize h = j) : Prop :=
  ∀ (w' : List C.Letter) (b : Bool) (δ : ℝ) (e : Fin 2), ∃ Cf : Fin (j + 1) → Wd.Ix (Fin w'.length) →
      B.Mat k (r - j) → (Wq →L[ℂ] Wp),
    Cf (Fin.last j) = (if e = 0 then KB.slv T F j hj w' h hh else 0) ∧
    (∀ l, ∃ ε, ∀ a, JC.NiceCoef (T.bs j) ε (Cf l a)) ∧
    ∀ t : ℝ, EqGV (fun a => KB.slv T F j hj ((b, t + δ) :: w') h hh (Fin.cons e a)) (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • Cf l)

variable {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r)
  (w : List C.Letter) (h h' : C.LPt) (hh : D.ptSize h = j) (hh' : D.ptSize h' = j) (s : ℂ)
  (Mo : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) →ₗ[ℂ]
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)))

def xP (ys : List ℝ) : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp) :=
  KB.waveG (p.T.bs j) s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (KB.slv p.T F j hj (KB.plusW ys w) h hh))

def xM (ys : List ℝ) : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp) :=
  KB.slv p.T F j hj (KB.minusW ys w) h' hh'

def Wv (ys : List ℝ) : ℂ := KB.pairJ (p.form j hj w) ys (xP p F j hj w h hh s Mo ys) (xM p F j hj w h' hh' ys)

theorem form_eq : p.form j hj w = D.formLev p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w := rfl

theorem xP_cons0 (t : ℝ) (ys : List ℝ) :
    (fun e' => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 0 e')) =
      KB.waveG (p.T.bs j) s (KB.plusW ys w) (KB.onOld (⇑Mo) ys
        (fun a => KB.slv p.T F j hj ((true, t) :: KB.plusW ys w) h hh (Fin.cons 0 a))) := by
  funext e'
  exact waveG_cons0 (p.T.bs j) s t (KB.plusW ys w) _ e'

theorem xP_cons1 (t : ℝ) (ys : List ℝ) :
    (fun e' => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 1 e')) =
      KB.waveG (p.T.bs j) s (KB.plusW ys w) (KB.onOld (⇑Mo) ys
        (fun a => KB.slv p.T F j hj ((true, t) :: KB.plusW ys w) h hh (Fin.cons 1 a))) +
      s • KB.waveG (p.T.bs j) s (KB.plusW ys w) (KB.onOld (⇑Mo) ys
        (fun a => KB.slv p.T F j hj ((true, t) :: KB.plusW ys w) h hh (Fin.cons 0 a))) := by
  funext e'
  exact waveG_cons1 (p.T.bs j) s t (KB.plusW ys w) _ e'

theorem conj_tpow (t : ℝ) (m : ℕ) : conj ((t : ℂ) ^ m) = (t : ℂ) ^ m := by
  rw [map_pow, Complex.conj_ofReal]

theorem wv_step (hSP : SlicePoly p.T F j hj h hh) (hSP' : SlicePoly p.T F j hj h' hh')
    (hMo : ∀ ε x, (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → ∀ e, JC.NiceCoef (p.T.bs j) ε (Mo x e)) (ys : List ℝ) :
    ∃ c : Fin (2 * j + 1) → ℂ, c (Fin.last (2 * j)) = s * Wv p F j hj w h h' hh hh' s Mo ys ∧
      ∀ t : ℝ, Wv p F j hj w h h' hh hh' s Mo (t :: ys) = ∑ q : Fin (2 * j + 1), ((t : ℂ) ^ (q : ℕ)) * c q := by
  obtain ⟨C0, hC0l, hC0n, hC0⟩ := hSP (KB.plusW ys w) true 0 0
  obtain ⟨C1, hC1l, hC1n, hC1⟩ := hSP (KB.plusW ys w) true 0 1
  obtain ⟨D0, hD0l, hD0n, hD0⟩ := hSP' (KB.minusW ys w) false 1 0
  obtain ⟨D1, hD1l, hD1n, hD1⟩ := hSP' (KB.minusW ys w) false 1 1
  set Bs := p.T.bs j with hBs
  set A0 : Fin (j + 1) → Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp) :=
    fun l => KB.waveG Bs s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (C0 l)) with hA0
  set A1 : Fin (j + 1) → Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp) :=
    fun l => KB.waveG Bs s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (C1 l)) + s • KB.waveG Bs s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (C0 l)) with hA1
  have hMoc : ∀ x y, EqGV x y → EqGV (Mo x) (Mo y) := mo_congrGV Bs Mo hMo
  have nA : ∀ (Cf : Fin (j + 1) → Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)),
      (∀ l, ∃ ε, ∀ a, JC.NiceCoef Bs ε (Cf l a)) → ∀ l, DecV (KB.waveG Bs s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (Cf l))) := by
    intro Cf hn l
    obtain ⟨ε, hε⟩ := hn l
    exact decV_of_nice (Formalism.FourierDecayAlt.P.PBFV.waveG_nice Bs ε s (KB.plusW ys w) _
      (onOld_nice Bs ε (⇑Mo) (fun x hx => hMo ε x hx) ys (Cf l) hε))
  have dA0 : ∀ l, DecV (A0 l) := nA C0 hC0n
  have dA1 : ∀ l, DecV (A1 l) := fun l => decV_add (nA C1 hC1n l) (decV_smul s (nA C0 hC0n l))
  have dD0 : ∀ l, DecV (D0 l) := fun l => by obtain ⟨ε, hε⟩ := hD0n l; exact decV_of_nice hε
  have dD1 : ∀ l, DecV (D1 l) := fun l => by obtain ⟨ε, hε⟩ := hD1n l; exact decV_of_nice hε

  have ePlus : ∀ (t : ℝ) (Cf : Fin (j + 1) → Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (e : Fin 2),
      EqGV (fun a => KB.slv p.T F j hj ((true, t + 0) :: KB.plusW ys w) h hh (Fin.cons e a)) (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • Cf l) →
      EqGV (KB.waveG Bs s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (fun a => KB.slv p.T F j hj ((true, t) :: KB.plusW ys w) h hh (Fin.cons e a))))
        (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • KB.waveG Bs s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (Cf l))) := by
    intro t Cf e hE
    rw [add_zero] at hE
    have h1 := waveG_congrGV Bs s (KB.plusW ys w) _ _ (onOld_congrGV (⇑Mo) hMoc ys _ _ hE)
    rw [onOld_sum, waveG_sum] at h1
    exact h1
  have e0 : ∀ t : ℝ, EqGV (fun e' => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 0 e'))
      (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • A0 l) := by
    intro t
    rw [xP_cons0]
    exact ePlus t C0 0 (hC0 t)
  have e1 : ∀ t : ℝ, EqGV (fun e' => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 1 e'))
      (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • A1 l) := by
    intro t
    rw [xP_cons1]
    have := eqGV_add_smul s (ePlus t C1 1 (hC1 t)) (ePlus t C0 0 (hC0 t))
    refine eqGV_trans this (fun a g hg => ?_)
    simp only [hA1, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_add, Finset.smul_sum, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [smul_comm]

  have hX : ∀ t : ℝ, Wv p F j hj w h h' hh hh' s Mo (t :: ys) =
      ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) * ((t : ℂ) ^ (m : ℕ)) *
        (KB.pairJ (p.form j hj w) ys (A1 l) (D0 m) - KB.pairJ (p.form j hj w) ys (A0 l) (D1 m)) := by
    intro t
    show KB.pairJ (p.form j hj w) ys (fun e => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 1 e))
        (fun e => xM p F j hj w h' hh' (t :: ys) (Fin.cons 0 e)) -
      KB.pairJ (p.form j hj w) ys (fun e => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 0 e))
        (fun e => xM p F j hj w h' hh' (t :: ys) (Fin.cons 1 e)) = _
    rw [form_eq]
    have c1 := pairJ_formLev_congrGV p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys
      (fun e => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 1 e)) (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • A1 l)
      (fun e => xM p F j hj w h' hh' (t :: ys) (Fin.cons 0 e)) (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • D0 l)
      (e1 t) (hD0 t)
    have c2 := pairJ_formLev_congrGV p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys
      (fun e => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 0 e)) (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • A0 l)
      (fun e => xM p F j hj w h' hh' (t :: ys) (Fin.cons 1 e)) (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • D1 l)
      (e0 t) (hD1 t)
    rw [c1, c2]
    rw [pairJ_sum_sum P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ A1 D0 dA1 dD0,
      pairJ_sum_sum P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ A0 D1 dA0 dD1, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [conj_tpow]
    ring
  set X : Fin (j + 1) → Fin (j + 1) → ℂ := fun l m =>
    KB.pairJ (p.form j hj w) ys (A1 l) (D0 m) - KB.pairJ (p.form j hj w) ys (A0 l) (D1 m) with hXdef
  refine ⟨fun q => ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), if l.val + m.val = q.val then X l m else 0, ?_, fun t => ?_⟩
  ·
    dsimp only
    rw [Finset.sum_eq_single (Fin.last j)]
    · rw [Finset.sum_eq_single (Fin.last j)]
      · rw [if_pos (by simp; omega)]
        have z0 : ∀ (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), DecV y →
            KB.pairJ (p.form j hj w) ys 0 y = 0 := by
          intro y hy
          have := pairJ_sesq_left P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys 0 0 y 1 decV_zero decV_zero hy
          rw [one_smul, add_zero, one_mul, ← form_eq p j hj w] at this
          linear_combination -this
        have z1 : ∀ (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), DecV x →
            KB.pairJ (p.form j hj w) ys x 0 = 0 := by
          intro x hx
          have := pairJ_sesq_right P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys x 0 0 1 hx decV_zero decV_zero
          rw [one_smul, add_zero, map_one, one_mul, ← form_eq p j hj w] at this
          linear_combination -this
        have hA1l : A1 (Fin.last j) = 0 + s • xP p F j hj w h hh s Mo ys := by
          simp only [hA1, hC1l, hC0l, if_pos, show ((1 : Fin 2) = 0) = False from by decide, if_false,
            onOld_zero, waveG_zero]
          rfl
        have hD0l' : D0 (Fin.last j) = xM p F j hj w h' hh' ys := by rw [hD0l, if_pos rfl]; rfl
        have hD1l' : D1 (Fin.last j) = 0 := by rw [hD1l]; simp
        have dxP : DecV (xP p F j hj w h hh s Mo ys) := by
          have h1 := dA1 (Fin.last j)
          rw [hA1l, zero_add] at h1
          have h2 := nA C0 hC0n (Fin.last j)
          simp only [hC0l, if_pos] at h2
          exact h2
        have dxM : DecV (xM p F j hj w h' hh' ys) := by rw [← hD0l']; exact dD0 _
        simp only [hXdef]
        rw [hA1l, hD0l', hD1l', z1 _ (dA0 _)]
        have := pairJ_sesq_left P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys 0 (xP p F j hj w h hh s Mo ys)
          (xM p F j hj w h' hh' ys) s decV_zero dxP dxM
        rw [← form_eq p j hj w] at this
        rw [this, z0 _ dxM]
        simp only [Wv]
        ring
      · intro m _ hm
        rw [if_neg]
        have := m.isLt
        have hm' : m.val ≠ j := fun e => hm (Fin.ext (by simp [e]))
        simp; omega
      · simp
    · intro l _ hl
      apply Finset.sum_eq_zero
      intro m _
      rw [if_neg]
      have := l.isLt
      have := m.isLt
      have hl' : l.val ≠ j := fun e => hl (Fin.ext (by simp [e]))
      simp; omega
    · simp
  ·
    have key : ∀ l m : Fin (j + 1), ∑ q : Fin (2 * j + 1), ((t : ℂ) ^ (q : ℕ)) * (if l.val + m.val = q.val then X l m else 0) =
        ((t : ℂ) ^ (l : ℕ)) * ((t : ℂ) ^ (m : ℕ)) * X l m := by
      intro l m
      rw [Finset.sum_eq_single ⟨l.val + m.val, by omega⟩]
      · rw [if_pos rfl, pow_add]
      · intro q _ hq
        rw [if_neg, mul_zero]
        intro e
        exact hq (Fin.ext e.symm)
      · simp
    rw [hX t]
    calc ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) * ((t : ℂ) ^ (m : ℕ)) * X l m
        = ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), ∑ q : Fin (2 * j + 1),
            ((t : ℂ) ^ (q : ℕ)) * (if l.val + m.val = q.val then X l m else 0) := by
          simp only [key]
      _ = ∑ q : Fin (2 * j + 1), ∑ l : Fin (j + 1), ∑ m : Fin (j + 1),
            ((t : ℂ) ^ (q : ℕ)) * (if l.val + m.val = q.val then X l m else 0) := by
          refine (Finset.sum_congr rfl (fun l _ => Finset.sum_comm)).trans ?_
          exact Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro q _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.mul_sum]

end deg

def Lst (K m : ℕ) (y : Fin K → ℝ) : List ℝ := List.ofFn fun b : Fin m => if hb : m - 1 - b < K then y ⟨m - 1 - b, hb⟩ else 0

theorem lst_succ (K : ℕ) (a : Fin K) (y : Fin K → ℝ) (t : ℝ) :
    Lst K ((a : ℕ) + 1) (Function.update y a t) = t :: Lst K a y := by
  unfold Lst
  rw [List.ofFn_succ]
  congr 1
  · rw [dif_pos (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - ((0 : Fin ((a : ℕ) + 1)) : ℕ), by omega⟩ : Fin K) = a := Fin.ext (by simp)
    rw [e, Function.update_self]
  · congr 1
    funext i
    have hi := i.isLt
    rw [dif_pos (by simp; omega), dif_pos (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - (i.succ : ℕ), by simp; omega⟩ : Fin K) = ⟨(a : ℕ) - 1 - i, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [e, Function.update_of_ne]
    intro h'
    have := congrArg Fin.val h'
    simp at this
    omega

theorem lst_full (K : ℕ) (z : Fin K → ℝ) : Lst K K z = List.ofFn fun b => z (Fin.rev b) := by
  unfold Lst
  congr 1
  funext b
  rw [dif_pos (by omega)]
  congr 1
  ext
  simp [Fin.val_rev]
  omega

section final

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def SlicePolyAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F → ∀ (j : ℕ) (hj : j ≤ P.r) (h : C.LPt)
    (hh : D.IsLocPt h j), SlicePoly p.T F j hj h hh.2

theorem degWave_of (hS : SlicePolyAll) : KB.DegWave := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h h' hh hh' K grid s Mo hMo hF hgrid
  set W : ℕ → (Fin K → ℝ) → ℂ := fun m y => Wv p F j hj w h h' hh.2 hh'.2 s Mo (Lst K m y) with hW
  have hPS : F7.PolyStep K (2 * j) (fun _ => s) W := by
    intro a y
    obtain ⟨c, hc, hcs⟩ := wv_step p F j hj w h h' hh.2 hh'.2 s Mo (hS Wp Wq P p F hF j hj h hh)
      (hS Wp Wq P p F hF j hj h' hh') hMo (Lst K a y)
    refine ⟨c, ?_, fun t => ?_⟩
    · rw [hc, smul_eq_mul]
    · simp only [hW]
      rw [lst_succ, hcs t]
      simp only [smul_eq_mul]
  have hinj : ∀ a, Function.Injective (fun i => grid (Fin.rev a) i) := fun a => hgrid _
  have hE := Formalism.FourierDecayAlt.P.extract_K_bound ℂ K (2 * j) (fun _ => s) W (fun a => grid (Fin.rev a)) hPS hinj (fun _ => 0)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hE
  have hW0 : W 0 (fun _ => 0) = p.form j hj w (KB.waveG (p.T.bs j) s w (Mo (KB.slv p.T F j hj w h hh.2)))
      (KB.slv p.T F j hj w h' hh'.2) := rfl
  rw [hW0] at hE
  rw [hE]

  refine Fintype.sum_equiv ((Fin.revPerm).arrowCongr (Equiv.refl _)) _ _ (fun n => ?_)
  simp only [hW, smul_eq_mul]
  rw [lst_full]
  have e1 : (fun b : Fin K => grid (Fin.rev (Fin.rev b)) (n (Fin.rev b))) =
      fun b => grid b ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (2 * j + 1)))) n b) := by
    funext b
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  have e2 : (∏ a : Fin K, F7.lagCo (grid (Fin.rev a)) (n a)) =
      ∏ a : Fin K, F7.lagCo (grid a) ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (2 * j + 1)))) n a) := by
    refine Fintype.prod_equiv Fin.revPerm _ _ (fun a => ?_)
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  rw [e1, e2]
  rfl

end final

end Formalism.FourierDecayAlt.P.PBG
