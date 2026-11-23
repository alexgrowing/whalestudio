import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleInv

open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Col

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {r : ℕ}

def Jm : Matrix (Fin 2) (Fin 2) A := !![0, 1; -1, 0]

theorem tvl_conjT (L : R.LevelData A r) (hS : StarCoords L) (Y : ℂ) (hY : star Y = Y) (l : Fin r) :
    (L.Tvl Y l)ᴴ = (L.Tl Y l)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R.LevelData.Tl, R.LevelData.Tvl, Matrix.conjTranspose_apply, (hS l).1, (hS l).2.1,
      (hS l).2.2.1, (hS l).2.2.2.1, (hS l).2.2.2.2.1, (hS l).2.2.2.2.2, ← algebraMap_star_comm, hY]

theorem tJt (L : R.LevelData A r) (Y : ℂ) (l : Fin r) : (L.Tl (Y + 1) l)ᵀ * Jm * L.Tl Y l = Jm := by
  have e1 : L.p l * L.ci l = L.ci l * L.p l - L.ci l := by simpa using L.p_ci l l
  have e2 : algebraMap ℂ A Y * L.ci l = L.ci l * algebraMap ℂ A Y := Algebra.commutes Y (L.ci l)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R.LevelData.Tl, Jm, Matrix.mul_apply, Fin.sum_univ_two]
  · simp only [add_mul, mul_add, e1, e2, one_mul]
    abel
  · exact L.ci_c l
  · exact L.c_ci l

theorem diag_mul_comm (f : A) (X : Matrix (Fin 2) (Fin 2) A) (h : ∀ i j, Commute f (X i j)) :
    Matrix.diagonal (fun _ => f) * X = X * Matrix.diagonal (fun _ => f) := by
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, (h i j).eq]

theorem tl_comm (L : R.LevelData A r) (f : A) (l : Fin r) (Y : ℂ) (hp : Commute f (L.p l)) (hc : Commute f (L.c l))
    (hci : Commute f (L.ci l)) : ∀ i j, Commute f ((L.Tl Y l) i j) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [R.LevelData.Tl]
  all_goals first
    | exact (Algebra.commute_algebraMap_right Y f).add_right hp
    | exact hc
    | exact hc.neg_right
    | exact hci
    | exact Commute.zero_right f

theorem tele (L : R.LevelData A r) (Y : ℂ) (f : A) (ls : List (Fin r))
    (hls : ∀ l ∈ ls, Commute f (L.p l) ∧ Commute f (L.c l) ∧ Commute f (L.ci l)) :
    (ls.map (fun l => (L.Tl (Y + 1) l)ᵀ)).prod * (Matrix.diagonal (fun _ => f) * Jm) *
      (ls.map (L.Tl Y)).reverse.prod = Matrix.diagonal (fun _ => f) * Jm := by
  induction ls with
  | nil => simp
  | cons l t ih =>
    have hl := hls l (by simp)
    have ht : ∀ m ∈ t, Commute f (L.p m) ∧ Commute f (L.c m) ∧ Commute f (L.ci m) :=
      fun m hm => hls m (List.mem_cons_of_mem _ hm)
    simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.prod_append, List.prod_nil,
      Matrix.mul_one]
    rw [show ∀ (X P Q T M : Matrix (Fin 2) (Fin 2) A), X * P * M * (Q * T) = X * (P * M * Q) * T from
      fun X P Q T M => by simp only [Matrix.mul_assoc], ih ht]
    have hcomm : ∀ i j, Commute f ((L.Tl (Y + 1) l)ᵀ i j) :=
      fun i j => tl_comm L f l (Y + 1) hl.1 hl.2.1 hl.2.2 j i
    calc (L.Tl (Y + 1) l)ᵀ * (Matrix.diagonal (fun _ => f) * Jm) * L.Tl Y l
        = Matrix.diagonal (fun _ => f) * ((L.Tl (Y + 1) l)ᵀ * Jm * L.Tl Y l) := by
          rw [← Matrix.mul_assoc, ← diag_mul_comm f _ hcomm]
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun _ => f) * Jm := by rw [tJt]

theorem site_zero_matrix_entry (L : R.LevelData A r) (l : Fin r) (s Y : ℂ) (f : A) (hci : Commute f (L.ci l))
    (hp : L.p l * f = f * L.p l + algebraMap ℂ A s * f * L.c l) :
    (((L.Tl (Y + 1) l)ᵀ * (Matrix.diagonal (fun _ => f) * Jm) * L.Tl Y l : Matrix (Fin 2) (Fin 2) A) 0 0) =
      algebraMap ℂ A s * f := by
  have e1 : L.p l * L.ci l = L.ci l * L.p l - L.ci l := by simpa using L.p_ci l l
  have k2 : f * L.ci l = L.ci l * f := hci.eq
  have k1 : algebraMap ℂ A Y * (f * L.ci l) = L.ci l * (f * algebraMap ℂ A Y) := by
    rw [Algebra.commutes, k2, mul_assoc]
  have k3 : L.p l * (f * L.ci l) = L.ci l * (f * L.p l) - L.ci l * f + algebraMap ℂ A s * f := by
    calc L.p l * (f * L.ci l) = (L.p l * f) * L.ci l := (mul_assoc _ _ _).symm
      _ = f * (L.p l * L.ci l) + algebraMap ℂ A s * f * (L.c l * L.ci l) := by
        rw [hp]
        simp only [add_mul, mul_assoc]
      _ = f * (L.ci l * L.p l - L.ci l) + algebraMap ℂ A s * f := by rw [e1, L.c_ci, mul_one]
      _ = L.ci l * (f * L.p l) - L.ci l * f + algebraMap ℂ A s * f := by
        rw [mul_sub, ← mul_assoc, k2, mul_assoc]
  simp [R.LevelData.Tl, Jm, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [add_mul, mul_add, mul_assoc, one_mul]
  rw [k1, k3, k2]
  abel

end Col

theorem radial_collapse : RDCollapse := by
  intro A _ _ _ _ r hr L st s Y f fi hS hW hY
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have hY1 : star (Y + 1) = Y + 1 := by simp [hY]
  have hM : (L.Tvprod (Y + 1))ᴴ = ((List.finRange (k + 1)).map (fun l => (L.Tl (Y + 1) l)ᵀ)).prod := by
    rw [R.LevelData.Tvprod, Matrix.conjTranspose_list_prod, List.map_reverse, List.reverse_reverse,
      List.map_ofFn, List.ofFn_eq_map]
    congr 1
    apply List.map_congr_left
    intro l _
    exact tvl_conjT L hS (Y + 1) hY1 l
  have hN : L.Tprod Y = ((List.finRange (k + 1)).map (L.Tl Y)).reverse.prod := by
    rw [R.LevelData.Tprod, List.ofFn_eq_map]
  have key : star (L.Avr (Y + 1)) * f * L.Br Y - star (L.Bvr (Y + 1)) * f * L.Ar Y =
      ((L.Tvprod (Y + 1))ᴴ * (Matrix.diagonal (fun _ => f) * Jm) * L.Tprod Y :
        Matrix (Fin 2) (Fin 2) A) 0 0 := by
    simp [R.LevelData.Avr, R.LevelData.Bvr, R.LevelData.Ar, R.LevelData.Br, Matrix.mul_apply,
      Fin.sum_univ_two, Jm, Matrix.conjTranspose_apply]
    noncomm_ring
  have hls : ∀ l ∈ (List.finRange k).map Fin.succ,
      Commute f (L.p l) ∧ Commute f (L.c l) ∧ Commute f (L.ci l) := by
    intro l hl
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hl
    have hne : i.succ ≠ ⟨0, hr⟩ := Fin.succ_ne_zero i
    have h8 := hW.2.2.2.2.2.2.2.1 i.succ hne
    exact ⟨h8 _ (by simp [coordOps]), h8 _ (by simp [coordOps]), h8 _ (by simp [coordOps])⟩
  rw [key, hM, hN, List.finRange_succ, List.map_cons, List.map_cons, List.prod_cons, List.reverse_cons,
    List.prod_append, List.prod_singleton,
    show ∀ (X P Q T M : Matrix (Fin 2) (Fin 2) A), X * P * M * (Q * T) = X * (P * M * Q) * T from
      fun X P Q T M => by simp only [Matrix.mul_assoc], tele L Y f _ hls]
  exact site_zero_matrix_entry L 0 s Y f hW.2.2.1 hW.2.2.2.2.2.1

private theorem star_eq_self_of_right_inv_of_star_eq_self {A : Type} [Ring A] [StarRing A] {b bi : A} (hb : star b = b)
    (h1 : b * bi = 1) : star bi = bi := by
  have hsb : star bi * b = 1 := by
    calc star bi * b = star bi * star b := by rw [hb]
      _ = star (b * bi) := (star_mul b bi).symm
      _ = 1 := by rw [h1, star_one]
  calc star bi = star bi * (b * bi) := by rw [h1, mul_one]
    _ = bi := by rw [← mul_assoc, hsb, one_mul]

theorem radial_gauge_identity : RadialGaugeAdjointRelation := by
  intro A _ _ _ _ r L st Y hSL hS hLS hY hYi hY1i
  obtain ⟨hxx, hxx'⟩ := hLS.x_xi Y hYi
  obtain ⟨hxx1, hxx1'⟩ := hLS.x_xi (Y + 1) hY1i
  have h11 := congrFun (congrFun (hLS.start.det Y).1 1) 1
  simp [YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, hLS.tau] at h11
  have hrel : st.QQ (Y + 1) 0 1 * (L.GG * st.x Y) = L.GG * st.x (Y + 1) * st.QQ Y 0 1 := by
    rw [← sub_eq_zero]
    rw [← h11]
    noncomm_ring
  have hzb : star L.ζb = L.ζ := by rw [← hSL.1, star_star]
  have hGGs : star L.GG = L.GG := by
    rw [L.GG_def, star_sub, star_mul, hzb, hSL.1, ← algebraMap_star_comm, hSL.2.2]
  have hGGis : star L.GGi = L.GGi := star_eq_self_of_right_inv_of_star_eq_self hGGs L.GG_GGi
  have hxis : star (st.xi Y) = st.xi Y := star_eq_self_of_right_inv_of_star_eq_self (hLS.x_star Y hY) hxx
  have hQs : star (st.QQ Y 1 0) = st.QQ Y 0 1 := by
    have := congrFun (congrFun (hLS.start.herm Y hY) 0) 1
    simpa [Matrix.conjTranspose_apply] using this
  have hxG : Commute (st.x Y) L.GGi := hLS.x_fn Y _ (by simp [Fr.zfns])
  have hQ01 : st.QQ Y 0 1 = st.xi (Y + 1) * L.GGi * st.QQ (Y + 1) 0 1 * (L.GG * st.x Y) := by
    rw [mul_assoc (st.xi (Y + 1) * L.GGi), hrel,
      show st.xi (Y + 1) * L.GGi * (L.GG * st.x (Y + 1) * st.QQ Y 0 1) =
        st.xi (Y + 1) * (L.GGi * L.GG) * st.x (Y + 1) * st.QQ Y 0 1 by simp only [mul_assoc],
      L.GGi_GG, mul_one, hxx1', one_mul]
  have h1 : L.GG * st.x Y * (L.GGi * st.xi Y) = 1 := by
    rw [mul_assoc, ← mul_assoc (st.x Y), hxG.eq, mul_assoc, ← mul_assoc L.GG, L.GG_GGi, one_mul, hxx]
  rw [star_mul, star_mul, hQs, hGGis, hxis, hQ01, mul_assoc (st.xi (Y + 1) * L.GGi * st.QQ (Y + 1) 0 1), h1,
    mul_one]

section Rearr

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem comm_inv' {a b bi : A} (h : Commute a b) (h1 : b * bi = 1) (h2 : bi * b = 1) : Commute a bi := by
  show a * bi = bi * a
  calc a * bi = (bi * b) * a * bi := by rw [h2, one_mul]
    _ = bi * (b * a) * bi := by rw [mul_assoc bi b a]
    _ = bi * (a * b) * bi := by rw [h.eq]
    _ = bi * a * (b * bi) := by simp only [mul_assoc]
    _ = bi * a := by rw [h1, mul_one]

theorem star_inv' {b bi : A} (hb : star b = b) (h1 : b * bi = 1) (h2 : bi * b = 1) : star bi = bi := by
  have hsb : star bi * b = 1 := by
    calc star bi * b = star bi * star b := by rw [hb]
      _ = star (b * bi) := (star_mul b bi).symm
      _ = 1 := by rw [h1, star_one]
  calc star bi = star bi * (b * bi) := by rw [h1, mul_one]
    _ = bi := by rw [← mul_assoc, hsb, one_mul]

theorem canc {a b : A} (h : a * b = 1) (z : A) : a * (b * z) = z := by rw [← mul_assoc, h, one_mul]

theorem star_list_prod_comm (l : List A) (h : ∀ a ∈ l, ∀ b ∈ l, Commute (star a) (star b)) :
    star l.prod = (l.map star).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons, star_mul, List.map_cons, List.prod_cons,
      ih (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))]
    refine (Commute.list_prod_right _ _ ?_).eq.symm
    intro b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    exact h a (by simp) x (List.mem_cons_of_mem _ hx)

theorem star_ofFn_prod {r : ℕ} (g h : Fin r → A) (hs : ∀ i, star (g i) = h i) (hc : ∀ i j, Commute (h i) (h j)) :
    star (List.ofFn g).prod = (List.ofFn h).prod := by
  rw [star_list_prod_comm _ ?_, List.map_ofFn, show star ∘ g = h from funext hs]
  intro a ha b hb
  simp only [List.mem_ofFn] at ha hb
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  rw [hs, hs]
  exact hc i j

end Rearr

private theorem commute_list_ofFn_prod_of_commute {A : Type} [Ring A] {r : ℕ} (a : A) (g : Fin r → A)
    (h : ∀ i, Commute a (g i)) : Commute a (List.ofFn g).prod := by
  refine Commute.list_prod_right _ _ ?_
  intro b hb
  simp only [List.mem_ofFn] at hb
  obtain ⟨i, rfl⟩ := hb
  exact h i

private theorem commute_list_ofFn_prod_ofFn_prod {A : Type} [Ring A] {r : ℕ} (g h : Fin r → A)
    (hc : ∀ i j, Commute (g i) (h j)) : Commute (List.ofFn g).prod (List.ofFn h).prod :=
  commute_list_ofFn_prod_of_commute _ _ (fun j => (commute_list_ofFn_prod_of_commute _ _ (fun i => (hc i j).symm)).symm)

private theorem list_ofFn_prod_mul_ofFn_prod_eq_one {A : Type} [Ring A] {r : ℕ} (g h : Fin r → A)
    (hgh : ∀ i, g i * h i = 1) (hc : ∀ i j, Commute (g i) (h j)) :
    (List.ofFn g).prod * (List.ofFn h).prod = 1 := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have hP : Commute (List.ofFn fun i : Fin n => g i.succ).prod (h 0) :=
      (commute_list_ofFn_prod_of_commute (h 0) _ (fun i => (hc i.succ 0).symm)).symm
    rw [mul_assoc, ← mul_assoc _ (h 0), hP.eq, mul_assoc, ← mul_assoc (g 0), hgh 0, one_mul,
      ih (fun i => g i.succ) (fun i => h i.succ) (fun i => hgh _) (fun i j => hc _ _)]

private theorem commute_of_commute_mul_of_left_inv {A : Type} [Ring A] {G Gi x y : A} (h1 : Gi * G = 1)
    (hGx : Commute (G * x) y) (hG : Commute G y) : Commute x y := by
  show x * y = y * x
  calc x * y = Gi * (G * x) * y := by rw [← mul_assoc Gi, h1, one_mul]
    _ = Gi * ((G * x) * y) := mul_assoc _ _ _
    _ = Gi * (y * (G * x)) := by rw [hGx.eq]
    _ = Gi * (y * G * x) := by rw [← mul_assoc y]
    _ = Gi * (G * y * x) := by rw [← hG.eq]
    _ = y * x := by rw [mul_assoc G, ← mul_assoc Gi, h1, one_mul]

theorem radial_rearrangement : RDRearr := by
  intro A _ _ _ _ r hr L st s Y f fi hS hSL hLS hSC hW hY hYi hY1i hGa
  have hfc : ∀ a ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
      {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi}, ∀ b ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪
      Set.range L.cbi ∪ {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi}, Commute a b := L.fns_comm
  have hY1 : star (Y + 1) = Y + 1 := by simp [hY]
  obtain ⟨hx0, hx0'⟩ := hLS.x_xi Y hYi
  obtain ⟨hx1, hx1'⟩ := hLS.x_xi (Y + 1) hY1i
  have hWz := hW.2.2.2.2.2.2.2.2.1
  have hWQ := hW.2.2.2.2.2.2.2.2.2
  have hfG : Commute f L.GG := hWz _ (by simp [Fr.zfns])
  have hfGi : Commute f L.GGi := hWz _ (by simp [Fr.zfns])
  have hfl : ∀ l, Commute f (L.c l) ∧ Commute f (L.ci l) ∧ Commute f (L.cb l) ∧ Commute f (L.cbi l) := by
    intro l
    by_cases hl : l = ⟨0, hr⟩
    · subst hl
      exact ⟨hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩
    · have h8 := hW.2.2.2.2.2.2.2.1 l hl
      exact ⟨h8 _ (by simp [coordOps]), h8 _ (by simp [coordOps]), h8 _ (by simp [coordOps]),
        h8 _ (by simp [coordOps])⟩
  have hfD : Commute f L.Dr := commute_list_ofFn_prod_of_commute _ _ (fun i => (hfl i).1)
  have hfDi : Commute f L.Dri := commute_list_ofFn_prod_of_commute _ _ (fun i => (hfl i).2.1)
  have hxg : ∀ Z l y, y ∈ coordOps L l → Commute L.GG y → Commute (st.x Z) y :=
    fun Z l y hy hG => commute_of_commute_mul_of_left_inv L.GGi_GG (by rw [← hLS.tau]; exact hSC Z 1 1 l y hy) hG
  have hxDb : ∀ Z, Commute (st.x Z) L.Drb := fun Z =>
    commute_list_ofFn_prod_of_commute _ _ (fun i => hxg Z i _ (by simp [coordOps]) (hfc _ (by simp) _ (by simp)))
  have hxG : ∀ Z, Commute (st.x Z) L.GG := fun Z => hLS.x_fn Z _ (by simp [Fr.zfns])
  have hxGi : ∀ Z, Commute (st.x Z) L.GGi := fun Z => hLS.x_fn Z _ (by simp [Fr.zfns])
  have hxiDb0 : Commute (st.xi Y) L.Drb := (comm_inv' (hxDb Y).symm hx0 hx0').symm
  have hxiDb1 : Commute (st.xi (Y + 1)) L.Drb := (comm_inv' (hxDb (Y + 1)).symm hx1 hx1').symm
  have hxiG0 : Commute (st.xi Y) L.GG := (comm_inv' (hxG Y).symm hx0 hx0').symm
  have hxiG1 : Commute (st.xi (Y + 1)) L.GG := (comm_inv' (hxG (Y + 1)).symm hx1 hx1').symm
  have hxiGi0 : Commute (st.xi Y) L.GGi := (comm_inv' (hxGi Y).symm hx0 hx0').symm
  have hxiGi1 : Commute (st.xi (Y + 1)) L.GGi := (comm_inv' (hxGi (Y + 1)).symm hx1 hx1').symm
  have hfx1 : Commute f (st.x (Y + 1)) :=
    (commute_of_commute_mul_of_left_inv L.GGi_GG (by rw [← hLS.tau]; exact (hWQ (Y + 1) 1 1).symm) hfG.symm).symm
  have hfxi1 : Commute f (st.xi (Y + 1)) := comm_inv' hfx1 hx1 hx1'
  have hGiDb : Commute L.GGi L.Drb := commute_list_ofFn_prod_of_commute _ _ (fun i => hfc _ (by simp) _ (by simp))
  have hDbDi : Commute L.Drb L.Dri := commute_list_ofFn_prod_ofFn_prod _ _ (fun i j => hfc _ (by simp) _ (by simp))
  have hDDi : L.Dr * L.Dri = 1 := list_ofFn_prod_mul_ofFn_prod_eq_one _ _ L.c_ci (fun i j => hfc _ (by simp) _ (by simp))
  have hDiD : L.Dri * L.Dr = 1 := list_ofFn_prod_mul_ofFn_prod_eq_one _ _ L.ci_c (fun i j => hfc _ (by simp) _ (by simp))
  have hDbDbi : L.Drb * L.Drbi = 1 :=
    list_ofFn_prod_mul_ofFn_prod_eq_one _ _ L.cb_cbi (fun i j => hfc _ (by simp) _ (by simp))
  have hDbiDb : L.Drbi * L.Drb = 1 :=
    list_ofFn_prod_mul_ofFn_prod_eq_one _ _ L.cbi_cb (fun i j => hfc _ (by simp) _ (by simp))
  have hsD : star L.Dr = L.Drb :=
    star_ofFn_prod _ _ (fun i => (hS i).2.2.1) (fun i j => hfc _ (by simp) _ (by simp))
  have hsDb : star L.Drb = L.Dr :=
    star_ofFn_prod _ _ (fun i => (hS i).2.2.2.1) (fun i j => hfc _ (by simp) _ (by simp))
  have hsDi : star L.Dri = L.Drbi :=
    star_ofFn_prod _ _ (fun i => (hS i).2.2.2.2.1) (fun i j => hfc _ (by simp) _ (by simp))
  have hsDbi : star L.Drbi = L.Dri :=
    star_ofFn_prod _ _ (fun i => (hS i).2.2.2.2.2) (fun i j => hfc _ (by simp) _ (by simp))
  have hzb : star L.ζb = L.ζ := by rw [← hSL.1, star_star]
  have hGs : star L.GG = L.GG := by
    rw [L.GG_def, star_sub, star_mul, hzb, hSL.1, ← algebraMap_star_comm, hSL.2.2]
  have hGis : star L.GGi = L.GGi := star_inv' hGs L.GG_GGi L.GGi_GG
  have hx1s : star (st.x (Y + 1)) = st.x (Y + 1) := hLS.x_star (Y + 1) hY1
  have hxi1s : star (st.xi (Y + 1)) = st.xi (Y + 1) := star_inv' hx1s hx1 hx1'
  have hQ1s : star (st.QQ (Y + 1) 0 1) = st.QQ (Y + 1) 1 0 := by
    have := congrFun (congrFun (hLS.start.herm (Y + 1) hY1) 1) 0
    simpa [Matrix.conjTranspose_apply] using this
  have B1 : L.Dr * (f * (L.Dri * (L.Drbi * (L.GGi * (st.xi Y * (L.Drb * st.QQ Y 1 0)))))) =
      f * (L.GGi * (st.xi Y * st.QQ Y 1 0)) := by
    rw [hfD.symm.left_comm, canc hDDi, hxiDb0.left_comm, hGiDb.left_comm, canc hDbiDb]
  have B2 : L.Dr * (f * (L.Dri * (L.Drbi * (L.GGi * (st.xi Y * (L.Drb * (L.GG * st.x Y))))))) = f := by
    rw [hfD.symm.left_comm, canc hDDi, hxiDb0.left_comm, hGiDb.left_comm, canc hDbiDb,
      hxiG0.left_comm, canc L.GGi_GG, hx0', mul_one]
  have B3 : L.Drb * (st.xi (Y + 1) * (L.GGi * (L.Dri * (L.Drbi * (f * L.Dr))))) =
      st.xi (Y + 1) * (L.GGi * f) := by
    rw [hxiDb1.symm.left_comm, hGiDb.symm.left_comm, hDbDi.left_comm, canc hDbDbi, hfDi.symm.left_comm,
      hDiD, mul_one]
  have B4 : st.x (Y + 1) * (L.GG * (L.Drb * (st.xi (Y + 1) * (L.GGi * (L.Dri * (L.Drbi * (f * L.Dr))))))) =
      f := by
    rw [B3, hxiG1.symm.left_comm, canc L.GG_GGi, canc hx1]
  have hfQ : Commute f (star (st.QQ (Y + 1) 0 1)) := by
    rw [hQ1s]
    exact hWQ (Y + 1) 1 0
  have hG' : st.xi Y * L.GGi * st.QQ Y 1 0 = star (st.QQ (Y + 1) 0 1) * (L.GGi * st.xi (Y + 1)) := by
    have := congrArg star hGa
    rwa [star_star, star_mul, star_mul, hGis, hxi1s] at this
  have E3 : f * (L.GGi * (st.xi Y * st.QQ Y 1 0)) =
      star (st.QQ (Y + 1) 0 1) * (st.xi (Y + 1) * (L.GGi * f)) := by
    calc f * (L.GGi * (st.xi Y * st.QQ Y 1 0)) = f * (st.xi Y * L.GGi * st.QQ Y 1 0) := by
          rw [← mul_assoc L.GGi, hxiGi0.symm.eq]
      _ = f * (star (st.QQ (Y + 1) 0 1) * (L.GGi * st.xi (Y + 1))) := by rw [hG']
      _ = star (st.QQ (Y + 1) 0 1) * (f * (L.GGi * st.xi (Y + 1))) := by
          rw [← mul_assoc, hfQ.eq, mul_assoc]
      _ = star (st.QQ (Y + 1) 0 1) * (st.xi (Y + 1) * (L.GGi * f)) := by
          rw [hfGi.left_comm, hfxi1.eq, hxiGi1.symm.left_comm]
  have E1 : star (thR L st Y 0) * f * thR L st Y 1 =
      star (L.Avr (Y + 1)) * (L.Dr * (f * (L.Dri * (L.Drbi * (L.GGi * (st.xi Y * (L.Drb *
        (L.GG * st.x Y)))))))) * L.Br Y +
      star (L.Avr (Y + 1)) * (L.Dr * (f * (L.Dri * (L.Drbi * (L.GGi * (st.xi Y * (L.Drb *
        st.QQ Y 1 0))))))) * L.Ar Y := by
    rw [show thR L st Y 0 = L.Drb * L.Avr (Y + 1) from rfl,
      show thR L st Y 1 = L.Dri * L.Drbi * L.GGi * st.xi Y *
        (L.Drb * (st.QQ Y 1 0 * L.Ar Y + st.QQ Y 1 1 * L.Br Y)) from rfl, hLS.tau, star_mul, hsDb]
    simp only [mul_add, add_mul, mul_assoc]
    all_goals abel
  have E2 : star (thR L st Y 2) * f * thR L st Y 3 =
      star (L.Bvr (Y + 1)) * (st.x (Y + 1) * (L.GG * (L.Drb * (st.xi (Y + 1) * (L.GGi * (L.Dri *
        (L.Drbi * (f * L.Dr)))))))) * L.Ar Y +
      star (L.Avr (Y + 1)) * (star (st.QQ (Y + 1) 0 1) * (L.Drb * (st.xi (Y + 1) * (L.GGi * (L.Dri *
        (L.Drbi * (f * L.Dr))))))) * L.Ar Y := by
    rw [show thR L st Y 2 = L.Dri * L.Drbi * L.GGi * st.xi (Y + 1) *
        (L.Dr * (st.QQ (Y + 1) 0 1 * L.Avr (Y + 1) + st.QQ (Y + 1) 1 1 * L.Bvr (Y + 1))) from rfl,
      show thR L st Y 3 = L.Dr * L.Ar Y from rfl, hLS.tau]
    simp only [star_mul, star_add, hsD, hsDi, hsDbi, hGis, hxi1s, hx1s, hGs, mul_add, add_mul, mul_assoc]
    all_goals abel
  rw [E1, E2, B2, B1, B4, B3, E3]
  abel

end Formalism.FourierDecayAlt.P.CutSE
