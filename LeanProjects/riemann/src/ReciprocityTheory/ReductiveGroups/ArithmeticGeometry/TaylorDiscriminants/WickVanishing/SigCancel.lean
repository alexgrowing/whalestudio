import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CoeffActAdd

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem dof_expS (F : Fin d → PS k 2 d) (u : Fin d → k) {f : PS k 1 d} (hf : constantCoeff f = 0) :
    Dof F u (FB.expS k f) = FB.expS k f * Dof F u f := by
  unfold Dof
  simp only [pderiv_expS hf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dof_Cmul (F : Fin d → PS k 2 d) (u : Fin d → k) (a : k) (g : PS k 1 d) :
    Dof F u (C a * g) = C a * Dof F u g := by
  have hD : ∀ j, pderiv k ((0 : Fin 1), j) (C a * g) = C a * pderiv k ((0 : Fin 1), j) g := by
    intro j
    rw [Derivation.leibniz]
    have h0 : pderiv k ((0 : Fin 1), j) (C a : PS k 1 d) = 0 := by
      rw [show (C a : PS k 1 d) = algebraMap k (PS k 1 d) a from rfl]
      exact Derivation.map_algebraMap _ _
    rw [h0, smul_zero, add_zero, smul_eq_mul]
  simp only [Dof, hD]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ig_dAct (B : FB R d O) (a : O) (i j : Fin d) : (C (dAct k B a i j) : PS k 1 d) ∈ Ig R k (Fin 1 × Fin d) := by
  unfold Ig
  refine RingHom.mem_range.2 ⟨C (coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act a i)), ?_⟩
  simp [dAct, FB.actK, MvPowerSeries.coeff_map]

theorem hL_eq (B : FB R d O) (h : PS k 2 d) (w0 : O) :
    B.hL k h w0 = ev (n := 1) ![pt k d 0, B.actK k w0] h := by
  have hc : comp1 (B.actK k w0) (pt k d 0) = B.actK k w0 := by
    funext i
    unfold comp1 ev
    have hX : (fun p : Fin 1 × Fin d => (![pt k d 0] : Fin 1 → Pt k 1 d) p.1 p.2) = MvPowerSeries.X := by
      funext p
      obtain ⟨a, b⟩ := p
      fin_cases a
      rfl
    rw [hX, MvPowerSeries.subst_self]
    rfl
  unfold FB.hL
  rw [hc]

theorem dof_hL (B : FB R d O) (h : PS k 2 d) (w0 : O) (u : Fin d → k) :
    Dof (B.FK k) u (ev (n := 1) ![pt k d 0, B.actK k w0] h) =
      ∑ b, C (u b) * ev (n := 1) ![pt k d 0, B.actK k w0]
          (∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b)) +
        ∑ j, (∑ b, C (u b) * C (dAct k B w0 j b)) * ev (n := 1) ![pt k d 0, B.actK k w0]
          (∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1] (Jac (lawK k B) c j)) := by
  have cPA : CZ (![pt k (n := 1) d 0, B.actK k w0] : Fin 2 → Pt k 1 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (const_actK' B w0) CZ.nil)
  have cAk : CZ (![B.actK k w0] : Fin 1 → Pt k 1 d) := CZ.cons (const_actK' B w0) CZ.nil
  have evx : ∀ g : PS k 1 d, ev (n := 1) ![pt k d 0, B.actK k w0] (ev (n := 2) ![pt k d 0] g) = g := by
    intro g
    rw [ev_ev cPA zero_constant_first_point]
    have : (fun j c => ev (n := 1) ![pt k d 0, B.actK k w0] ((![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) j c)) =
        (![pt k (n := 1) d 0] : Fin 1 → Pt k 1 d) := by
      funext j c; fin_cases j; simp [pt_apply, ev_X cPA]
    rw [this, gt_ev_pt_self]
  have evz : ∀ g : PS k 1 d, ev (n := 1) ![pt k d 0, B.actK k w0] (ev (n := 2) ![pt k d 1] g) = ev (n := 1) ![B.actK k w0] g := by
    intro g
    rw [ev_ev cPA czY]
    congr 1
    funext j c; fin_cases j; simp [pt_apply, ev_X cPA]
  have dh : ∀ j, pderiv k ((0 : Fin 1), j) (ev (n := 1) ![pt k d 0, B.actK k w0] h) = ev (n := 1) ![pt k d 0, B.actK k w0] (pderiv k ((0 : Fin 2), j) h) +
      ∑ c, ev (n := 1) ![pt k d 0, B.actK k w0] (pderiv k ((1 : Fin 2), c) h) * pderiv k ((0 : Fin 1), j) (B.actK k w0 c) := by
    intro j
    rw [d2 cPA]
    congr 1
    simp [pderiv_pt]
  have hDof : ∀ g : PS k 1 d, Dof (B.FK k) u g = ∑ j, (∑ b, C (u b) * Jac (lawK k B) j b) * pderiv k ((0 : Fin 1), j) g :=
    fun g => rfl
  have eD1 : ∀ b, ev (n := 1) ![pt k d 0, B.actK k w0] (∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b)) =
      ∑ c, ev (n := 1) ![pt k d 0, B.actK k w0] (pderiv k ((0 : Fin 2), c) h) * Jac (lawK k B) c b := by
    intro b; rw [ev_sum cPA]; simp only [ev_mul cPA, evx]
  have eD2 : ∀ j, ev (n := 1) ![pt k d 0, B.actK k w0] (∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1] (Jac (lawK k B) c j)) =
      ∑ c, ev (n := 1) ![pt k d 0, B.actK k w0] (pderiv k ((1 : Fin 2), c) h) * ev (n := 1) ![B.actK k w0] (Jac (lawK k B) c j) := by
    intro j; rw [ev_sum cPA]; simp only [ev_mul cPA, evz]
  have hm : ∀ c, ∑ j, (∑ b, C (u b) * Jac (lawK k B) j b) * pderiv k ((0 : Fin 1), j) (B.actK k w0 c) =
      ∑ j, (∑ b, C (u b) * C (dAct k B w0 j b)) * ev (n := 1) ![B.actK k w0] (Jac (lawK k B) c j) := by
    intro c
    calc ∑ j, (∑ b, C (u b) * Jac (lawK k B) j b) * pderiv k ((0 : Fin 1), j) (B.actK k w0 c)
        = ∑ b, C (u b) * ∑ j, pderiv k ((0 : Fin 1), j) (B.actK k w0 c) * Jac (lawK k B) j b := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = ∑ b, C (u b) * ∑ j, ev (n := 1) ![B.actK k w0] (Jac (lawK k B) c j) * C (dAct k B w0 j b) :=
          Finset.sum_congr rfl fun b _ => by rw [hom_rel B w0 c b]
      _ = ∑ j, (∑ b, C (u b) * C (dAct k B w0 j b)) * ev (n := 1) ![B.actK k w0] (Jac (lawK k B) c j) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hDof]
  simp only [dh, mul_add, Finset.sum_add_distrib, eD1, eD2]
  congr 1
  · simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · have e2 : ∑ j, (∑ b, C (u b) * Jac (lawK k B) j b) * ∑ c, ev (n := 1) ![pt k d 0, B.actK k w0] (pderiv k ((1 : Fin 2), c) h) *
        pderiv k ((0 : Fin 1), j) (B.actK k w0 c) =
        ∑ c, ev (n := 1) ![pt k d 0, B.actK k w0] (pderiv k ((1 : Fin 2), c) h) *
          ∑ j, (∑ b, C (u b) * Jac (lawK k B) j b) * pderiv k ((0 : Fin 1), j) (B.actK k w0 c) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e2]
    simp only [hm, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sig_cancel (B : FB R d O) (h : PS k 2 d) (w0 : O) (hw : w0 + star w0 = 1) (u : Fin d → k) :
    ∑ b, C (u b) * ∑ c, sgOf k h c * C (dAct k B (star w0) c b) +
      ∑ j, (∑ b, C (u b) * C (dAct k B w0 j b)) * sgOf k h j = ∑ c, sgOf k h c * C (u c) := by
  have hu : ∀ c, ∑ b, C (u b) * (C (dAct k B w0 c b) + C (dAct k B (star w0) c b)) = (C (u c) : PS k 1 d) := by
    intro c
    rw [Finset.sum_eq_single c]
    · rw [← map_add, dAct_sum B w0 hw c c, if_pos rfl, map_one, mul_one]
    · intro b _ hb
      rw [← map_add, dAct_sum B w0 hw c b, if_neg (Ne.symm hb), map_zero, mul_zero]
    · intro hc; exact absurd (Finset.mem_univ c) hc
  have L1 : ∑ b, C (u b) * ∑ c, sgOf k h c * C (dAct k B (star w0) c b) =
      ∑ c, ∑ b, sgOf k h c * (C (u b) * C (dAct k B (star w0) c b)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have L2 : ∑ j, (∑ b, C (u b) * C (dAct k B w0 j b)) * sgOf k h j =
      ∑ c, ∑ b, sgOf k h c * (C (u b) * C (dAct k B w0 c b)) := by
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have L3 : ∑ c, sgOf k h c * C (u c) = ∑ c, ∑ b, sgOf k h c * (C (u b) * C (dAct k B w0 c b)) +
      ∑ c, ∑ b, sgOf k h c * (C (u b) * C (dAct k B (star w0) c b)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib, ← hu c, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [L1, L2, L3]
  ring

theorem rel_hL {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (w0 : O) (hw : w0 + star w0 = 1)
    (u : Fin d → k) (hu : ∀ j, ∃ r, algebraMap R k r = u j) :
    Dof (B.FK k) u (B.hL k h w0) + ∑ c, sgOf k h c * C (u c) ∈ Ig R k (Fin 1 × Fin d) := by
  have iu : ∀ b, (C (u b) : PS k 1 d) ∈ Ig R k (Fin 1 × Fin d) := fun b => by
    obtain ⟨r, hr⟩ := hu b
    rw [← hr]
    exact ig_C r
  have cPA : CZ (![pt k (n := 1) d 0, B.actK k w0] : Fin 2 → Pt k 1 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (const_actK' B w0) CZ.nil)
  have iPA : ∀ j i, (![pt k (n := 1) d 0, B.actK k w0] : Fin 2 → Pt k 1 d) j i ∈ Ig R k (Fin 1 × Fin d) := by
    intro j i; fin_cases j
    · exact ig_pt _ _
    · exact ig_map _
  have evz : ∀ g : PS k 1 d, ev (n := 1) ![pt k d 0, B.actK k w0] (ev (n := 2) ![pt k d 1] g) =
      ev (n := 1) ![B.actK k w0] g := by
    intro g
    rw [ev_ev cPA czY]
    congr 1
    funext j c; fin_cases j; simp [pt_apply, ev_X cPA]
  have evx : ∀ g : PS k 1 d, ev (n := 1) ![pt k d 0, B.actK k w0] (ev (n := 2) ![pt k d 0] g) = g := by
    intro g
    rw [ev_ev cPA zero_constant_first_point]
    have : (fun j c => ev (n := 1) ![pt k d 0, B.actK k w0] ((![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) j c)) =
        (![pt k (n := 1) d 0] : Fin 1 → Pt k 1 d) := by
      funext j c; fin_cases j; simp [pt_apply, ev_X cPA]
    rw [this, gt_ev_pt_self]
  have E1 : ∀ b, ev (n := 1) ![pt k d 0, B.actK k w0]
      (∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b)) =
      (ev (n := 1) ![pt k d 0, B.actK k w0] (∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0]
          (Jac (lawK k B) c b) - ev (n := 2) ![0, pt k d 1] (pderiv k ((0 : Fin 2), b) h)) +
        ev (n := 1) ![pt k d 0, B.actK k w0] (ev (n := 2) ![pt k d 1] (sgOf k h b) +
          ev (n := 2) ![0, pt k d 1] (pderiv k ((0 : Fin 2), b) h)) +
        (∑ c, sgOf k h c * C (dAct k B (star w0) c b) - ev (n := 1) ![B.actK k w0] (sgOf k h b))) -
      ∑ c, sgOf k h c * C (dAct k B (star w0) c b) := by
    intro b
    rw [ev_sub cPA, ev_add cPA, evz]
    ring
  have E2 : ∀ j, ev (n := 1) ![pt k d 0, B.actK k w0]
      (∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1] (Jac (lawK k B) c j)) =
      ev (n := 1) ![pt k d 0, B.actK k w0] (∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1]
        (Jac (lawK k B) c j) + ev (n := 2) ![pt k d 0] (sgOf k h j)) - sgOf k h j := by
    intro j
    rw [ev_add cPA, evx]
    ring
  rw [hL_eq, dof_hL, ← sig_cancel B h w0 hw u]
  simp only [E1, E2, mul_sub, Finset.sum_sub_distrib]
  have key : ∀ (X1 X2 Y1 Y2 : PS k 1 d), X1 - Y1 + (X2 - Y2) + (Y1 + Y2) = X1 + X2 := fun _ _ _ _ => by ring
  rw [key]
  refine add_mem (sum_mem fun b _ => mul_mem (iu b) ?_) (sum_mem fun j _ => mul_mem ?_ ?_)
  · exact add_mem (add_mem (ig_ev cPA iPA (first_derivative_shift_integral hc b)) (ig_ev cPA iPA (rel_sy hc b))) (rel_ad hc w0 b)
  · exact sum_mem fun b _ => mul_mem (iu b) (ig_dAct B w0 j b)
  · exact ig_ev cPA iPA (second_derivative_shift_integral hc j)

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
