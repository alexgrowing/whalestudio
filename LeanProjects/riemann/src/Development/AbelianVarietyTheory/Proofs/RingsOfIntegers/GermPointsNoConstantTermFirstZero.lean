import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.FourierCoeffIntSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.DerivEndo

variable {R : Type} [CommRing R] {d : ℕ}

def NoConst {m n : ℕ} (a : Fin m → Pt R n d) : Prop := ∀ j i, constantCoeff (a j i) = 0

theorem NoConst.hasSubst {m n : ℕ} {a : Fin m → Pt R n d} (ha : NoConst a) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
  apply hasSubst_of_constantCoeff_zero
  rintro ⟨j, i⟩
  exact ha j i

theorem noConst_one {n : ℕ} {a : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0) :
    NoConst (![a] : Fin 1 → Pt R n d) := by
  intro j i
  rw [Fin.fin_one_eq_zero j]
  exact ha i

theorem noConst_two {n : ℕ} {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) : NoConst (![a, b] : Fin 2 → Pt R n d) := by
  intro j i
  fin_cases j
  · exact ha i
  · exact hb i

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  unfold pt
  simp

theorem cc_ev {m n : ℕ} {a : Fin m → Pt R n d} (ha : NoConst a) (f : PS R m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  rw [GlobalTheory.FormalCalc.constantCoeff_subst_of_zero ha.hasSubst (fun p => ha p.1 p.2)]
  rfl

theorem ev_pt {m n : ℕ} {a : Fin m → Pt R n d} (ha : NoConst a) (j : Fin m) (i : Fin d) :
    ev a (pt R d j i) = a j i := by
  unfold ev pt
  exact subst_X ha.hasSubst (j, i)

theorem ev_zero {m n : ℕ} {a : Fin m → Pt R n d} (ha : NoConst a) :
    ev a (0 : PS R m d) = 0 := by
  unfold ev
  rw [← coe_substAlgHom ha.hasSubst, map_zero]

theorem ev_mul {m n : ℕ} {a : Fin m → Pt R n d} (ha : NoConst a) (f g : PS R m d) :
    ev a (f * g) = ev a f * ev a g := by
  unfold ev
  rw [← coe_substAlgHom ha.hasSubst]
  exact map_mul _ f g

theorem ev_add {m n : ℕ} {a : Fin m → Pt R n d} (ha : NoConst a) (f g : PS R m d) :
    ev a (f + g) = ev a f + ev a g := by
  unfold ev
  rw [← coe_substAlgHom ha.hasSubst]
  exact map_add _ f g

theorem ev_sum {m n : ℕ} {a : Fin m → Pt R n d} (ha : NoConst a) {κ : Type} (s : Finset κ)
    (f : κ → PS R m d) : ev a (∑ k ∈ s, f k) = ∑ k ∈ s, ev a (f k) := by
  unfold ev
  rw [← coe_substAlgHom ha.hasSubst]
  exact map_sum _ f s

theorem ev_C {m n : ℕ} (a : Fin m → Pt R n d) (r : R) : ev a (C r : PS R m d) = C r := by
  unfold ev
  rw [subst_C]

theorem ev_ev {l m n : ℕ} {a : Fin l → Pt R m d} {b : Fin m → Pt R n d} (hb : NoConst b)
    (ha : NoConst a) (f : PS R l d) :
    ev b (ev a f) = ev (fun j i => ev b (a j i)) f := by
  unfold ev
  rw [subst_comp_subst_apply ha.hasSubst hb.hasSubst]

theorem ev_id (f : PS R 1 d) : ev (n := 1) ![pt R d 0] f = f := by
  have hX : (fun p : Fin 1 × Fin d => (![pt R d 0] : Fin 1 → Pt R 1 d) p.1 p.2) = X := by
    funext p
    rcases p with ⟨j, i⟩
    rw [Fin.fin_one_eq_zero j]
    rfl
  unfold ev
  rw [hX, subst_self]
  rfl

theorem ev_const {m n : ℕ} (f : PS R m d) :
    ev (fun _ _ => (0 : PS R n d)) f = C (constantCoeff f) := by
  unfold ev
  show subst (0 : Fin m × Fin d → PS R n d) f = _
  rw [subst_zero_eq_C_constantCoeff]
  simp

theorem pderiv_ev {m n : ℕ} {a : Fin m → Pt R n d} (ha : NoConst a) (f : PS R m d)
    (v : Fin n × Fin d) :
    pderiv R v (ev a f) = ∑ j, ∑ i, ev a (pderiv R (j, i) f) * pderiv R v (a j i) := by
  unfold ev
  rw [GlobalTheory.FormalCalc.pderiv_subst ha.hasSubst, Fintype.sum_prod_type]

theorem germPointsNoConstantTerm_first_zero : NoConst (![pt R (n := 1) d 0, 0] : Fin 2 → Pt R 1 d) := by
  intro j i
  fin_cases j
  · exact cc_pt 0 i
  · exact map_zero _

theorem formalGroupLaw_ev_second_zero (G : FGLaw R d) (c : Fin d) :
    ev (n := 1) ![pt R d 0, 0] (G.F c) = pt R (n := 1) d 0 c := by
  have hs : NoConst (![pt R (n := 2) d 1, pt R (n := 2) d 0] : Fin 2 → Pt R 2 d) :=
    noConst_two (cc_pt 1) (cc_pt 0)
  have hfam : (fun j i => ev (n := 1) ![pt R d 0, 0]
      ((![pt R (n := 2) d 1, pt R (n := 2) d 0] : Fin 2 → Pt R 2 d) j i)) =
        (![0, pt R d 0] : Fin 2 → Pt R 1 d) := by
    funext j i
    fin_cases j
    · show ev (n := 1) ![pt R d 0, 0] (pt R d 1 i) = 0
      rw [ev_pt germPointsNoConstantTerm_first_zero]
      rfl
    · show ev (n := 1) ![pt R d 0, 0] (pt R d 0 i) = pt R d 0 i
      rw [ev_pt germPointsNoConstantTerm_first_zero]
      rfl
  rw [← G.comm c, ev_ev germPointsNoConstantTerm_first_zero hs, hfam]
  exact G.unit c

private theorem ev_xy_eq (f : PS R 2 d) :
    ev (n := 2) (![pt R (n := 2) d 0, pt R (n := 2) d 1] : Fin 2 → Pt R 2 d) f = f := by
  have hX : (fun p : Fin 2 × Fin d =>
      (![pt R (n := 2) d 0, pt R (n := 2) d 1] : Fin 2 → Pt R 2 d) p.1 p.2) = X := by
    funext p
    rcases p with ⟨j, i⟩
    fin_cases j <;> rfl
  unfold ev
  rw [hX, subst_self]
  rfl

theorem add_pt (G : FGLaw R d) : G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1) = G.F := by
  funext c
  exact ev_xy_eq (G.F c)

theorem germ_ev_restrict_axis_first_point (h : PS R 1 d) : ev (n := 1) ![pt R d 0, 0] (ev (n := 2) ![pt R d 0] h) = h := by
  have hx : NoConst (![pt R (n := 2) d 0] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 0)
  have hfam : (fun j i => ev (n := 1) ![pt R d 0, 0]
      ((![pt R (n := 2) d 0] : Fin 1 → Pt R 2 d) j i)) = (![pt R d 0] : Fin 1 → Pt R 1 d) := by
    funext j i
    rw [Fin.fin_one_eq_zero j]
    show ev (n := 1) ![pt R d 0, 0] (pt R d 0 i) = pt R d 0 i
    rw [ev_pt germPointsNoConstantTerm_first_zero]
    rfl
  rw [ev_ev germPointsNoConstantTerm_first_zero hx, hfam, ev_id]

theorem germ_ev_restrict_axis_second_point (h : PS R 1 d) :
    ev (n := 1) ![pt R d 0, 0] (ev (n := 2) ![pt R d 1] h) = C (constantCoeff h) := by
  have hy : NoConst (![pt R (n := 2) d 1] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 1)
  have hfam : (fun j i => ev (n := 1) ![pt R d 0, 0]
      ((![pt R (n := 2) d 1] : Fin 1 → Pt R 2 d) j i)) = fun _ _ => (0 : PS R 1 d) := by
    funext j i
    rw [Fin.fin_one_eq_zero j]
    show ev (n := 1) ![pt R d 0, 0] (pt R d 1 i) = 0
    rw [ev_pt germPointsNoConstantTerm_first_zero]
    rfl
  rw [ev_ev germPointsNoConstantTerm_first_zero hy, hfam, ev_const]

theorem germ_ev_restrict_axis_groupLaw (G : FGLaw R d) (h : PS R 1 d) :
    ev (n := 1) ![pt R d 0, 0] (ev (n := 2) ![G.F] h) = h := by
  have hfam : (fun j i => ev (n := 1) ![pt R d 0, 0]
      ((![G.F] : Fin 1 → Pt R 2 d) j i)) = (![pt R d 0] : Fin 1 → Pt R 1 d) := by
    funext j i
    rw [Fin.fin_one_eq_zero j]
    exact formalGroupLaw_ev_second_zero G i
  rw [ev_ev germPointsNoConstantTerm_first_zero (noConst_one G.const), hfam, ev_id]

theorem pderiv_second_of_ev_first_point (h : PS R 1 d) (i : Fin d) :
    pderiv R ((1 : Fin 2), i) (ev (n := 2) ![pt R d 0] h) = 0 := by
  have hx : NoConst (![pt R (n := 2) d 0] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 0)
  rw [pderiv_ev hx]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  rw [Fin.fin_one_eq_zero j]
  show _ * pderiv R ((1 : Fin 2), i) (X ((0 : Fin 2), k)) = 0
  rw [pderiv_X_of_ne (by simp), mul_zero]

theorem dy_y (h : PS R 1 d) (i : Fin d) :
    pderiv R ((1 : Fin 2), i) (ev (n := 2) ![pt R d 1] h) =
      ev (n := 2) ![pt R d 1] (pderiv R ((0 : Fin 1), i) h) := by
  have hy : NoConst (![pt R (n := 2) d 1] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 1)
  rw [pderiv_ev hy, Fin.sum_univ_one, Finset.sum_eq_single i]
  · show _ * pderiv R ((1 : Fin 2), i) (X ((1 : Fin 2), i)) = _
    rw [pderiv_X_self, mul_one]
  · intro k _ hk
    show _ * pderiv R ((1 : Fin 2), i) (X ((1 : Fin 2), k)) = 0
    rw [pderiv_X_of_ne (by simp [hk]), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem cc_pderiv (φ : Pt R 1 d) (b i : Fin d) :
    constantCoeff (pderiv R ((0 : Fin 1), i) (φ b)) = dLin φ b i := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp [dLin]

private theorem comp1_apply_eq_ev {n : ℕ} (φ : Pt R 1 d) (ψ : Pt R n d) (b : Fin d) :
    comp1 φ ψ b = ev (n := n) ![ψ] (φ b) := by
  rfl

private theorem ev_swap_of_constantCoeff_eq_zero (φ : Pt R 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0) (g : PS R 2 d) :
    ev (n := 1) ![pt R d 0, 0]
        (ev (n := 2) ![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] g) =
      ev (n := 1) ![φ] (ev (n := 1) ![pt R d 0, 0] g) := by
  have hx : NoConst (![pt R (n := 2) d 0] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 0)
  have hy : NoConst (![pt R (n := 2) d 1] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 1)
  have hxy : NoConst (![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] :
      Fin 2 → Pt R 2 d) :=
    noConst_two (fun b => (cc_ev hx (φ b)).trans (hφ b)) (fun b => (cc_ev hy (φ b)).trans (hφ b))
  rw [ev_ev germPointsNoConstantTerm_first_zero hxy, ev_ev (noConst_one hφ) germPointsNoConstantTerm_first_zero]
  congr 1
  funext j b
  fin_cases j
  · show ev (n := 1) ![pt R d 0, 0] (ev (n := 2) ![pt R (n := 2) d 0] (φ b)) =
      ev (n := 1) ![φ] (pt R d 0 b)
    rw [germ_ev_restrict_axis_first_point, ev_pt (noConst_one hφ)]
    rfl
  · show ev (n := 1) ![pt R d 0, 0] (ev (n := 2) ![pt R (n := 2) d 1] (φ b)) =
      ev (n := 1) ![φ] (0 : PS R 1 d)
    rw [germ_ev_restrict_axis_second_point, hφ b, map_zero, ev_zero (noConst_one hφ)]

theorem jac_endo (G : FGLaw R d) (φ : Pt R 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hom : comp1 φ (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
      G.add (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1))) (a i : Fin d) :
    ∑ c, pderiv R ((0 : Fin 1), c) (φ a) *
        ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F c)) =
      ∑ b, ev (n := 1) ![φ] (ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), b) (G.F a))) *
        C (dLin φ b i) := by
  have hF : NoConst (![G.F] : Fin 1 → Pt R 2 d) := noConst_one G.const
  have hx : NoConst (![pt R (n := 2) d 0] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 0)
  have hy : NoConst (![pt R (n := 2) d 1] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 1)
  have hxy : NoConst (![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] :
      Fin 2 → Pt R 2 d) :=
    noConst_two (fun b => (cc_ev hx (φ b)).trans (hφ b)) (fun b => (cc_ev hy (φ b)).trans (hφ b))
  have key : ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (ev (n := 2) ![G.F] (φ a))) =
      ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i)
        (ev (n := 2) ![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] (G.F a))) := by
    have h2 := congrFun hom a
    rw [add_pt] at h2
    exact congrArg (fun g => ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) g)) h2
  rw [pderiv_ev hF, pderiv_ev hxy, Fin.sum_univ_one, Fin.sum_univ_two] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, comp1_apply_eq_ev, pderiv_second_of_ev_first_point,
    dy_y, mul_zero, Finset.sum_const_zero, zero_add] at key
  simp only [ev_sum germPointsNoConstantTerm_first_zero, ev_mul germPointsNoConstantTerm_first_zero, germ_ev_restrict_axis_groupLaw, ev_swap_of_constantCoeff_eq_zero φ hφ, germ_ev_restrict_axis_second_point, cc_pderiv] at key
  exact key

private theorem dof_eq_sum_C_mul_ev (F : Fin d → PS R 2 d) (u : Fin d → R) (g : PS R 1 d) :
    Dof F u g = ∑ j, (∑ i, C (u i) * ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (F j))) *
      pderiv R ((0 : Fin 1), j) g := by
  rfl

theorem dof_comp_endo : ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (φ : Pt R 1 d),
    (∀ i, constantCoeff (φ i) = 0) →
    comp1 φ (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
      G.add (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1)) →
    ∀ (u : Fin d → R) (f : PS R 1 d),
      Dof G.F u (ev (n := 1) ![φ] f) = ev (n := 1) ![φ] (Dof G.F ((dLin φ).mulVec u) f) := by
  intro R _ d G φ hφ hom u f
  have h1 : NoConst (![φ] : Fin 1 → Pt R 1 d) := noConst_one hφ
  rw [dof_eq_sum_C_mul_ev, dof_eq_sum_C_mul_ev, ev_sum h1]
  simp only [pderiv_ev h1, Fin.sum_univ_one, Matrix.cons_val_zero, ev_mul h1, ev_sum h1, ev_C,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have step : ∀ i, ∑ x, C (u i) * ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F x)) *
      (ev (n := 1) ![φ] (pderiv R ((0 : Fin 1), c) f) * pderiv R ((0 : Fin 1), x) (φ c)) =
      C (u i) * ev (n := 1) ![φ] (pderiv R ((0 : Fin 1), c) f) *
        ∑ x, pderiv R ((0 : Fin 1), x) (φ c) *
          ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F x)) := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  conv_lhs => rw [Finset.sum_comm]
  simp only [step, jac_endo G φ hφ hom c, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.DerivEndo
