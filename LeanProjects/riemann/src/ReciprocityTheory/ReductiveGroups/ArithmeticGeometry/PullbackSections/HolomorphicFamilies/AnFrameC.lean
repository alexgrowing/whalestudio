import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.AnFrameC

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj

section Form

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

theorem hermForm_add_left (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  unfold hermForm
  rw [add_dotProduct]

theorem hermForm_add_right (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  unfold hermForm
  rw [star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_zero_left (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by
  unfold hermForm
  rw [zero_dotProduct]

theorem hermForm_zero_right (z : Fin g → ℂ) : hermForm Hm z 0 = 0 := by
  unfold hermForm
  rw [star_zero, Matrix.mulVec_zero, dotProduct_zero]

theorem hermForm_swap (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm dotProduct Matrix.mulVec dotProduct
  simp only [Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply i j, star_star]
  ring

def rho (z l : Fin g → ℂ) : ℝ := Real.pi * (hermForm Hm z l).re + Real.pi / 2 * (hermForm Hm l l).re

def lam2 (x y l m : Fin g → ℂ) : ℝ := rho Hm (x + y) (l + m) - rho Hm x l - rho Hm y m

theorem rho_zero : rho Hm 0 0 = 0 := by
  simp [rho, hermForm_zero_left]

theorem cube_rho (z l : Fin 3 → Fin g → ℂ) :
    ∑ I : Finset (Fin 3), ((-1 : ℝ) ^ (3 - I.card)) * rho Hm (∑ i ∈ I, z i) (∑ i ∈ I, l i) = 0 := by
  have hu : (Finset.univ : Finset (Fin 3)) = insert 0 (insert 1 (insert 2 ∅)) := by decide
  rw [← Finset.powerset_univ, hu]
  simp only [Finset.sum_powerset_insert (show (0 : Fin 3) ∉ insert 1 (insert 2 (∅ : Finset (Fin 3))) by decide),
    Finset.sum_powerset_insert (show (1 : Fin 3) ∉ insert 2 (∅ : Finset (Fin 3)) by decide),
    Finset.sum_powerset_insert (show (2 : Fin 3) ∉ (∅ : Finset (Fin 3)) by decide), Finset.powerset_empty,
    Finset.sum_singleton]
  simp [Finset.sum_insert, Finset.card_insert_of_notMem]
  simp only [rho, hermForm_add_left, hermForm_add_right, hermForm_zero_left, hermForm_zero_right,
    Complex.add_re, Complex.zero_re]
  norm_num
  ring

theorem prim_rho (A Ab : (Fin g → ℂ) → (Fin g → ℂ)) (hA : ∀ z w, hermForm Hm (A z) w = hermForm Hm z (Ab w))
    (hs : ∀ z, A z + Ab z = z) (z l : Fin g → ℂ) :
    lam2 Hm z (A z) l (A l) = rho Hm z l := by
  have e1 : hermForm Hm z (A l) + hermForm Hm z (Ab l) = hermForm Hm z l := by
    rw [← hermForm_add_right, hs]
  have e2 : hermForm Hm l (A l) + hermForm Hm l (Ab l) = hermForm Hm l l := by
    rw [← hermForm_add_right, hs]
  have r1 := congrArg Complex.re e1
  have r2 := congrArg Complex.re e2
  simp only [Complex.add_re] at r1 r2
  simp only [lam2, rho, hermForm_add_left, hermForm_add_right, hA, Complex.add_re]
  linear_combination Real.pi * r1 + Real.pi / 2 * r2

theorem ad_rho (A Ab : (Fin g → ℂ) → (Fin g → ℂ)) (hA : ∀ z w, hermForm Hm (A z) w = hermForm Hm z (Ab w))
    (hAb : ∀ z w, hermForm Hm (Ab z) w = hermForm Hm z (A w)) (x z l m : Fin g → ℂ) :
    lam2 Hm (A x) z (A l) m = lam2 Hm x (Ab z) l (Ab m) := by
  simp only [lam2, rho, hermForm_add_left, hermForm_add_right, Complex.add_re, hA, hAb]
  ring

theorem adj_symm (hH : Hm.IsHermitian) (A Ab : (Fin g → ℂ) → (Fin g → ℂ))
    (hA : ∀ z w, hermForm Hm (A z) w = hermForm Hm z (Ab w)) (z w : Fin g → ℂ) :
    hermForm Hm (Ab z) w = hermForm Hm z (A w) := by
  rw [hermForm_swap Hm hH, ← hA, ← hermForm_swap Hm hH]

end Form

section Compat

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

theorem hermForm_smul_left (c : ℂ) (z w : Fin g → ℂ) : hermForm Hm (c • z) w = c * hermForm Hm z w := by
  unfold hermForm
  rw [smul_dotProduct, smul_eq_mul]

theorem hermForm_smul_right (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z (c • w) = star c * hermForm Hm z w := by
  unfold hermForm
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem real_smul_eq (r : ℝ) (z : Fin g → ℂ) : r • z = (r : ℂ) • z := by
  funext i
  simp [Complex.real_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def tyAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (z : Fin g → ℂ) : Fin g → ℂ := fun i => ty i (a : E) * z i

theorem tyAct_add (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (u v : Fin g → ℂ) :
    tyAct ty a (u + v) = tyAct ty a u + tyAct ty a v := by
  funext i
  simp only [tyAct, Pi.add_apply, mul_add]

theorem tyAct_smul (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (c : ℂ) (u : Fin g → ℂ) :
    tyAct ty a (c • u) = c • tyAct ty a u := by
  funext i
  simp only [tyAct, Pi.smul_apply, smul_eq_mul]
  ring

theorem tyAct_zero (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : tyAct ty a 0 = 0 := by
  funext i
  simp [tyAct]

variable {H : Host E} (D : Datum H) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ))

theorem im_hermForm_act (hP : IsPeriod D ty P) (hc1 : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (a : 𝓞 E) (u v : Fin g → ℂ) :
    (hermForm Hm (tyAct ty a u) v).im = (hermForm Hm u (tyAct ty (H.bar a) v)).im := by
  have hTP : ∀ (b : 𝓞 E) x, tyAct ty b (P x) = P (b • x) := fun b x => funext fun i => (hP.1 b x i).symm
  have hspan : ∀ w : Fin g → ℂ, w ∈ Submodule.span ℝ (Set.range P) := fun w => by
    rw [hP.2.2.2.1]; trivial
  have base : ∀ x y, (hermForm Hm (tyAct ty a (P x)) (P y)).im =
      (hermForm Hm (P x) (tyAct ty (H.bar a) (P y))).im := by
    intro x y
    rw [hTP, hTP, hc1, hc1, D.adj]
  have step1 : ∀ x (w : Fin g → ℂ), (hermForm Hm (tyAct ty a (P x)) w).im =
      (hermForm Hm (P x) (tyAct ty (H.bar a) w)).im := by
    intro x w
    induction hspan w using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, rfl⟩ := hw
      exact base x y
    | zero => simp [tyAct_zero, hermForm_zero_right]
    | add w w' _ _ h1 h2 =>
      rw [hermForm_add_right, tyAct_add, hermForm_add_right, Complex.add_im, Complex.add_im, h1, h2]
    | smul r w _ h =>
      rw [real_smul_eq, hermForm_smul_right, tyAct_smul, hermForm_smul_right, Complex.mul_im, Complex.mul_im, h]
      simp
  induction hspan u using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, rfl⟩ := hu
    exact step1 x v
  | zero => simp [tyAct_zero, hermForm_zero_left]
  | add u u' _ _ h1 h2 =>
    rw [tyAct_add, hermForm_add_left, hermForm_add_left, Complex.add_im, Complex.add_im, h1, h2]
  | smul r u _ h =>
    rw [real_smul_eq, tyAct_smul, hermForm_smul_left, hermForm_smul_left, Complex.mul_im, Complex.mul_im, h]
    simp

theorem hermForm_act (hP : IsPeriod D ty P) (hc1 : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (a : 𝓞 E) (u v : Fin g → ℂ) :
    hermForm Hm (tyAct ty a u) v = hermForm Hm u (tyAct ty (H.bar a) v) := by
  apply Complex.ext
  · have h := im_hermForm_act Hm D ty P hP hc1 a (Complex.I • u) v
    rw [tyAct_smul, hermForm_smul_left, hermForm_smul_left, Complex.mul_im, Complex.mul_im] at h
    simpa using h
  · exact im_hermForm_act Hm D ty P hP hc1 a u v

end Compat

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem norm_fr_add {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} {W : UnfAt U k x} (Wu : UnitAt W)
    (a : _) (j : Xo.univ.t.PP.L.ι) (z : Fin W.g → ℂ)
    (h : ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j) :
    ‖Wu.fr j (z + W.Pm a)‖ = ‖Wu.fr j z‖ * Real.exp (-rho Wu.Hm z (W.Pm a)) := by
  obtain ⟨h1, h2⟩ := Wu.c6 a j z
  have hre : ((Real.pi : ℂ) * hermForm Wu.Hm z (W.Pm a) +
      (Real.pi : ℂ) / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a)).re = rho Wu.Hm z (W.Pm a) := by
    simp only [rho, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im, zero_mul, sub_zero, zero_div]
  rw [h2 h, norm_mul, norm_mul, h1, one_mul, Complex.norm_exp, hre, mul_comm, ← mul_assoc, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, one_mul]

abbrev tyW {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) : Fin W.g → (E →+* ℂ) :=
  fun j => relab c σ (W.e j).1

theorem unit_hermForm_act {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} {W : UnfAt U k x} (Wu : UnitAt W)
    (a : 𝓞 E) (z w : Fin W.g → ℂ) :
    hermForm Wu.Hm (tyAct (tyW W) a z) w = hermForm Wu.Hm z (tyAct (tyW W) (H.bar a) w) :=
  hermForm_act Wu.Hm (W.F.Di (W.ik k)) (tyW W) W.Pm W.per Wu.c1 a z w

theorem unit_prim_rho {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} {W : UnfAt U k x} (Wu : UnitAt W)
    (z l : Fin W.g → ℂ) :
    lam2 Wu.Hm z (tyAct (tyW W) H.w0 z) l (tyAct (tyW W) H.w0 l) = rho Wu.Hm z l := by
  refine prim_rho Wu.Hm _ (tyAct (tyW W) (H.bar H.w0)) (unit_hermForm_act Wu H.w0) (fun z => ?_) z l
  funext i
  simp only [tyAct, Pi.add_apply, ← add_mul]
  have h := congrArg (fun t : 𝓞 E => tyW W i (t : E)) (CVA.cmHostUnit_add_conj_eq_one H)
  push_cast at h
  simp only [map_add, map_one] at h
  rw [h, one_mul]

theorem unit_ad_rho {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} {W : UnfAt U k x} (Wu : UnitAt W)
    (a : 𝓞 E) (y z l m : Fin W.g → ℂ) :
    lam2 Wu.Hm (tyAct (tyW W) a y) z (tyAct (tyW W) a l) m =
      lam2 Wu.Hm y (tyAct (tyW W) (H.bar a) z) l (tyAct (tyW W) (H.bar a) m) :=
  ad_rho Wu.Hm _ _ (unit_hermForm_act Wu a)
    (adj_symm Wu.Hm Wu.herm _ _ (unit_hermForm_act Wu a)) y z l m

end Frame

end ReciprocityTheory.ChartRestriction.G.PullbackSections.AnFrameC
