import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Semichar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnHolFamOfHolTo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj MonObj
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem hermForm_zero_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by
  unfold hermForm
  simp

theorem hermForm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  unfold hermForm
  rw [add_dotProduct]

theorem hermForm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  unfold hermForm
  rw [star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hji : star (Hm i j) = Hm j i := by
    have := congrFun (congrFun hH j) i
    rwa [Matrix.conjTranspose_apply] at this
  simp only [Pi.star_apply, star_star, hji]
  ring

theorem hermForm_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (t • z) w = t * hermForm Hm z w := by
  unfold hermForm
  rw [smul_dotProduct, smul_eq_mul]

theorem hermForm_real_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm z ((t : ℂ) • w) = t * hermForm Hm z w := by
  unfold hermForm
  have h1 : star ((t : ℂ) • w) = (t : ℂ) • star w := by
    ext i
    simp [Complex.conj_ofReal]
  rw [h1, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

def mulTy {g : ℕ} (ty : Fin g → E →+* ℂ) (a : 𝓞 E) (z : Fin g → ℂ) : Fin g → ℂ := fun i => ty i (a : E) * z i

theorem mulTy_zero {g : ℕ} (ty : Fin g → E →+* ℂ) (a : 𝓞 E) : mulTy ty a 0 = 0 := by
  funext i
  simp [mulTy]

theorem mulTy_add {g : ℕ} (ty : Fin g → E →+* ℂ) (a : 𝓞 E) (z z' : Fin g → ℂ) :
    mulTy ty a (z + z') = mulTy ty a z + mulTy ty a z' := by
  funext i
  simp [mulTy, mul_add]

theorem mulTy_smul {g : ℕ} (ty : Fin g → E →+* ℂ) (a : 𝓞 E) (t : ℂ) (z : Fin g → ℂ) :
    mulTy ty a (t • z) = t • mulTy ty a z := by
  funext i
  simp only [mulTy, Pi.smul_apply, smul_eq_mul]
  ring

theorem herm_adj {D : Datum H} {g : ℕ} {ty : Fin g → E →+* ℂ} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hIm : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) (a : 𝓞 E)
    (z w : Fin g → ℂ) : hermForm Hm (mulTy ty a z) w = hermForm Hm z (mulTy ty (H.bar a) w) := by
  obtain ⟨hsm, -, -, hspan, -⟩ := hP
  have hA : ∀ x, P (a • x) = mulTy ty a (P x) := fun x => funext fun i => by rw [hsm]; rfl
  have hB : ∀ x, P (H.bar a • x) = mulTy ty (H.bar a) (P x) := fun x => funext fun i => by rw [hsm]; rfl
  have hsr : ∀ (t : ℝ) (v : Fin g → ℂ), t • v = (t : ℂ) • v := fun t v => by
    ext i
    simp [Complex.real_smul]

  have step1 : ∀ y v, (hermForm Hm (mulTy ty a v) (P y)).im =
      (hermForm Hm v (mulTy ty (H.bar a) (P y))).im := by
    intro y
    let S : Submodule ℝ (Fin g → ℂ) :=
      { carrier := {v | (hermForm Hm (mulTy ty a v) (P y)).im =
          (hermForm Hm v (mulTy ty (H.bar a) (P y))).im}
        add_mem' := by
          intro v v' hv hv'
          simp only [Set.mem_setOf_eq] at *
          rw [mulTy_add, hermForm_add_left, hermForm_add_left, Complex.add_im, Complex.add_im, hv, hv']
        zero_mem' := by
          simp only [Set.mem_setOf_eq, mulTy_zero, hermForm_zero_left]
        smul_mem' := by
          intro t v hv
          simp only [Set.mem_setOf_eq] at *
          rw [hsr, mulTy_smul, hermForm_smul_left, hermForm_smul_left, Complex.im_ofReal_mul,
            Complex.im_ofReal_mul, hv] }
    have hle : Submodule.span ℝ (Set.range P) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      show (hermForm Hm (mulTy ty a (P x)) (P y)).im = (hermForm Hm (P x) (mulTy ty (H.bar a) (P y))).im
      rw [← hA, ← hB, hIm, hIm, D.adj]
    rw [hspan] at hle
    exact fun v => hle Submodule.mem_top
  have key : ∀ u v, (hermForm Hm (mulTy ty a u) v).im = (hermForm Hm u (mulTy ty (H.bar a) v)).im := by
    intro u
    let S : Submodule ℝ (Fin g → ℂ) :=
      { carrier := {v | (hermForm Hm (mulTy ty a u) v).im = (hermForm Hm u (mulTy ty (H.bar a) v)).im}
        add_mem' := by
          intro v v' hv hv'
          simp only [Set.mem_setOf_eq] at *
          rw [mulTy_add, hermForm_add_right, hermForm_add_right, Complex.add_im, Complex.add_im, hv, hv']
        zero_mem' := by
          simp only [Set.mem_setOf_eq, mulTy_zero]
          unfold hermForm
          simp
        smul_mem' := by
          intro t v hv
          simp only [Set.mem_setOf_eq] at *
          rw [hsr, mulTy_smul, hermForm_real_smul_right, hermForm_real_smul_right, Complex.im_ofReal_mul,
            Complex.im_ofReal_mul, hv] }
    have hle : Submodule.span ℝ (Set.range P) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      exact step1 y u
    rw [hspan] at hle
    exact fun v => hle Submodule.mem_top
  have hI : ∀ u v, (hermForm Hm u v).re = (hermForm Hm (Complex.I • u) v).im := by
    intro u v
    rw [hermForm_smul_left]
    simp
  apply Complex.ext
  · rw [hI, hI, ← mulTy_smul]
    exact key _ _
  · exact key z w

theorem chiL_add {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (Wu : UnitAt W)
    (a b : (W.F.Di (W.ik k)).La) :
    Wu.χl (W.Pm (a + b)) = Wu.χl (W.Pm a) * Wu.χl (W.Pm b) * (-1 : ℂ) ^ ((W.F.Di (W.ik k)).EF a b) := by
  obtain ⟨j, hj⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.exists_chart _ Xo.univ.t.PP.isLB
    ((W.F.ex (W.ik k) W.Pm 0).left cpt)
  have h0 : ⊤ ≤ (W.F.ex (W.ik k) W.Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := top_le_of_mem hj
  have hc : ∀ v, ⊤ ≤ (W.F.ex (W.ik k) W.Pm (W.Pm v)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
    intro v
    rw [(W.F.ex_ker _ _ W.per _).2 ⟨v, rfl⟩]
    rw [(W.F.ex_ker _ _ W.per _).2 ⟨0, map_zero _⟩] at h0
    exact h0
  have hab : W.Pm (a + b) = W.Pm a + W.Pm b := map_add _ _ _
  have E1 := ((Wu.c6 (a + b) j 0).2 h0)
  have E2 := ((Wu.c6 a j 0).2 h0)
  have E3 := ((Wu.c6 b j (W.Pm a)).2 (hc a))
  have hF := Wu.c3 j (W.Pm a + W.Pm b) (by rw [← hab]; exact hc (a + b))
  rw [hab] at E1 ⊢
  simp only [hermForm_zero_left, mul_zero, zero_add] at E1 E2
  have key : Wu.χl (W.Pm a + W.Pm b) *
      Complex.exp (Real.pi / 2 * hermForm Wu.Hm (W.Pm a + W.Pm b) (W.Pm a + W.Pm b)) =
      Wu.χl (W.Pm a) * Wu.χl (W.Pm b) * Complex.exp (Real.pi / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a) +
        (Real.pi * hermForm Wu.Hm (W.Pm a) (W.Pm b) + Real.pi / 2 * hermForm Wu.Hm (W.Pm b) (W.Pm b))) := by
    apply mul_right_cancel₀ hF
    rw [Complex.exp_add]
    calc _ = Wu.fr j 0 := E1.symm
      _ = _ := by rw [E2, E3]; ring
  have hexp : (Real.pi / 2 * hermForm Wu.Hm (W.Pm a + W.Pm b) (W.Pm a + W.Pm b) : ℂ) +
      ((W.F.Di (W.ik k)).EF a b : ℂ) * (Real.pi * Complex.I) =
      Real.pi / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a) +
        (Real.pi * hermForm Wu.Hm (W.Pm a) (W.Pm b) + Real.pi / 2 * hermForm Wu.Hm (W.Pm b) (W.Pm b)) := by
    rw [hermForm_add_left, hermForm_add_right, hermForm_add_right,
      hermForm_swap Wu.herm (W.Pm a) (W.Pm b)]
    have hc1 := Wu.c1 a b
    apply Complex.ext <;> simp [Complex.star_def, Complex.conj_re, Complex.conj_im, hc1] <;> ring
  rw [show ((-1 : ℂ)) ^ ((W.F.Di (W.ik k)).EF a b) =
      Complex.exp (((W.F.Di (W.ik k)).EF a b : ℂ) * (Real.pi * Complex.I)) by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]]
  apply mul_right_cancel₀
    (Complex.exp_ne_zero (Real.pi / 2 * hermForm Wu.Hm (W.Pm a + W.Pm b) (W.Pm a + W.Pm b)))
  rw [key, ← hexp, Complex.exp_add]
  ring

section Prim

variable {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x)

def qW (z : Fin W.g → ℂ) : Sp ℂ ⟶ Xo.univ.t.G.left := (W.F.ex (W.ik k) W.Pm z).left

def tyW' : Fin W.g → E →+* ℂ := fun j => relab c σ (W.e j).1

theorem qW_period (z : Fin W.g → ℂ) (b : (W.F.Di (W.ik k)).La) : qW W (z + W.Pm b) = qW W z := by
  unfold qW
  rw [W.F.ex_add _ _ W.per, (W.F.ex_ker _ _ W.per _).2 ⟨b, rfl⟩, _root_.mul_one]

theorem pm_smul (b : 𝓞 E) (y : (W.F.Di (W.ik k)).La) : W.Pm (b • y) = mulTy (tyW' W) b (W.Pm y) := by
  funext i
  rw [W.per.1]
  rfl

theorem isHolFam_qW : IsHolFam (qW W) := by
  have hP := W.per
  have hh := (W.F.hol (W.ik k) 0 Set.univ (fun _ => W.Pm) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  intro V f
  obtain ⟨ho, hd⟩ := hh V f
  let j : (Fin W.g → ℂ) → (Fin 0 → ℂ) × (Fin W.g → ℂ) := fun z => (0, z)
  have hjd : Differentiable ℂ j := (differentiable_const _).prodMk differentiable_id
  have hset : {z | ⊤ ≤ qW W z ⁻¹ᵁ V} =
      j ⁻¹' {bz ∈ (Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin W.g → ℂ)) |
        ⊤ ≤ (W.F.ex (W.ik k) W.Pm bz.2).left ⁻¹ᵁ V} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_self, true_and]
    exact Iff.rfl
  rw [hset]
  refine ⟨ho.preimage hjd.continuous, ?_⟩
  refine (hd.comp hjd.differentiableOn (Set.mapsTo_preimage _ _)).congr ?_
  intro z _
  rfl

def linI (I : Finset (Fin 2)) (z : Fin W.g → ℂ) : Fin W.g → ℂ :=
  (if (0 : Fin 2) ∈ I then z else 0) + (if (1 : Fin 2) ∈ I then mulTy (tyW' W) H.w0 z else 0)

def linB (I : Finset (Fin 2)) (b : (W.F.Di (W.ik k)).La) : (W.F.Di (W.ik k)).La :=
  (if (0 : Fin 2) ∈ I then b else 0) + (if (1 : Fin 2) ∈ I then H.w0 • b else 0)

theorem pm_linB (I : Finset (Fin 2)) (b : (W.F.Di (W.ik k)).La) : W.Pm (linB W I b) = linI W I (W.Pm b) := by
  unfold linB linI
  by_cases h0 : (0 : Fin 2) ∈ I <;> by_cases h1 : (1 : Fin 2) ∈ I <;>
    simp only [h0, h1, ↓reduceIte, map_add, map_zero, pm_smul]

theorem linI_add (I : Finset (Fin 2)) (z z' : Fin W.g → ℂ) : linI W I (z + z') = linI W I z + linI W I z' := by
  unfold linI
  by_cases h0 : (0 : Fin 2) ∈ I <;> by_cases h1 : (1 : Fin 2) ∈ I <;>
    simp only [h0, h1, ↓reduceIte, mulTy_add, add_zero] <;> abel

theorem mulTy_diff {g : ℕ} (ty : Fin g → E →+* ℂ) (a : 𝓞 E) : Differentiable ℂ (mulTy ty a) := by
  unfold mulTy
  exact differentiable_pi.2 fun i => (differentiable_apply i).const_mul _

theorem linI_diff (I : Finset (Fin 2)) : Differentiable ℂ (linI W I) := by
  unfold linI
  by_cases h0 : (0 : Fin 2) ∈ I <;> by_cases h1 : (1 : Fin 2) ∈ I <;>
    simp only [h0, h1, ↓reduceIte, add_zero, zero_add]
  · exact differentiable_id.add (mulTy_diff _ _)
  · exact differentiable_id
  · exact mulTy_diff _ _
  · exact differentiable_const 0

theorem ex_psum (I : Finset (Fin 2)) (z : Fin W.g → ℂ) :
    qW W z ≫ (psum Xo.univ.t.G ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0] I).left = qW W (linI W I z) := by
  have hP := W.per
  have e0 : W.F.ex (W.ik k) W.Pm 0 = 1 := (W.F.ex_ker _ _ hP 0).2 ⟨0, map_zero _⟩
  have ew : W.F.ex (W.ik k) W.Pm (mulTy (tyW' W) H.w0 z) =
      W.F.ex (W.ik k) W.Pm z ≫ Xo.univ.t.act.act H.w0 := W.F.ex_lin _ _ hP H.w0 z
  have hl : List.finRange 2 = [0, 1] := by decide
  unfold qW linI
  rw [W.F.ex_add _ _ hP, ← Over.comp_left]
  congr 1
  by_cases h0 : (0 : Fin 2) ∈ I <;> by_cases h1 : (1 : Fin 2) ∈ I <;>
    simp [psum, padd, pzero, hl, h0, h1, e0, ew]
  all_goals first
    | rfl
    | (change _ = CartesianMonoidalCategory.lift _ _ ≫ μ
       rw [CartesianMonoidalCategory.comp_lift_assoc, Category.comp_id])

abbrev phiP : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)) → (Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) :=
  Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφG Xo.univ.t ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])

abbrev epsP : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)) → ℤ := Sum.elim (fun _ => 1) fun I => -cε 2 I

def linK : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)) → (Fin W.g → ℂ) → (Fin W.g → ℂ) :=
  Sum.elim (fun _ z => z) fun I z => linI W I.down z

def linBK : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)) → (W.F.Di (W.ik k)).La → (W.F.Di (W.ik k)).La :=
  Sum.elim (fun _ b => b) fun I b => linB W I.down b

theorem qW_phiP (kk : Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) (z : Fin W.g → ℂ) :
    qW W z ≫ (phiP (Xo := Xo) (H := H)) kk = qW W (linK W kk z) := by
  rcases kk with _ | I
  · exact Category.comp_id _
  · exact ex_psum W I.down z

theorem linK_add (kk) (z z' : Fin W.g → ℂ) : linK W kk (z + z') = linK W kk z + linK W kk z' := by
  rcases kk with _ | I
  · rfl
  · exact linI_add W I.down z z'

theorem pm_linBK (kk) (b : (W.F.Di (W.ik k)).La) : W.Pm (linBK W kk b) = linK W kk (W.Pm b) := by
  rcases kk with _ | I
  · rfl
  · exact pm_linB W I.down b

theorem linK_diff (kk) : Differentiable ℂ (linK W kk) := by
  rcases kk with _ | I
  · exact differentiable_id
  · exact linI_diff W I.down

end Prim

end ReciprocityTheory.ChartRestriction.G.PullbackSections
