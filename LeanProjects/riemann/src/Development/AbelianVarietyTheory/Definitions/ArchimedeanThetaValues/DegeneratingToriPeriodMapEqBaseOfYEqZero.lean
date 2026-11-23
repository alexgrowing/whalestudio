import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)

structure AnArc (O : Type) [CommRing O] [StarRing O] where

  gB : ℕ

  abelian₂ : Submodule ℤ (Fin gB → ℂ)

  discrete : DiscreteTopology abelian₂

  full : Submodule.span ℝ (abelian₂ : Set (Fin gB → ℂ)) = ⊤

  Hm : Matrix (Fin gB) (Fin gB) ℂ

  Hm_herm : Hm.IsHermitian

  Hm_pos : ∀ z : Fin gB → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re

  Ef : LinearMap.BilinForm ℤ abelian₂

  Ef_eq : ∀ l m : abelian₂, (Ef l m : ℝ) = (hermForm Hm l m).im

  Ef_bij : Function.Bijective Ef

  chi : abelian₂ → ℂ

  chi_norm : ∀ l, ‖chi l‖ = 1

  chi_add : ∀ l m : abelian₂,
    chi (l + m) = chi l * chi m * Complex.exp (Real.pi * Complex.I * ((hermForm Hm l m).im : ℂ))

  chi_neg : ∀ l, chi (-l) = chi l

  F : O →+* Module.End ℂ (Fin gB → ℂ)

  F_mem : ∀ a, ∀ l ∈ abelian₂, F a l ∈ abelian₂

  F_adj : ∀ a z w, hermForm Hm (F a z) w = hermForm Hm z (F (star a) w)

  X : Type
  [acg : AddCommGroup X]
  [free : Module.Free ℤ X]
  [fin : Module.Finite ℤ X]
  [mod : Module O X]

  ct : X →+ (Fin gB → ℂ)

  ct_smul : ∀ (a : O) x, ct (a • x) = F a (ct x)

  T : X →+ X →+ ℂ

  T_symm : ∀ x y, T x y = T y x

  T_adj : ∀ (a : O) y x, T (a • y) x = T y (star a • x)

  psi : X → ℂˣ

  psi_neg : ∀ x, psi (-x) = psi x

  psi_add : ∀ x y, (psi (x + y) : ℂ) = psi x * psi y * eTwoPi (T x y)

  be : LinearMap.BilinForm ℤ X

  be_symm : ∀ x y, be x y = be y x

  be_pos : ∀ x, x ≠ 0 → 0 < be x x

  be_adj : ∀ (a : O) y x, be (a • y) x = be y (star a • x)

  be_even : ∀ x, (2 : ℤ) ∣ be x x

attribute [instance] AnArc.acg AnArc.free AnArc.fin AnArc.mod AnArc.discrete

namespace AnArc

theorem e_add (x y : ℂ) : eTwoPi (x + y) = eTwoPi x * eTwoPi y := by
  simp only [eTwoPi, mul_add, Complex.exp_add]

@[simp] theorem e_zero : eTwoPi 0 = 1 := by simp [eTwoPi]

theorem e_ne_zero (x : ℂ) : eTwoPi x ≠ 0 := Complex.exp_ne_zero _

@[simp] theorem e_intCast (n : ℤ) : eTwoPi n = 1 := by
  rw [eTwoPi, mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I n

theorem e_nat_mul (n : ℕ) (x : ℂ) : eTwoPi (n * x) = eTwoPi x ^ n := by
  rw [eTwoPi, eTwoPi, ← Complex.exp_nat_mul]; congr 1; ring

theorem e_mul_intCast (x : ℂ) (n : ℤ) : eTwoPi (x * n) = eTwoPi x ^ n := by
  rw [eTwoPi, eTwoPi, ← Complex.exp_int_mul]; congr 1; ring

theorem e_neg_div (x : ℂ) : eTwoPi (-(x / (2 * Complex.I))) = Complex.exp (-(Real.pi * x)) := by
  rw [eTwoPi]; congr 1
  have := Complex.I_ne_zero
  field_simp

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

def H (z w : Fin A.gB → ℂ) : ℂ := hermForm A.Hm z w

theorem H_def (z w : Fin A.gB → ℂ) : A.H z w = hermForm A.Hm z w := rfl

theorem H_add_left (z z' w : Fin A.gB → ℂ) : A.H (z + z') w = A.H z w + A.H z' w := by
  simp [H, hermForm, add_dotProduct]

theorem H_add_right (z w w' : Fin A.gB → ℂ) : A.H z (w + w') = A.H z w + A.H z w' := by
  simp [H, hermForm, Matrix.mulVec_add, dotProduct_add]

theorem H_smul_left (c : ℂ) (z w : Fin A.gB → ℂ) : A.H (c • z) w = c * A.H z w := by
  simp [H, hermForm, smul_dotProduct]

theorem H_smul_right (c : ℂ) (z w : Fin A.gB → ℂ) : A.H z (c • w) = starRingEnd ℂ c * A.H z w := by
  simp [H, hermForm, Matrix.mulVec_smul, dotProduct_smul]

@[simp] theorem H_zero_left (w : Fin A.gB → ℂ) : A.H 0 w = 0 := by simp [H, hermForm]

@[simp] theorem H_zero_right (z : Fin A.gB → ℂ) : A.H z 0 = 0 := by simp [H, hermForm]

theorem H_neg_left (z w : Fin A.gB → ℂ) : A.H (-z) w = -A.H z w := by simp [H, hermForm]

theorem H_neg_right (z w : Fin A.gB → ℂ) : A.H z (-w) = -A.H z w := by
  simp [H, hermForm, Matrix.mulVec_neg]

theorem H_conj (z w : Fin A.gB → ℂ) : starRingEnd ℂ (A.H z w) = A.H w z := by
  have h : ∀ i k, starRingEnd ℂ (A.Hm i k) = A.Hm k i := fun i k => A.Hm_herm.apply k i
  simp only [H, hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, h, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem H_self_im (z : Fin A.gB → ℂ) : (A.H z z).im = 0 := by
  have := congrArg Complex.im (A.H_conj z z)
  rw [Complex.conj_im] at this
  linarith

theorem H_pos {z : Fin A.gB → ℂ} (hz : z ≠ 0) : 0 < (A.H z z).re := A.Hm_pos z hz

theorem H_F (a : O) (z w : Fin A.gB → ℂ) : A.H (A.F a z) w = A.H z (A.F (star a) w) := A.F_adj a z w

theorem Ef_eq_im (l m : A.abelian₂) : (A.Ef l m : ℝ) = (A.H l m).im := A.Ef_eq l m

@[simp] theorem Ef_self (l : A.abelian₂) : A.Ef l l = 0 := by
  have := A.Ef_eq_im l l
  rw [H_self_im] at this
  exact_mod_cast this

@[simp] theorem chi_zero : A.chi 0 = 1 := by
  have h := A.chi_add 0 0
  have h0 : A.chi 0 ≠ 0 := by
    intro h0
    have := A.chi_norm 0
    simp [h0] at this
  have hz : hermForm A.Hm ((0 : A.abelian₂) : Fin A.gB → ℂ) (0 : A.abelian₂) = 0 := A.H_zero_left _
  rw [add_zero, hz] at h
  simp only [Complex.zero_im, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
  exact (mul_eq_left₀ h0).1 h.symm

@[simp] theorem psi_zero : A.psi 0 = 1 := by
  have h := A.psi_add 0 0
  simp only [add_zero, map_zero, e_zero, mul_one] at h
  exact Units.ext ((mul_eq_left₀ (A.psi 0).ne_zero).1 h.symm)

def FLam (a : O) (l : A.abelian₂) : A.abelian₂ := ⟨A.F a l, A.F_mem a l l.2⟩

@[simp] theorem coe_FLam (a : O) (l : A.abelian₂) : (A.FLam a l : Fin A.gB → ℂ) = A.F a l := rfl

theorem Ef_FLam (a : O) (l m : A.abelian₂) : A.Ef (A.FLam a l) m = A.Ef l (A.FLam (star a) m) := by
  have h : (A.Ef (A.FLam a l) m : ℝ) = A.Ef l (A.FLam (star a) m) := by
    rw [Ef_eq_im, Ef_eq_im, coe_FLam, coe_FLam, H_F]
  exact_mod_cast h

def coord : (A.X →+ ℂ) ≃ₗ[ℂ] (Module.Free.ChooseBasisIndex ℤ A.X → ℂ) where
  toFun l i := l (Module.Free.chooseBasis ℤ A.X i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ((Module.Free.chooseBasis ℤ A.X).constr ℤ f).toAddMonoidHom
  left_inv l := by
    have : (Module.Free.chooseBasis ℤ A.X).constr ℤ (fun i => l (Module.Free.chooseBasis ℤ A.X i)) =
        l.toIntLinearMap := (Module.Free.chooseBasis ℤ A.X).ext fun i => by simp
    ext x
    simp [this]
  right_inv f := by
    funext i
    simp

theorem coord_apply (l : A.X →+ ℂ) (i) : A.coord l i = l (Module.Free.chooseBasis ℤ A.X i) := rfl

instance : NormedAddCommGroup (A.X →+ ℂ) :=
  NormedAddCommGroup.induced _ _ A.coord.toLinearMap A.coord.injective

instance : NormedSpace ℂ (A.X →+ ℂ) := NormedSpace.induced ℂ _ _ A.coord.toLinearMap

instance : NormedSpace ℝ (A.X →+ ℂ) where
  norm_smul_le r l := norm_smul_le r (A.coord l)

instance : FiniteDimensional ℂ (A.X →+ ℂ) := A.coord.symm.finiteDimensional

instance : FiniteDimensional ℝ (A.X →+ ℂ) := Module.Finite.trans ℂ _

instance : CompleteSpace (A.X →+ ℂ) := FiniteDimensional.complete ℂ _

theorem norm_eq_coord (l : A.X →+ ℂ) : ‖l‖ = ‖A.coord l‖ := rfl

theorem finrank_hom : Module.finrank ℂ (A.X →+ ℂ) = Module.finrank ℤ A.X := by
  rw [A.coord.finrank_eq, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_chooseBasisIndex]

def evalCLM (x : A.X) : (A.X →+ ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun l => l x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[simp] theorem evalCLM_apply (x : A.X) (l : A.X →+ ℂ) : A.evalCLM x l = l x := rfl

abbrev V : Type := (A.X →+ ℂ) × (Fin A.gB → ℂ)

theorem finrank_V : Module.finrank ℂ A.V = Module.finrank ℤ A.X + A.gB := by
  rw [Module.finrank_prod, finrank_hom, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

def actV : O →+* Module.End ℂ A.V where
  toFun a :=
    { toFun := fun v => (v.1.comp (DistribSMul.toAddMonoidHom A.X (star a)), A.F a v.2)
      map_add' := fun v v' => by ext <;> simp
      map_smul' := fun c v => by ext <;> simp }
  map_one' := by ext <;> simp
  map_mul' a b := by
    refine LinearMap.ext fun v => Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · show v.1 (star (a * b) • x) = v.1 (star b • star a • x)
      rw [star_mul, mul_smul]
    · simp
  map_zero' := by ext <;> simp
  map_add' a b := by
    refine LinearMap.ext fun v => Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · simp [add_smul]
    · simp

@[simp] theorem actV_fst_apply (a : O) (v : A.V) (x : A.X) : (A.actV a v).1 x = v.1 (star a • x) := rfl

@[simp] theorem actV_snd (a : O) (v : A.V) : (A.actV a v).2 = A.F a v.2 := rfl

abbrev moduleV : Module O A.V := Module.compHom A.V A.actV

def La : Type := A.X × (A.X →+ ℤ) × A.abelian₂

instance : AddCommGroup A.La := inferInstanceAs (AddCommGroup (A.X × (A.X →+ ℤ) × A.abelian₂))

namespace La

variable {A}

def mk (y : A.X) (n : A.X →+ ℤ) (l : A.abelian₂) : A.La := (y, n, l)

def y (v : A.La) : A.X := Prod.fst v

def n (v : A.La) : A.X →+ ℤ := (Prod.snd v).1

def l (v : A.La) : A.abelian₂ := (Prod.snd v).2

@[simp] theorem mk_y (y : A.X) (n : A.X →+ ℤ) (l : A.abelian₂) : (mk y n l).y = y := rfl

@[simp] theorem mk_n (y : A.X) (n : A.X →+ ℤ) (l : A.abelian₂) : (mk y n l).n = n := rfl

@[simp] theorem mk_l (y : A.X) (n : A.X →+ ℤ) (l : A.abelian₂) : (mk y n l).l = l := rfl

@[simp] theorem mk_eta (v : A.La) : mk v.y v.n v.l = v := rfl

@[ext] theorem ext {v v' : A.La} (hy : v.y = v'.y) (hn : v.n = v'.n) (hl : v.l = v'.l) : v = v' :=
  Prod.ext hy (Prod.ext hn hl)

@[simp] theorem zero_y : (0 : A.La).y = 0 := rfl

@[simp] theorem zero_n : (0 : A.La).n = 0 := rfl

@[simp] theorem zero_l : (0 : A.La).l = 0 := rfl

@[simp] theorem add_y (v v' : A.La) : (v + v').y = v.y + v'.y := rfl

@[simp] theorem add_n (v v' : A.La) : (v + v').n = v.n + v'.n := rfl

@[simp] theorem add_l (v v' : A.La) : (v + v').l = v.l + v'.l := rfl

@[simp] theorem neg_y (v : A.La) : (-v).y = -v.y := rfl

@[simp] theorem neg_n (v : A.La) : (-v).n = -v.n := rfl

@[simp] theorem neg_l (v : A.La) : (-v).l = -v.l := rfl

@[simp] theorem sub_y (v v' : A.La) : (v - v').y = v.y - v'.y := rfl

@[simp] theorem sub_n (v v' : A.La) : (v - v').n = v.n - v'.n := rfl

@[simp] theorem sub_l (v v' : A.La) : (v - v').l = v.l - v'.l := rfl

@[simp] theorem zsmul_y (k : ℤ) (v : A.La) : (k • v).y = k • v.y := rfl

@[simp] theorem zsmul_n (k : ℤ) (v : A.La) : (k • v).n = k • v.n := rfl

@[simp] theorem zsmul_l (k : ℤ) (v : A.La) : (k • v).l = k • v.l := rfl

@[simp] theorem nsmul_y (k : ℕ) (v : A.La) : (k • v).y = k • v.y := rfl

@[simp] theorem nsmul_n (k : ℕ) (v : A.La) : (k • v).n = k • v.n := rfl

@[simp] theorem nsmul_l (k : ℕ) (v : A.La) : (k • v).l = k • v.l := rfl

theorem eq_add_parts (v : A.La) : v = mk v.y 0 0 + mk 0 v.n 0 + mk 0 0 v.l := by ext <;> simp

end La

def laEquiv : A.La ≃ₗ[ℤ] A.X × (A.X →+ ℤ) × A.abelian₂ where
  toFun v := (v.y, v.n, v.l)
  invFun p := La.mk p.1 p.2.1 p.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

instance : IsZLattice ℝ A.abelian₂ := ⟨A.full⟩

instance : Module.Finite ℤ A.abelian₂ := ZLattice.module_finite ℝ A.abelian₂

instance : Module.Free ℤ A.abelian₂ := ZLattice.module_free ℝ A.abelian₂

instance : Module.Finite ℤ A.La := Module.Finite.equiv A.laEquiv.symm

instance : Module.Free ℤ A.La := Module.Free.of_equiv A.laEquiv.symm

instance (priority := low) : SMul O A.La where
  smul a v := La.mk (a • v.y) (v.n.comp (DistribSMul.toAddMonoidHom A.X (star a))) (A.FLam a v.l)

namespace La

variable {A}

@[simp] theorem smul_y (a : O) (v : A.La) : (a • v).y = a • v.y := rfl

@[simp] theorem smul_n_apply (a : O) (v : A.La) (x : A.X) : (a • v).n x = v.n (star a • x) := rfl

@[simp] theorem smul_l (a : O) (v : A.La) : (a • v).l = A.FLam a v.l := rfl

end La

instance (priority := low) : Module O A.La where
  one_smul v := by ext <;> simp
  mul_smul a b v := by
    refine La.ext (by simp [mul_smul]) (AddMonoidHom.ext fun x => ?_) (Subtype.ext (by simp))
    simp only [La.smul_n_apply]
    rw [star_mul, mul_smul]
  smul_zero a := by ext <;> simp
  smul_add a v v' := by ext <;> simp
  add_smul a b v := by ext <;> simp [add_smul]
  zero_smul v := by ext <;> simp

def yLin : A.La →ₗ[O] A.X where
  toFun := La.y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem yLin_apply (v : A.La) : A.yLin v = v.y := rfl

theorem yLin_surjective : Function.Surjective A.yLin := fun y => ⟨La.mk y 0 0, rfl⟩

def P0 : A.La →+ A.V where
  toFun v :=
    ({ toFun := fun x => A.T v.y x + v.n x - A.H (A.ct x) v.l / (2 * Complex.I)
       map_zero' := by simp
       map_add' := fun x x' => by simp only [map_add, H_add_left]; push_cast; ring },
      A.ct v.y + v.l)
  map_zero' := by ext <;> simp
  map_add' v v' := by
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · simp only [La.add_y, La.add_n, La.add_l, map_add, AddMonoidHom.add_apply, Submodule.coe_add, H_add_right,
        Prod.fst_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      push_cast; ring
    · simp only [La.add_y, La.add_l, map_add, Submodule.coe_add, Prod.snd_add]
      abel

@[simp] theorem degeneratingTori_basePeriodMap_fst_apply (v : A.La) (x : A.X) :
    (A.P0 v).1 x = A.T v.y x + v.n x - A.H (A.ct x) v.l / (2 * Complex.I) := rfl

@[simp] theorem degeneratingTori_basePeriodMap_snd (v : A.La) : (A.P0 v).2 = A.ct v.y + v.l := rfl

def N : A.La →+ A.V where
  toFun v := ((Int.castAddHom ℂ).comp (A.be v.y).toAddMonoidHom, 0)
  map_zero' := by ext <;> simp
  map_add' v v' := by ext <;> simp

@[simp] theorem N_fst_apply (v : A.La) (x : A.X) : (A.N v).1 x = A.be v.y x := rfl

@[simp] theorem N_snd (v : A.La) : (A.N v).2 = 0 := rfl

def Pw (w : ℂ) : A.La →+ A.V := A.P0 + w • A.N

theorem Pw_apply (w : ℂ) (v : A.La) : A.Pw w v = A.P0 v + w • A.N v := rfl

@[simp] theorem Pw_fst_apply (w : ℂ) (v : A.La) (x : A.X) :
    (A.Pw w v).1 x = A.T v.y x + v.n x - A.H (A.ct x) v.l / (2 * Complex.I) + w * A.be v.y x := rfl

@[simp] theorem Pw_snd (w : ℂ) (v : A.La) : (A.Pw w v).2 = A.ct v.y + v.l := by
  simp [Pw_apply]

theorem degeneratingTori_periodMap_eq_base_of_y_eq_zero (w : ℂ) {v : A.La} (hv : v.y = 0) : A.Pw w v = A.P0 v := by
  ext <;> simp [hv]

theorem degeneratingTori_basePeriodMap_smul (a : O) (v : A.La) : A.P0 (a • v) = A.actV a (A.P0 v) := by
  refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
  · simp [A.T_adj, A.ct_smul, H_F]
  · simp [A.ct_smul]

theorem N_smul (a : O) (v : A.La) : A.N (a • v) = A.actV a (A.N v) := by
  refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
  · simp [A.be_adj]
  · simp

theorem Pw_smul (w : ℂ) (a : O) (v : A.La) : A.Pw w (a • v) = A.actV a (A.Pw w v) := by
  rw [Pw_apply, Pw_apply, degeneratingTori_basePeriodMap_smul, N_smul, map_add, map_smul]

def nn : A.La →ₗ[O] A.La where
  toFun v := La.mk 0 (A.be v.y).toAddMonoidHom 0
  map_add' v v' := by ext <;> simp
  map_smul' a v := by ext <;> simp [A.be_adj]

theorem nn_apply (v : A.La) : A.nn v = La.mk 0 (A.be v.y).toAddMonoidHom 0 := rfl

theorem nn_nn (v : A.La) : A.nn (A.nn v) = 0 := by ext <;> simp [nn_apply]

theorem degeneratingTori_basePeriodMap_nilpotentMap (v : A.La) : A.P0 (A.nn v) = A.N v := by ext <;> simp [nn_apply]

def EF : LinearMap.BilinForm ℤ A.La :=
  LinearMap.mk₂ ℤ (fun v v' => v'.n v.y - v.n v'.y + A.Ef v.l v'.l)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring)

theorem EF_apply (v v' : A.La) : A.EF v v' = v'.n v.y - v.n v'.y + A.Ef v.l v'.l := rfl

theorem EF_n_y (n : A.X →+ ℤ) (y : A.X) : A.EF (La.mk 0 n 0) (La.mk y 0 0) = -n y := by
  simp [EF_apply]

theorem EF_n_left (n : A.X →+ ℤ) (v : A.La) : A.EF (La.mk 0 n 0) v = -n v.y := by
  simp [EF_apply]

theorem EF_l_l (l m : A.abelian₂) : (A.EF (La.mk 0 0 l) (La.mk 0 0 m) : ℝ) = (A.H l m).im := by
  simp [EF_apply, Ef_eq_im]

theorem EF_isAlt : A.EF.IsAlt := fun v => by
  show A.EF v v = 0
  simp [EF_apply]

theorem EF_smul (a : O) (v v' : A.La) : A.EF (a • v) v' = A.EF v (star a • v') := by
  simp [EF_apply, Ef_FLam]

def ah (l : A.abelian₂) (z : Fin A.gB → ℂ) : ℂ :=
  A.chi l * Complex.exp (Real.pi * A.H z l + Real.pi / 2 * A.H l l)

theorem ah_ne_zero (l : A.abelian₂) (z : Fin A.gB → ℂ) : A.ah l z ≠ 0 := by
  refine mul_ne_zero (fun h => ?_) (Complex.exp_ne_zero _)
  have := A.chi_norm l
  simp [h] at this

theorem ah_add (l : A.abelian₂) (z c : Fin A.gB → ℂ) :
    A.ah l (z + c) = A.ah l z * Complex.exp (Real.pi * A.H c l) := by
  rw [ah, ah, H_add_left, mul_assoc (A.chi l), ← Complex.exp_add]
  congr 2; ring

def Theta (j : ℕ) (α : A.X) : Submodule ℂ ((Fin A.gB → ℂ) → ℂ) where
  carrier := {th | Differentiable ℂ th ∧ ∀ (l : A.abelian₂) z,
    th (z + l) = A.ah l z ^ j * Complex.exp (Real.pi * A.H (A.ct α) l) * th z}
  zero_mem' := ⟨differentiable_const 0, fun _ _ => by simp⟩
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun l z => by
    simp only [Pi.add_apply, ha.2 l z, hb.2 l z]; ring⟩
  smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun l z => by
    simp only [Pi.smul_apply, smul_eq_mul, ha.2 l z]; ring⟩

theorem mem_Theta {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} : th ∈ A.Theta j α ↔
    Differentiable ℂ th ∧ ∀ (l : A.abelian₂) z, th (z + l) =
      (A.chi l * Complex.exp (Real.pi * A.H z l + Real.pi / 2 * A.H l l)) ^ j *
        Complex.exp (Real.pi * A.H (A.ct α) l) * th z := Iff.rfl

theorem mul_mem_Theta {j j' : ℕ} {α α' : A.X} {th th' : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α)
    (h' : th' ∈ A.Theta j' α') : th * th' ∈ A.Theta (j + j') (α + α') :=
  ⟨h.1.mul h'.1, fun l z => by
    simp only [Pi.mul_apply, h.2 l z, h'.2 l z, map_add, H_add_left, mul_add, Complex.exp_add]; ring⟩

theorem translate_mem_Theta {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (μ : A.X) :
    (fun z => th (z + A.ct μ)) ∈ A.Theta j (α + j • μ) :=
  ⟨h.1.comp (differentiable_id.add_const _), fun l z => by
    have h1 : A.H (A.ct (α + j • μ)) l = A.H (A.ct α) l + j * A.H (A.ct μ) l := by
      rw [map_add, map_nsmul, H_add_left, ← Nat.cast_smul_eq_nsmul ℂ, H_smul_left]
    show th (z + l + A.ct μ) = _ * _ * th (z + A.ct μ)
    rw [add_right_comm, h.2, ah_add, h1, mul_pow, ← Complex.exp_nat_mul, mul_add, Complex.exp_add,
      mul_left_comm (Real.pi : ℂ) (j : ℂ)]
    ring⟩

def term (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ : A.X) (v : A.V) : ℂ :=
  (A.psi μ : ℂ) ^ j * eTwoPi (A.T μ α) * eTwoPi (v.1 (α + j • μ)) * th (v.2 + A.ct μ)

theorem differentiable_term (j : ℕ) (α : A.X) {th : (Fin A.gB → ℂ) → ℂ} (h : Differentiable ℂ th) (μ : A.X) :
    Differentiable ℂ (A.term j α th μ) := by
  have h1 : Differentiable ℂ fun v : A.V => v.1 (α + j • μ) :=
    (A.evalCLM (α + j • μ)).differentiable.comp differentiable_fst
  unfold term eTwoPi
  fun_prop

def q (μ : A.X) : ℤ := A.be μ μ / 2

theorem two_mul_q (μ : A.X) : 2 * A.q μ = A.be μ μ := Int.mul_ediv_cancel' (A.be_even μ)

@[simp] theorem q_zero : A.q 0 = 0 := by simp [q]

@[simp] theorem q_neg (μ : A.X) : A.q (-μ) = A.q μ := by simp [q]

theorem q_add (μ ν : A.X) : A.q (μ + ν) = A.q μ + A.q ν + A.be μ ν := by
  have h1 := A.two_mul_q (μ + ν)
  have h2 := A.two_mul_q μ
  have h3 := A.two_mul_q ν
  simp only [map_add, LinearMap.add_apply, A.be_symm ν μ] at h1
  omega

theorem be_self_nonneg (μ : A.X) : 0 ≤ A.be μ μ := by
  by_cases h : μ = 0
  · simp [h]
  · exact (A.be_pos μ h).le

def exponent (j : ℕ) (α μ : A.X) : ℤ := j * A.q μ + A.be μ α

theorem two_mul_exponent (j : ℕ) (α μ : A.X) :
    2 * A.exponent j α μ = j * A.be μ μ + 2 * A.be μ α := by
  rw [exponent, ← two_mul_q]; ring

def Sum (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (w : ℂ) (v : A.V) : ℂ :=
  ∑' μ : A.X, A.term j α th μ v * eTwoPi (w * A.exponent j α μ)

theorem finite_be_le (R : ℤ) : {μ : A.X | A.be μ μ ≤ R}.Finite := by
  classical
  let b := Module.Free.chooseBasis ℤ A.X
  let f : A.X → (Module.Free.ChooseBasisIndex ℤ A.X → ℤ) := fun μ i => A.be μ (b i)
  have hf : Function.Injective f := by
    intro μ ν h
    have h0 : A.be (μ - ν) = 0 := b.ext fun i => by
      have := congrFun h i
      simp only [f] at this
      simp [this]
    by_contra hne
    have := A.be_pos _ (sub_ne_zero.2 hne)
    rw [h0] at this
    simp at this
  refine Set.Finite.of_finite_image ?_ hf.injOn
  refine (Set.finite_Icc (fun i => -(R + A.be (b i) (b i))) (fun i => R + A.be (b i) (b i))).subset ?_
  rintro _ ⟨μ, hμ, rfl⟩
  have hμ' : A.be μ μ ≤ R := hμ
  have h0 := A.be_self_nonneg μ
  have key : ∀ i, -(R + A.be (b i) (b i)) ≤ A.be μ (b i) ∧ A.be μ (b i) ≤ R + A.be (b i) (b i) := fun i => by
    have h1 := A.be_self_nonneg (μ + b i)
    have h2 := A.be_self_nonneg (μ - b i)
    have h3 := A.be_self_nonneg (b i)
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, A.be_symm (b i) μ] at h1 h2
    constructor <;> omega
  exact ⟨fun i => (key i).1, fun i => (key i).2⟩

theorem be_le_exponent {j : ℕ} (hj : j ≠ 0) (α μ : A.X) :
    A.be μ μ ≤ 4 * (A.exponent j α μ + A.be α α) := by
  have h1 := A.two_mul_exponent j α μ
  have h2 := A.be_self_nonneg (μ + (α + α))
  have h0 := A.be_self_nonneg μ
  simp only [map_add, LinearMap.add_apply, A.be_symm α μ] at h2
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
  nlinarith [mul_le_mul_of_nonneg_right hj' h0]

theorem neg_be_le_exponent {j : ℕ} (hj : j ≠ 0) (α μ : A.X) : -A.be α α ≤ A.exponent j α μ := by
  have h1 := A.be_le_exponent hj α μ
  have h0 := A.be_self_nonneg μ
  omega

theorem finite_exponent_le {j : ℕ} (hj : j ≠ 0) (α : A.X) (n : ℤ) : {μ | A.exponent j α μ ≤ n}.Finite :=
  (A.finite_be_le (4 * (n + A.be α α))).subset fun μ hμ => by
    have h1 := A.be_le_exponent hj α μ
    have h2 : A.exponent j α μ ≤ n := hμ
    show A.be μ μ ≤ _
    omega

theorem finite_exponent_eq {j : ℕ} (hj : j ≠ 0) (α : A.X) (n : ℤ) : {μ | A.exponent j α μ = n}.Finite :=
  (A.finite_exponent_le hj α n).subset fun _ hμ => le_of_eq hμ

def level (j : ℕ) [NeZero j] (α : A.X) (n : ℤ) : Finset A.X := (A.finite_exponent_eq (NeZero.ne j) α n).toFinset

@[simp] theorem mem_level {j : ℕ} [NeZero j] {α : A.X} {n : ℤ} {μ : A.X} :
    μ ∈ A.level j α n ↔ A.exponent j α μ = n := by simp [level]

theorem level_eq_empty {j : ℕ} [NeZero j] {α : A.X} {n : ℤ} (hn : n < -A.be α α) : A.level j α n = ∅ :=
  Finset.eq_empty_of_forall_notMem fun μ hμ => by
    have h1 := A.neg_be_le_exponent (NeZero.ne j) α μ
    rw [mem_level] at hμ
    omega

def FSum (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) : LaurentSeries ℂ :=
  HahnSeries.ofSuppBddBelow (fun n => ∑ μ ∈ A.level j α n, A.term j α th μ v)
    ⟨-A.be α α, fun n hn => by
      by_contra h
      exact hn (by simp only [A.level_eq_empty (not_le.1 h), Finset.sum_empty])⟩

theorem coeff_FSum (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) (n : ℤ) :
    (A.FSum j α th v).coeff n = ∑ μ ∈ A.level j α n, A.term j α th μ v := rfl

theorem coeff_FSum_eq_zero (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) {n : ℤ}
    (hn : n < -A.be α α) : (A.FSum j α th v).coeff n = 0 := by
  rw [coeff_FSum, A.level_eq_empty hn, Finset.sum_empty]

theorem term_add_P0_l {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (μ : A.X) (l : A.abelian₂)
    (v : A.V) : A.term j α th μ (v + A.P0 (La.mk 0 0 l)) =
      (A.chi l * Complex.exp (Real.pi * A.H v.2 l + Real.pi / 2 * A.H l l)) ^ j * A.term j α th μ v := by
  have h1 : (v + A.P0 (La.mk 0 0 l)).1 (α + j • μ) =
      v.1 (α + j • μ) + -(A.H (A.ct (α + j • μ)) l / (2 * Complex.I)) := by
    rw [Prod.fst_add, AddMonoidHom.add_apply, degeneratingTori_basePeriodMap_fst_apply]; simp
  have h2 : (v + A.P0 (La.mk 0 0 l)).2 + A.ct μ = v.2 + l + A.ct μ := by simp
  have h3 := (A.translate_mem_Theta h μ).2 l v.2
  beta_reduce at h3
  have h4 : Complex.exp (-(Real.pi * A.H (A.ct (α + j • μ)) l)) *
      Complex.exp (Real.pi * A.H (A.ct (α + j • μ)) l) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [term, term, h1, h2, h3, e_add, e_neg_div]
  change _ = A.ah l v.2 ^ j * _
  linear_combination ((A.psi μ : ℂ) ^ j * eTwoPi (A.T μ α) * eTwoPi (v.1 (α + j • μ)) * A.ah l v.2 ^ j *
    th (v.2 + A.ct μ)) * h4

theorem term_add_P0_n (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ : A.X) (n : A.X →+ ℤ) (v : A.V) :
    A.term j α th μ (v + A.P0 (La.mk 0 n 0)) = A.term j α th μ v := by
  have h1 : (v + A.P0 (La.mk 0 n 0)).1 (α + j • μ) = v.1 (α + j • μ) + (n (α + j • μ) : ℤ) := by
    rw [Prod.fst_add, AddMonoidHom.add_apply, degeneratingTori_basePeriodMap_fst_apply]; simp
  have h2 : (v + A.P0 (La.mk 0 n 0)).2 = v.2 := by simp
  rw [term, term, h1, h2, e_add, e_intCast, mul_one]

theorem term_add_Pw_y (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (w : ℂ) (μ y : A.X) (v : A.V) :
    (A.psi y * eTwoPi (v.1 y) * eTwoPi (w * A.q y)) ^ j *
        (A.term j α th μ (v + A.Pw w (La.mk y 0 0)) * eTwoPi (w * A.exponent j α μ)) =
      A.term j α th (μ + y) v * eTwoPi (w * A.exponent j α (μ + y)) := by
  have h1 : (v + A.Pw w (La.mk y 0 0)).1 (α + j • μ) =
      v.1 (α + j • μ) + A.T y α + j * A.T μ y + w * A.be y α + j * (w * A.be μ y) := by
    rw [Prod.fst_add, AddMonoidHom.add_apply, Pw_fst_apply, A.T_symm μ y, A.be_symm μ y]
    simp; ring
  have h2 : (v + A.Pw w (La.mk y 0 0)).2 + A.ct μ = v.2 + A.ct (μ + y) := by
    simp; abel
  have h3 : v.1 (α + j • (μ + y)) = v.1 (α + j • μ) + j * v.1 y := by
    simp; ring
  have h4 : w * A.exponent j α (μ + y) =
      w * A.exponent j α μ + j * (w * A.q y) + j * (w * A.be μ y) + w * A.be y α := by
    simp [exponent, q_add]; ring
  rw [term, term, h1, h2, h3, h4, psi_add, map_add A.T, AddMonoidHom.add_apply]
  simp only [e_add, e_nat_mul, mul_pow]
  ring

def beInt : LinearMap.BilinForm ℤ ℤ :=
  LinearMap.mk₂ ℤ (fun x y => 2 * x * y) (fun _ _ _ => by ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by ring) (fun _ _ _ => by simp; ring)

@[simp] theorem beInt_apply (x y : ℤ) : beInt x y = 2 * x * y := rfl

def TInt (τ₀ : ℂ) : ℤ →+ ℤ →+ ℂ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => τ₀ * x * y) (fun _ _ => by push_cast; ring))
    (fun _ _ => by ext; simp; ring)

@[simp] theorem TInt_apply (τ₀ : ℂ) (x y : ℤ) : TInt τ₀ x y = τ₀ * x * y := rfl

def psiInt (τ₀ : ℂ) (x : ℤ) : ℂˣ := Units.mk0 (eTwoPi (τ₀ * x ^ 2 / 2)) (e_ne_zero _)

@[simp] theorem coe_psiInt (τ₀ : ℂ) (x : ℤ) : (psiInt τ₀ x : ℂ) = eTwoPi (τ₀ * x ^ 2 / 2) := rfl

theorem psiInt_neg (τ₀ : ℂ) (x : ℤ) : psiInt τ₀ (-x) = psiInt τ₀ x := Units.ext (by simp)

theorem psiInt_add (τ₀ : ℂ) (x y : ℤ) :
    (psiInt τ₀ (x + y) : ℂ) = psiInt τ₀ x * psiInt τ₀ y * eTwoPi (TInt τ₀ x y) := by
  simp only [coe_psiInt, TInt_apply, ← e_add]
  congr 1; push_cast; ring

def tate (τ₀ : ℂ) : AnArc ℤ where
  gB := 0
  abelian₂ := ⊥
  discrete := inferInstance
  full := Subsingleton.elim _ _
  Hm := 0
  Hm_herm := Matrix.isHermitian_zero
  Hm_pos z hz := absurd (Subsingleton.elim _ _) hz
  Ef := 0
  Ef_eq l m := by simp [hermForm]
  Ef_bij := ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  chi _ := 1
  chi_norm _ := norm_one
  chi_add l m := by simp [hermForm]
  chi_neg _ := rfl
  F := Int.castRingHom _
  F_mem a l _ := Subsingleton.elim (α := Fin 0 → ℂ) _ _
  F_adj a z w := by simp [hermForm]
  X := ℤ
  ct := 0
  ct_smul _ _ := Subsingleton.elim _ _
  T := TInt τ₀
  T_symm x y := by simp only [TInt_apply]; ring
  T_adj a y x := by simp; ring
  psi := psiInt τ₀
  psi_neg := psiInt_neg τ₀
  psi_add := psiInt_add τ₀
  be := beInt
  be_symm x y := by simp only [beInt_apply]; ring
  be_pos x hx := by simp only [beInt_apply]; have := mul_self_pos.2 hx; linarith
  be_adj a y x := by simp; ring
  be_even x := ⟨x * x, by simp only [beInt_apply]; ring⟩

theorem tate_Pw (τ₀ w : ℂ) (y : ℤ) (n : ℤ →+ ℤ) :
    ((tate τ₀).Pw w (La.mk (A := tate τ₀) y n 0)).1 (1 : ℤ) = n 1 + y * (τ₀ + 2 * w) := by
  change TInt τ₀ y 1 + (n 1 : ℤ) - hermForm (0 : Matrix (Fin 0) (Fin 0) ℂ) 0 0 / (2 * Complex.I) +
    w * (beInt y 1 : ℤ) = _
  simp [hermForm]; ring

theorem tate_EF (τ₀ : ℂ) : (tate τ₀).EF (La.mk (A := tate τ₀) 0 (AddMonoidHom.id ℤ) 0)
    (La.mk (A := tate τ₀) (1 : ℤ) 0 0) = -1 := (tate τ₀).EF_n_y _ _

theorem tate_one_mem_Theta (τ₀ : ℂ) (j : ℕ) (α : (tate τ₀).X) :
    (1 : (Fin (tate τ₀).gB → ℂ) → ℂ) ∈ (tate τ₀).Theta j α :=
  ⟨differentiable_const 1, fun l z => by
    have hl : l = 0 := Subsingleton.elim (α := (⊥ : Submodule ℤ (Fin 0 → ℂ))) _ _
    simp [hl, ah]⟩

theorem tate_exponent (τ₀ : ℂ) (μ : ℤ) : (tate τ₀).exponent 1 (0 : ℤ) μ = μ ^ 2 := by
  change ((1 : ℕ) : ℤ) * (beInt μ μ / 2) + beInt μ 0 = _
  simp [mul_assoc, sq]

theorem tate_Sum (τ₀ w : ℂ) (v : (tate τ₀).V) : (tate τ₀).Sum 1 (0 : ℤ) 1 w v =
    ∑' μ : ℤ, eTwoPi (μ ^ 2 * (τ₀ + 2 * w) / 2 + μ * v.1 (1 : ℤ)) := by
  refine tsum_congr fun μ : ℤ => ?_
  obtain ⟨l, z⟩ : (ℤ →+ ℂ) × (Fin 0 → ℂ) := v
  have h1 : l (@HAdd.hAdd ℤ ℤ ℤ _ 0 ((1 : ℕ) • μ)) = μ * l 1 := by simpa using map_zsmul l μ 1
  rw [tate_exponent]
  change (psiInt τ₀ μ : ℂ) ^ 1 * eTwoPi (TInt τ₀ μ 0) * eTwoPi (l (@HAdd.hAdd ℤ ℤ ℤ _ 0 ((1 : ℕ) • μ))) * 1 *
      eTwoPi (w * ((μ ^ 2 : ℤ) : ℂ)) =
    eTwoPi (μ ^ 2 * (τ₀ + 2 * w) / 2 + μ * l 1)
  rw [h1]
  simp only [coe_psiInt, pow_one, mul_one, TInt_apply, ← e_add]
  congr 1; push_cast; ring

theorem tate_FSum_coeff_zero (τ₀ : ℂ) (v : (tate τ₀).V) : ((tate τ₀).FSum 1 0 1 v).coeff 0 = 1 := by
  have h : (tate τ₀).level 1 0 0 = {0} := by
    ext μ
    rw [mem_level, Finset.mem_singleton]
    exact (Eq.congr_left (tate_exponent τ₀ μ)).trans (pow_eq_zero_iff (M₀ := ℤ) two_ne_zero)
  rw [coeff_FSum, h, Finset.sum_singleton]
  simp [term]

def gaussEmb : GaussianInt →ₗ[ℤ] (Fin 1 → ℂ) where
  toFun a _ := a
  map_add' a b := by ext; simp
  map_smul' k a := by ext; simp

@[simp] theorem gaussEmb_apply (a : GaussianInt) (i : Fin 1) : gaussEmb a i = a := rfl

def gaussLam : Submodule ℤ (Fin 1 → ℂ) := LinearMap.range gaussEmb

def gaussEquiv : GaussianInt ≃ₗ[ℤ] gaussLam :=
  LinearEquiv.ofInjective gaussEmb fun _ _ h => GaussianInt.toComplex_injective (congrFun h 0)

@[simp] theorem coe_gaussEquiv (a : GaussianInt) : (gaussEquiv a : Fin 1 → ℂ) = gaussEmb a := rfl

theorem hermForm_one (z w : Fin 1 → ℂ) : hermForm 1 z w = z 0 * starRingEnd ℂ (w 0) := by
  simp [hermForm, dotProduct]

def gaussForm : LinearMap.BilinForm ℤ GaussianInt :=
  LinearMap.mk₂ ℤ (fun a b => a.im * b.re - a.re * b.im) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

@[simp] theorem gaussForm_apply (a b : GaussianInt) : gaussForm a b = a.im * b.re - a.re * b.im := rfl

def gaussEf : LinearMap.BilinForm ℤ gaussLam := LinearMap.BilinForm.congr gaussEquiv gaussForm

@[simp] theorem gaussEf_apply (a b : GaussianInt) :
    gaussEf (gaussEquiv a) (gaussEquiv b) = a.im * b.re - a.re * b.im := by simp [gaussEf]

theorem gaussEf_eq (l m : gaussLam) : (gaussEf l m : ℝ) = (hermForm 1 (l : Fin 1 → ℂ) m).im := by
  obtain ⟨a, rfl⟩ := gaussEquiv.surjective l
  obtain ⟨b, rfl⟩ := gaussEquiv.surjective m
  rw [gaussEf_apply, hermForm_one]
  simp; ring

theorem gaussEf_bij : Function.Bijective gaussEf := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro l hl
    obtain ⟨a, rfl⟩ := gaussEquiv.surjective l
    have h1 := gaussEf_apply a 1
    have h2 := gaussEf_apply a ⟨0, 1⟩
    rw [hl] at h1 h2
    have : a = 0 := by ext <;> simp at h1 h2 ⊢ <;> omega
    simp [this]
  · intro φ
    refine ⟨gaussEquiv ⟨-φ (gaussEquiv ⟨0, 1⟩), φ (gaussEquiv 1)⟩, LinearMap.ext fun m => ?_⟩
    obtain ⟨b, rfl⟩ := gaussEquiv.surjective m
    have hb : b = b.re • (1 : GaussianInt) + b.im • (⟨0, 1⟩ : GaussianInt) := by ext <;> simp
    rw [gaussEf_apply]
    conv_rhs => rw [hb, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_zsmul]
    simp; ring

theorem gaussLam_discrete : DiscreteTopology gaussLam := by
  refine DiscreteTopology.of_forall_le_norm one_pos fun l hl => ?_
  obtain ⟨a, rfl⟩ := gaussEquiv.surjective l
  have ha : a ≠ 0 := by rintro rfl; simp at hl
  have h1 : (1 : ℝ) ≤ Complex.normSq a := by
    rw [← GaussianInt.intCast_real_norm]
    exact_mod_cast GaussianInt.norm_pos.2 ha
  have h2 : (1 : ℝ) ≤ ‖(a : ℂ)‖ := by
    rw [Complex.normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg (a : ℂ)]
  exact h2.trans (norm_le_pi_norm (gaussEmb a) 0)

theorem gaussLam_full : Submodule.span ℝ (gaussLam : Set (Fin 1 → ℂ)) = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  have hz : z = (z 0).re • gaussEmb 1 + (z 0).im • gaussEmb ⟨0, 1⟩ := by
    funext i
    rw [Subsingleton.elim i 0]
    simp [GaussianInt.toComplex_def']
  rw [hz]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

def gaussChi (l : gaussLam) : ℂ :=
  Complex.exp (Real.pi * Complex.I * ((l.1 0).re * (l.1 0).im : ℝ))

theorem gaussChi_norm (l : gaussLam) : ‖gaussChi l‖ = 1 := by
  rw [gaussChi, mul_right_comm, ← Complex.ofReal_mul]
  exact Complex.norm_exp_ofReal_mul_I _

theorem gaussChi_add (l m : gaussLam) : gaussChi (l + m) =
    gaussChi l * gaussChi m * Complex.exp (Real.pi * Complex.I * ((hermForm 1 (l : Fin 1 → ℂ) m).im : ℂ)) := by
  rw [← gaussEf_eq]
  obtain ⟨a, rfl⟩ := gaussEquiv.surjective l
  obtain ⟨b, rfl⟩ := gaussEquiv.surjective m
  rw [gaussEf_apply, gaussChi, gaussChi, gaussChi, ← Complex.exp_add, ← Complex.exp_add,
    Complex.exp_eq_exp_iff_exists_int]
  refine ⟨a.re * b.im, ?_⟩
  simp [← GaussianInt.intCast_re, ← GaussianInt.intCast_im]; ring

theorem gaussChi_neg (l : gaussLam) : gaussChi (-l) = gaussChi l := by simp [gaussChi]

theorem hermForm_one_pos (z : Fin 1 → ℂ) (hz : z ≠ 0) : 0 < (hermForm 1 z z).re := by
  have h : z 0 ≠ 0 := fun h => hz (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
  rw [hermForm_one, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_pos.2 h

def gaussInt (c τ₀ : ℂ) : AnArc ℤ where
  gB := 1
  abelian₂ := gaussLam
  discrete := gaussLam_discrete
  full := gaussLam_full
  Hm := 1
  Hm_herm := Matrix.isHermitian_one
  Hm_pos := hermForm_one_pos
  Ef := gaussEf
  Ef_eq := gaussEf_eq
  Ef_bij := gaussEf_bij
  chi := gaussChi
  chi_norm := gaussChi_norm
  chi_add := gaussChi_add
  chi_neg := gaussChi_neg
  F := Int.castRingHom _
  F_mem a l hl := by simpa using gaussLam.smul_mem a hl
  F_adj a z w := by simp [hermForm_one]; ring
  X := ℤ
  ct := AddMonoidHom.mk' (fun x _ => x * c) fun _ _ => by ext; simp; ring
  ct_smul a x := by ext; simp; ring
  T := TInt τ₀
  T_symm x y := by simp only [TInt_apply]; ring
  T_adj a y x := by simp; ring
  psi := psiInt τ₀
  psi_neg := psiInt_neg τ₀
  psi_add := psiInt_add τ₀
  be := beInt
  be_symm x y := by simp only [beInt_apply]; ring
  be_pos x hx := by simp only [beInt_apply]; have := mul_self_pos.2 hx; linarith
  be_adj a y x := by simp; ring
  be_even x := ⟨x * x, by simp only [beInt_apply]; ring⟩

theorem gaussInt_ct_zero (τ₀ : ℂ) : (gaussInt 0 τ₀).ct = 0 := by
  refine AddMonoidHom.ext fun x => funext fun i => ?_
  exact mul_zero _

theorem gaussInt_EF (c τ₀ : ℂ) : (gaussInt c τ₀).EF (La.mk (A := gaussInt c τ₀) 0 0 (gaussEquiv 1))
    (La.mk (A := gaussInt c τ₀) 0 0 (gaussEquiv ⟨0, 1⟩)) = -1 := by
  rw [EF_apply]
  change (0 : ℤ) - 0 + gaussEf (gaussEquiv 1) (gaussEquiv ⟨0, 1⟩) = -1
  simp

theorem gaussian_integers_period_component (c τ₀ : ℂ) :
    ((gaussInt c τ₀).P0 (La.mk (A := gaussInt c τ₀) 0 0 (gaussEquiv 1))).1 (1 : ℤ) = -(c / (2 * Complex.I)) := by
  change TInt τ₀ 0 1 + ((0 : ℤ) : ℂ) -
    hermForm 1 (fun _ : Fin 1 => ((1 : ℤ) : ℂ) * c) (gaussEmb 1) / (2 * Complex.I) = _
  simp [hermForm_one]

def gaussProd : (ℤ × ℤ) ≃ₗ[ℤ] GaussianInt where
  toFun p := ⟨p.1, p.2⟩
  invFun a := (a.re, a.im)
  map_add' _ _ := rfl
  map_smul' _ _ := by ext <;> simp
  left_inv _ := rfl
  right_inv _ := rfl

def beGauss : LinearMap.BilinForm ℤ GaussianInt :=
  LinearMap.mk₂ ℤ (fun a b => 2 * (a.re * b.re + a.im * b.im)) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

@[simp] theorem beGauss_apply (a b : GaussianInt) : beGauss a b = 2 * (a.re * b.re + a.im * b.im) := rfl

def gaussCM (c τ₀ : ℂ) : AnArc GaussianInt where
  gB := 1
  abelian₂ := gaussLam
  discrete := gaussLam_discrete
  full := gaussLam_full
  Hm := 1
  Hm_herm := Matrix.isHermitian_one
  Hm_pos := hermForm_one_pos
  Ef := gaussEf
  Ef_eq := gaussEf_eq
  Ef_bij := gaussEf_bij
  chi := gaussChi
  chi_norm := gaussChi_norm
  chi_add := gaussChi_add
  chi_neg := gaussChi_neg
  F := (algebraMap ℂ _).comp GaussianInt.toComplex
  F_mem := by
    rintro a _ ⟨b, rfl⟩
    exact ⟨a * b, by ext; simp⟩
  F_adj a z w := by simp [hermForm_one]; ring
  X := GaussianInt
  free := Module.Free.of_equiv gaussProd
  fin := Module.Finite.equiv gaussProd
  ct := AddMonoidHom.mk' (fun x _ => x * c) fun _ _ => by ext; simp; ring
  ct_smul a x := by ext; simp; ring
  T := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => τ₀ * beGauss x y) fun _ _ => by simp; ring)
    fun _ _ => by ext; simp; ring
  T_symm x y := by
    show τ₀ * (beGauss x y : ℤ) = τ₀ * (beGauss y x : ℤ)
    congr 2; simp only [beGauss_apply]; ring
  T_adj a y x := by
    show τ₀ * (beGauss (a • y) x : ℤ) = τ₀ * (beGauss y (star a • x) : ℤ)
    congr 2; simp; ring
  psi x := Units.mk0 (eTwoPi (τ₀ * (x.re ^ 2 + x.im ^ 2))) (e_ne_zero _)
  psi_neg x := Units.ext (by simp)
  psi_add x y := by
    simp only [Units.val_mk0, ← e_add]
    congr 1; simp; ring
  be := beGauss
  be_symm x y := by simp only [beGauss_apply]; ring
  be_pos x hx := by
    have := GaussianInt.norm_pos.2 hx
    simp only [beGauss_apply]
    rw [Zsqrtd.norm_def] at this
    linarith
  be_adj a y x := by simp; ring
  be_even x := ⟨_, rfl⟩

example (c τ₀ : ℂ) (v : (gaussCM c τ₀).La) :
    ((⟨0, 1⟩ : GaussianInt) • v).n (1 : GaussianInt) = v.n (⟨0, -1⟩ : GaussianInt) := by
  refine congrArg v.n ?_
  show star (⟨0, 1⟩ : GaussianInt) * 1 = ⟨0, -1⟩
  ext <;> simp

example (τ₀ : ℂ) : Module.finrank ℂ (tate τ₀).V = 1 := by
  rw [finrank_V]
  exact congrArg (· + 0) (Module.finrank_self ℤ)

example : (NormedSpace.toModule : Module ℝ A.V) =
    @Prod.instModule ℝ _ _ _ _ _ AddMonoidHom.instModule (Pi.Function.module _ _ _) := by
  with_reducible_and_instances rfl

example : CompleteSpace A.V ∧ FiniteDimensional ℂ A.V ∧ FiniteDimensional ℝ A.V ∧ IsScalarTower ℝ ℂ A.V :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end AnArc

end GlobalTheory
