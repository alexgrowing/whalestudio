import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalModuleMatrixApplyPointsActionLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralExponentialSimilitudeGauge

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PlaceInt.MatAct GlobalTheory.PlaceInt.Kappa

namespace GlobalTheory.PlaceInt.TrKappa

section Abstract
variable {R : Type} [CommRing R]

def iter (ψ : R →+* R) (a : R) (k : ℕ) : R := (fun f => a * ψ f)^[k] 1

theorem iter_zero (ψ : R →+* R) (a : R) : iter ψ a 0 = 1 := rfl

theorem iter_succ (ψ : R →+* R) (a : R) (k : ℕ) : iter ψ a (k + 1) = a * ψ (iter ψ a k) := by
  unfold iter
  rw [Function.iterate_succ_apply']

theorem iter_prod {J : Type} [Fintype J] (ψ : R →+* R) (a : J → R) (k : ℕ) :
    iter ψ (∏ b, a b) k = ∏ b, iter ψ (a b) k := by
  induction k with
  | zero => simp [iter_zero]
  | succ k ih => simp only [iter_succ, ih, map_prod, Finset.prod_mul_distrib]

theorem map_iter {S : Type} [CommRing S] (e : S →+* R) (φ : S → S) (ψ : R →+* R) (he : ∀ f, e (φ f) = ψ (e f))
    (a : S) (k : ℕ) : e ((fun f => a * φ f)^[k] 1) = iter ψ (e a) k := by
  induction k with
  | zero => simp [iter_zero]
  | succ k ih => rw [Function.iterate_succ_apply', iter_succ, map_mul, he, ih]

theorem iter_mul (ψ : R →+* R) (χ U κ : R) (hχ : χ * κ = U * ψ κ) (k : ℕ) :
    iter ψ χ k * κ = iter ψ U k * ψ^[k] κ := by
  induction k with
  | zero => simp [iter_zero]
  | succ k ih =>
    have := congrArg ψ ih
    rw [map_mul, map_mul] at this
    rw [iter_succ, iter_succ, Function.iterate_succ_apply']
    linear_combination ψ (iter ψ χ k) * hχ + U * this

theorem core [IsDomain R] [CharZero R] (ψ E0 Ea En : R →+* R) (U κ T I : R) (N : ℕ) (hN : Odd N)
    (h1 : ∀ f, ψ (E0 f) = E0 f) (h2 : ∀ f, ψ (Ea f) = Ea f) (h3 : ∀ f, E0 (E0 f) = E0 f)
    (h4 : ∀ f, E0 (Ea f) = Ea f) (h5 : ∀ f, En (E0 f) = E0 f) (h6 : ∀ f, E0 (ψ f) = Ea f)
    (h7 : ∀ f, En (ψ f) = E0 f) (hκ : IsUnit κ) (hU : IsUnit U) (hκ0 : E0 κ = 1) (hper : ψ^[N] κ = κ)
    (hord : iter ψ U N = 1)
    (hcube : ψ (ψ κ) * κ * Ea κ * Ea κ * T = ψ κ * ψ κ * Ea (ψ κ))
    (hmul : ψ U * E0 U = U * Ea U * T) (hneg : En κ * I = Ea κ) (hsym : E0 U * I * En U = 1) :
    U * ψ κ = κ := by
  obtain ⟨k', hk'⟩ := hκ.exists_right_inv
  have hκne : κ ≠ 0 := hκ.ne_zero
  obtain ⟨χ, hχ⟩ : ∃ χ, χ * κ = U * ψ κ := ⟨U * ψ κ * k', by linear_combination U * ψ κ * hk'⟩
  have hχu : IsUnit χ := isUnit_of_mul_isUnit_left (hχ ▸ hU.mul (hκ.map ψ))
  have e0 : E0 χ = E0 U * Ea κ := by
    have := congrArg E0 hχ
    rwa [map_mul, map_mul, hκ0, _root_.mul_one, h6] at this
  have e1 : ψ χ * ψ κ = ψ U * ψ (ψ κ) := by rw [← map_mul, hχ, map_mul]
  have e2 : Ea χ * Ea κ = Ea U * Ea (ψ κ) := by rw [← map_mul, hχ, map_mul]
  have e3 : ψ χ * E0 χ = χ * Ea χ := by
    have hne : ψ κ * κ * Ea κ ≠ 0 := (((hκ.map ψ).mul hκ).mul (hκ.map Ea)).ne_zero
    apply mul_right_cancel₀ hne
    rw [e0]
    linear_combination (E0 U * Ea κ * κ * Ea κ) * e1 + (ψ (ψ κ) * κ * Ea κ * Ea κ) * hmul + (U * Ea U) * hcube
      - (ψ κ * Ea χ * Ea κ) * hχ - (U * ψ κ * ψ κ) * e2
  obtain ⟨c', hc'⟩ := hχu.exists_right_inv
  have hc0 : E0 χ * E0 c' = 1 := by rw [← map_mul, hc', map_one]
  have e4 : ψ χ = (Ea χ * E0 c') * χ := by linear_combination E0 c' * e3 - ψ χ * hc0
  have e5 : ∀ k : ℕ, ∃ l, ψ l = l ∧ E0 l = l ∧ iter ψ χ k = l * χ ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, map_one _, map_one _, by simp [iter_zero]⟩
    | succ k ih =>
      obtain ⟨l, a, b, c⟩ := ih
      refine ⟨l * (Ea χ * E0 c') ^ k, by simp only [map_mul, map_pow, a, h1, h2],
        by simp only [map_mul, map_pow, b, h3, h4], ?_⟩
      rw [iter_succ, c, map_mul, map_pow, a, e4]
      ring
  have e6 : iter ψ χ N = 1 := by
    have := iter_mul ψ χ U κ hχ N
    rw [hord, hper] at this
    exact mul_right_cancel₀ hκne this
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have e7 : χ = E0 χ := by
    obtain ⟨l, -, b, c⟩ := e5 N
    rw [e6] at c
    have c0 := congrArg E0 c
    rw [map_one, map_mul, map_pow, b] at c0
    have hl : l ≠ 0 := by rintro rfl; simp at c
    have hp : χ ^ N = E0 χ ^ N := mul_left_cancel₀ hl (c.symm.trans c0)
    have hg := (Commute.all χ (E0 χ)).geom_sum₂_mul N
    rw [hp, sub_self] at hg
    rcases mul_eq_zero.1 hg with hg | hg
    · exfalso
      have := congrArg E0 hg
      simp only [map_sum, map_mul, map_pow, h3, map_zero] at this
      rw [geom_sum₂_self] at this
      exact mul_ne_zero (Nat.cast_ne_zero.2 hN0) (pow_ne_zero _ (hχu.map E0).ne_zero) this
    · exact sub_eq_zero.1 hg
  have e8 : ψ χ = χ := by rw [e7, h1]
  have e9 : ∀ k, iter ψ χ k = χ ^ k := by
    intro k
    induction k with
    | zero => simp [iter_zero]
    | succ k ih => rw [iter_succ, ih, map_pow, e8, pow_succ']
  have e10 : χ * En κ = En U := by
    have := congrArg En hχ
    rwa [map_mul, map_mul, h7, hκ0, _root_.mul_one, e7, h5, ← e7] at this
  have e11 : χ ^ 2 = 1 := by
    have hne : En κ ≠ 0 := (hκ.map En).ne_zero
    rw [← e7] at e0
    apply mul_right_cancel₀ hne
    linear_combination χ * e10 + En U * e0 - (E0 U * En U) * hneg + En κ * hsym
  obtain ⟨r, rfl⟩ := hN
  have e12 : χ = 1 := by
    have := e9 (2 * r + 1)
    rw [e6, pow_succ, pow_mul, e11, one_pow, _root_.one_mul] at this
    exact this.symm
  rw [← hχ, e12, _root_.one_mul]

end Abstract

section Points
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O] {B : FB V d O}

def evS {k m : ℕ} (x : Fin k → SP B m) : PS V k d →+* PS V m d :=
  (evV_alg (fun j => (x j).val) fun j => (x j).sm).choose.toRingHom

theorem evS_eq {k m : ℕ} (x : Fin k → SP B m) (f : PS V k d) : evS x f = evV (fun j => (x j).val) f :=
  ((evV_alg (fun j => (x j).val) fun j => (x j).sm).choose_spec.2 f).symm

theorem evS_C {k m : ℕ} (x : Fin k → SP B m) (c : V) : evS x (MvPowerSeries.C c) = MvPowerSeries.C c :=
  (evV_alg (fun j => (x j).val) fun j => (x j).sm).choose.commutes c

theorem evS_X {k m : ℕ} (x : Fin k → SP B m) (j : Fin k) (i : Fin d) :
    evS x (MvPowerSeries.X (j, i)) = (x j).val i :=
  (evV_alg (fun j => (x j).val) fun j => (x j).sm).choose_spec.1 (j, i)

def sL {k m : ℕ} (x : Fin k → SP B m) : SP B k →ₗ[O] SP B m := evL B (fun j => (x j).val) fun j => (x j).sm

theorem evS_comp {l k m : ℕ} (x : Fin k → SP B m) (a : Fin l → SP B k) (f : PS V l d) :
    evS x (evS a f) = evS (fun j => sL x (a j)) f := by
  rw [evS_eq, evS_eq, evS_eq, evV_comp _ _ (fun j => (a j).sm) fun j => (x j).sm]
  rfl

theorem evS_comp1 {k m : ℕ} (x : Fin k → SP B m) (a : SP B k) (f : PS V 1 d) :
    evS x (evS ![a] f) = evS ![sL x a] f := by
  rw [evS_comp]
  congr 2
  funext j; fin_cases j; rfl

theorem evS_comp3 {k m : ℕ} (x : Fin k → SP B m) (a b c : SP B k) (f : PS V 3 d) :
    evS x (evS ![a, b, c] f) = evS ![sL x a, sL x b, sL x c] f := by
  rw [evS_comp]
  congr 2
  funext j; fin_cases j <;> rfl

theorem smallPointSubstitution_single_eq_constTerms {m : ℕ} (a : SP B m) (f : PS V 1 d) : evS ![a] f = evV ![a.val] f := by
  rw [evS_eq]
  congr 1
  funext j; fin_cases j; rfl

theorem smallPointSubstitution_triple_eq_constTerms {m : ℕ} (a b c : SP B m) (f : PS V 3 d) : evS ![a, b, c] f = evV ![a.val, b.val, c.val] f := by
  rw [evS_eq]
  congr 1
  funext j; fin_cases j <;> rfl

variable (B) in

def uP {k : ℕ} (j : Fin k) : SP B k := ⟨pt V d j, sm_pt j⟩

variable (B) in

def cS {m : ℕ} (α : Fin d → V) (h : Small α) : SP B m := ⟨cpt α, fun i => by simpa [cpt] using h i⟩

theorem sL_uP {k m : ℕ} (x : Fin k → SP B m) (j : Fin k) : sL x (uP B j) = x j :=
  SP.ext (funext fun i => (evS_eq x _).symm.trans (evS_X x j i))

theorem sL_cS {k m : ℕ} (x : Fin k → SP B m) (α : Fin d → V) (h : Small α) : sL x (cS B α h) = cS B α h :=
  SP.ext (funext fun i => (evS_eq x _).symm.trans (evS_C x (α i)))

theorem evS_uP {k : ℕ} (f : PS V k d) : evS (uP B) f = f := by
  rw [evS_eq, evV_eq_ev (fun j => (uP B j).val) (fun j => gp_pt j)]
  change MvPowerSeries.subst (fun p : Fin k × Fin d => MvPowerSeries.X (p.1, p.2)) f = f
  exact congrFun MvPowerSeries.subst_self f

theorem evS_zero {k m : ℕ} (f : PS V k d) :
    evS (fun _ => (0 : SP B m)) f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
  rw [evS_eq, evV_eq_ev (fun _ => (0 : SP B m).val) (fun j => gp_zero₂)]
  change MvPowerSeries.subst (0 : Fin k × Fin d → PS V m d) f = _
  rw [MvPowerSeries.subst_zero_eq_C_constantCoeff]
  simp

theorem evS_zero1 {m : ℕ} (f : PS V 1 d) :
    evS ![(0 : SP B m)] f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
  rw [← evS_zero (B := B)]
  congr 2
  funext j; fin_cases j; rfl

theorem val_add_gp {m : ℕ} {x y : SP B m} (hx : GP x.val) (hy : GP y.val) :
    (x + y).val = addOf B.G.F x.val y.val := funext fun _ => evV_eq_ev _ (pair_points_zero_constant hx hy) _

theorem val_smul_gp {m : ℕ} (a : O) {x : SP B m} (hx : GP x.val) :
    (a • x).val = comp1 (B.A.act a) x.val := funext fun _ => evV_eq_ev _ (single_point_zero_constant hx) _

theorem gp_add {m : ℕ} {x y : SP B m} (hx : GP x.val) (hy : GP y.val) : GP (x + y).val := by
  rw [val_add_gp hx hy]; exact gp_addOf _ B.G.const _ _ hx hy

theorem gp_smul {m : ℕ} (a : O) {x : SP B m} (hx : GP x.val) : GP (a • x).val := by
  rw [val_smul_gp a hx]; exact gp_comp1 _ _ (constantCoeff_act_eq_zero B a) hx

theorem gp_uP {k : ℕ} (j : Fin k) : GP (uP B j).val := gp_pt j

def mv {n m : ℕ} (mu : Matrix (Fin n) (Fin n) O) (x : Fin n → SP B m) (i : Fin n) : SP B m := ∑ j, mu i j • x j

theorem gp_mv {n m : ℕ} (mu : Matrix (Fin n) (Fin n) O) {x : Fin n → SP B m} (hx : ∀ j, GP (x j).val) (i : Fin n) :
    GP (mv mu x i).val :=
  Finset.sum_induction _ (fun y : SP B m => GP y.val) (fun _ _ => gp_add) gp_zero₂ fun j _ => gp_smul _ (hx j)

theorem sL_mv {n k m : ℕ} (a : Fin k → SP B m) (mu : Matrix (Fin n) (Fin n) O) (x : Fin n → SP B k) (i : Fin n) :
    sL a (mv mu x i) = mv mu (fun j => sL a (x j)) i := by
  simp only [mv, map_sum, map_smul]

theorem mv_add {n m : ℕ} (mu : Matrix (Fin n) (Fin n) O) (x y : Fin n → SP B m) (i : Fin n) :
    mv mu (fun j => x j + y j) i = mv mu x i + mv mu y i := by
  simp only [mv, smul_add, Finset.sum_add_distrib]

theorem mv_smul {n m : ℕ} (mu : Matrix (Fin n) (Fin n) O) (c : O) (x : Fin n → SP B m) (i : Fin n) :
    mv mu (fun j => c • x j) i = c • mv mu x i := by
  simp only [mv, Finset.smul_sum, smul_smul, mul_comm]

end Points

section Logs
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O] {B : FB V d O}
  (K : Type) [Field K] [Algebra ℚ K] [Algebra V K]

def IsExp {m : ℕ} (u : PS V m d) (g : PS K m d) : Prop :=
  MvPowerSeries.constantCoeff g = 0 ∧ FB.toK K u = FB.expS K g

variable {K}

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem IsExp.one {m : ℕ} : IsExp K (1 : PS V m d) 0 := ⟨map_zero _, by rw [expS_zero']; exact map_one _⟩

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem IsExp.mul {m : ℕ} {u v : PS V m d} {f g : PS K m d} (hu : IsExp K u f) (hv : IsExp K v g) :
    IsExp K (u * v) (f + g) :=
  ⟨by rw [map_add, hu.1, hv.1, add_zero], by
    rw [gt_expS_add f g hu.1 hv.1, ← hu.2, ← hv.2]; exact map_mul _ _ _⟩

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem IsExp.pow {m : ℕ} {u : PS V m d} {f : PS K m d} (hu : IsExp K u f) (N : ℕ) : IsExp K (u ^ N) (N • f) := by
  induction N with
  | zero => rw [pow_zero, zero_smul]; exact IsExp.one
  | succ N ih => rw [pow_succ, succ_nsmul]; exact ih.mul hu

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem IsExp.prod {m n : ℕ} {u : Fin n → PS V m d} {f : Fin n → PS K m d} (hu : ∀ b, IsExp K (u b) (f b)) :
    IsExp K (∏ b, u b) (∑ b, f b) := by
  suffices ∀ s : Finset (Fin n), IsExp K (∏ b ∈ s, u b) (∑ b ∈ s, f b) from this _
  intro s
  induction s using Finset.induction_on with
  | empty => exact IsExp.one
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha]; exact (hu a).mul ih

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem IsExp.uniq (hi : Function.Injective (algebraMap V K)) {m : ℕ} {u v : PS V m d} {f g : PS K m d}
    (hu : IsExp K u f) (hv : IsExp K v g) (e : f = g) : u = v := by
  have : FB.toK K u = FB.toK K v := by rw [hu.2, hv.2, e]
  ext s
  apply hi
  have := congrArg (MvPowerSeries.coeff s) this
  simpa [FB.toK, MvPowerSeries.coeff_map] using this

variable (K) in

def evK {k m : ℕ} (a : Fin k → SP B m) (ha : ∀ j, GP (a j).val) : PS K k d →+ PS K m d :=
  AddMonoidHom.mk' (ev fun j => mp K (a j).val) (gt_ev_add _ fun j => constantCoeff_baseChange_eq_zero K (ha j))

theorem IsExp.ev {k m : ℕ} (a : Fin k → SP B m) (ha : ∀ j, GP (a j).val) {u : PS V k d} {f : PS K k d}
    (hu : IsExp K u f) : IsExp K (evS a u) (evK K a ha f) := by
  have ha' : ∀ j, GP (mp K (a j).val) := fun j => constantCoeff_baseChange_eq_zero K (ha j)
  refine ⟨gt_const_ev _ ha' f hu.1, ?_⟩
  rw [evS_eq, evV_eq_ev _ ha, toK_ev K _ ha, hu.2, gt_ev_expS _ ha' f hu.1]
  rfl

def lg (H : PS K 1 d) {m : ℕ} (x : SP B m) : PS K m d := ev ![mp K x.val] H

theorem evK_lg (H : PS K 1 d) {k m : ℕ} (a : Fin k → SP B m) (ha : ∀ j, GP (a j).val) {x : SP B k} (hx : GP x.val) :
    evK K a ha (lg H x) = lg H (sL a x) := by
  have ha' : ∀ j, GP (mp K (a j).val) := fun j => constantCoeff_baseChange_eq_zero K (ha j)
  change ev (fun j => mp K (a j).val) (ev ![mp K x.val] H) = ev _ H
  rw [gt_ev_ev' _ _ ha' (single_point_zero_constant (constantCoeff_baseChange_eq_zero K hx))]
  congr 1
  funext j i
  fin_cases j
  change ev (fun j => mp K (a j).val) (FB.toK K (x.val i)) = FB.toK K (evV (fun j => (a j).val) (x.val i))
  rw [evV_eq_ev _ ha, toK_ev K _ ha]

theorem cc_lg {H : PS K 1 d} (hH : MvPowerSeries.constantCoeff H = 0) {m : ℕ} {x : SP B m} (hx : GP x.val) :
    MvPowerSeries.constantCoeff (lg H x) = 0 := gt_const_ev _ (single_point_zero_constant (constantCoeff_baseChange_eq_zero K hx)) _ hH

theorem lg_zero {H : PS K 1 d} (hH : MvPowerSeries.constantCoeff H = 0) {m : ℕ} : lg H (0 : SP B m) = 0 := by
  change MvPowerSeries.subst (fun p : Fin 1 × Fin d => (![mp K (0 : Pt V m d)] p.1) p.2) H = 0
  have e : (fun p : Fin 1 × Fin d => (![mp K (0 : Pt V m d)] p.1) p.2) = 0 := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j
    simp [mp]
  rw [e]
  exact MvPowerSeries.subst_zero_of_constantCoeff_zero hH

variable {h : PS K 2 d} {w0 : O}

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem cc_hL (hh : B.IsCanonGauge K h) : MvPowerSeries.constantCoeff (B.hL K h w0) = 0 :=
  gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (constantCoeff_actK_eq_zero B K w0) (gp_pt 0))) _ (cc_h hh)

theorem mp_add {m : ℕ} {x y : SP B m} (hx : GP x.val) (hy : GP y.val) :
    mp K (x + y).val = addOf (B.FK K) (mp K x.val) (mp K y.val) := by
  rw [val_add_gp hx hy, mp_addOf K _ hx hy]; rfl

theorem exp_theta (hh : B.IsCanonGauge K h) {Θ : PS V 3 d} (hΘ : IsTheta B K h w0 Θ) {m : ℕ} {x y z : SP B m}
    (hx : GP x.val) (hy : GP y.val) (hz : GP z.val) :
    IsExp K (evS ![x, y, z] Θ) (lg (B.hL K h w0) (x + y + z) - lg (B.hL K h w0) (x + y) - lg (B.hL K h w0) (x + z)
      - lg (B.hL K h w0) (y + z) + lg (B.hL K h w0) x + lg (B.hL K h w0) y + lg (B.hL K h w0) z) := by
  have H0 := cc_hL (w0 := w0) hh
  have p : ∀ j : Fin 3, GP (uP B j).val := gp_uP
  have base : IsExp K Θ (lg (B.hL K h w0) (uP B 0 + uP B 1 + uP B 2) - lg (B.hL K h w0) (uP B 0 + uP B 1)
      - lg (B.hL K h w0) (uP B 0 + uP B 2) - lg (B.hL K h w0) (uP B 1 + uP B 2) + lg (B.hL K h w0) (uP B 0)
      + lg (B.hL K h w0) (uP B 1) + lg (B.hL K h w0) (uP B 2)) := by
    constructor
    · simp only [map_add, map_sub, cc_lg H0 (p _), cc_lg H0 (gp_add (p _) (p _)),
        cc_lg H0 (gp_add (gp_add (p _) (p _)) (p _)), sub_zero, add_zero]
    · have e : ∀ j : Fin 3, mp K (uP B j).val = pt K d j := fun j => mp_pt K j
      simp only [lg, mp_add (p _) (p _), mp_add (gp_add (p _) (p _)) (p _), e]
      exact hΘ
  have ha : ∀ j, GP (![x, y, z] j).val := by intro j; fin_cases j; exacts [hx, hy, hz]
  have := base.ev ![x, y, z] ha
  simp only [map_add, map_sub, evK_lg _ _ ha (p _), evK_lg _ _ ha (gp_add (p _) (p _)),
    evK_lg _ _ ha (gp_add (gp_add (p _) (p _)) (p _)), sL_uP] at this
  exact this

theorem exp_iota (hh : B.IsCanonGauge K h) {jo : PS V 1 d} (hj : IsIota B K h w0 jo) {m : ℕ} {x : SP B m}
    (hx : GP x.val) : IsExp K (evS ![x] jo) (lg (B.hL K h w0) ((-1 : O) • x) - lg (B.hL K h w0) x) := by
  have H0 := cc_hL (w0 := w0) hh
  have p : ∀ j : Fin 1, GP (uP B j).val := gp_uP
  have base : IsExp K jo (lg (B.hL K h w0) ((-1 : O) • uP B 0) - lg (B.hL K h w0) (uP B 0)) := by
    constructor
    · rw [map_sub, cc_lg H0 (p _), cc_lg H0 (gp_smul _ (p _)), sub_zero]
    · have e : mp K (uP B (0 : Fin 1)).val = pt K d 0 := mp_pt K 0
      have e' : ((-1 : O) • uP B (0 : Fin 1)).val = B.A.act (-1) :=
        (val_smul_gp _ (p 0)).trans (gt_comp1_pt_right _)
      rw [lg, lg, e, e', gt_ev_pt_self]
      exact hj
  have ha : ∀ j, GP (![x] j).val := by intro j; fin_cases j; exact hx
  have := base.ev ![x] ha
  simp only [map_sub, map_smul, evK_lg _ _ ha (p _), evK_lg _ _ ha (gp_smul _ (p _)), sL_uP] at this
  exact this

theorem exp_kappa (hh : B.IsCanonGauge K h) {n : ℕ} {mu : Matrix (Fin n) (Fin n) O} {N : ℕ} {κ : PS V n d}
    (hκ : IsKappa B K h w0 mu N κ) {m : ℕ} {x : Fin n → SP B m} (hx : ∀ b, GP (x b).val) :
    IsExp K (evS x κ) (∑ b, lg (B.hL K h w0) (mv mu x b) - N • ∑ b, lg (B.hL K h w0) (x b)) := by
  have H0 := cc_hL (w0 := w0) hh
  have p : ∀ j : Fin n, GP (uP B j).val := gp_uP
  have base : IsExp K κ (∑ b, lg (B.hL K h w0) (mv mu (uP B) b) - N • ∑ b, lg (B.hL K h w0) (uP B b)) := by
    constructor
    · simp only [map_sub, map_nsmul, map_sum, cc_lg H0 (p _), cc_lg H0 (gp_mv mu p _), Finset.sum_const_zero,
        smul_zero, sub_zero]
    · have e : ∀ j : Fin n, mp K (uP B j).val = pt K d j := fun j => mp_pt K j
      have e' : ∀ b, (mv mu (uP B) b).val = matV B mu (fun j => pt V (n := n) d j) b :=
        fun b => (congrFun (matV_val B mu (uP B)) b).symm
      simp only [lg, e, e']
      rw [← Nat.cast_smul_eq_nsmul K]
      exact hκ
  have := base.ev x hx
  simp only [map_sub, map_nsmul, map_sum, evK_lg _ _ hx (p _), evK_lg _ _ hx (gp_mv mu p _), sL_uP, sL_mv] at this
  exact this

variable (hi : Function.Injective (algebraMap V K)) (hh : B.IsCanonGauge K h)
include hi hh

theorem theta_zero {Θ : PS V 3 d} (hΘ : IsTheta B K h w0 Θ) {m : ℕ} (x y : SP B m) : evS ![x, y, 0] Θ = 1 := by
  have e : evS ![uP B (0 : Fin 2), uP B 1, 0] Θ = 1 :=
    (exp_theta hh hΘ (gp_uP _) (gp_uP _) (z := 0) gp_zero₂).uniq hi IsExp.one (by
      simp only [add_zero, lg_zero (cc_hL hh)]
      abel)
  have := congrArg (evS ![x, y]) e
  rwa [evS_comp3, map_one, sL_uP, sL_uP, map_zero] at this

theorem iota_zero {jo : PS V 1 d} (hj : IsIota B K h w0 jo) {m : ℕ} : evS ![(0 : SP B m)] jo = 1 :=
  (exp_iota hh hj (x := 0) gp_zero₂).uniq hi IsExp.one (by rw [smul_zero, sub_self])

theorem kappa_zero {n : ℕ} {mu : Matrix (Fin n) (Fin n) O} {N : ℕ} {κ : PS V n d}
    (hκ : IsKappa B K h w0 mu N κ) {m : ℕ} : evS (fun _ => (0 : SP B m)) κ = 1 :=
  (exp_kappa hh hκ (x := fun _ => 0) fun _ => gp_zero₂).uniq hi IsExp.one (by
    simp [mv, lg_zero (cc_hL hh)])

theorem kappa_neg {jo : PS V 1 d} (hj : IsIota B K h w0 jo) {n : ℕ} {mu : Matrix (Fin n) (Fin n) O} {N : ℕ}
    {κ : PS V n d} (hκ : IsKappa B K h w0 mu N κ) {m : ℕ} (x : Fin n → SP B m) :
    evS (fun b => (-1 : O) • x b) κ * ∏ b, evS ![x b] jo ^ N = evS x κ * ∏ b, evS ![mv mu x b] jo := by
  have p : ∀ j : Fin n, GP (uP B j).val := gp_uP
  have e := ((exp_kappa hh hκ fun b => gp_smul (-1) (p b)).mul
    (IsExp.prod fun b => (exp_iota hh hj (p b)).pow N)).uniq hi
    ((exp_kappa hh hκ p).mul (IsExp.prod fun b => exp_iota hh hj (gp_mv mu p b))) (by
      simp only [mv_smul, ← Finset.smul_sum, Finset.sum_sub_distrib, smul_sub]
      abel)
  have := congrArg (evS x) e
  simp only [map_mul, map_prod, map_pow, evS_comp1] at this
  simpa only [evS_comp, map_smul, sL_mv, sL_uP] using this

theorem kappa_cube {Θ : PS V 3 d} (hΘ : IsTheta B K h w0 Θ) {n : ℕ} {mu : Matrix (Fin n) (Fin n) O} {N : ℕ}
    {κ : PS V n d} (hκ : IsKappa B K h w0 mu N κ) {m : ℕ} (x y z : Fin n → SP B m) :
    evS (fun b => x b + y b + z b) κ * evS x κ * evS y κ * evS z κ * ∏ b, evS ![x b, y b, z b] Θ ^ N =
      evS (fun b => x b + y b) κ * evS (fun b => x b + z b) κ * evS (fun b => y b + z b) κ *
        ∏ b, evS ![mv mu x b, mv mu y b, mv mu z b] Θ := by
  let q : Fin 3 → Fin n → SP B (3 * n) := fun t b => uP B (finProdFinEquiv (t, b))
  have p : ∀ t b, GP (q t b).val := fun t b => gp_uP _
  have e := (((((exp_kappa hh hκ fun b => gp_add (gp_add (p 0 b) (p 1 b)) (p 2 b)).mul
    (exp_kappa hh hκ (p 0))).mul (exp_kappa hh hκ (p 1))).mul (exp_kappa hh hκ (p 2))).mul
    (IsExp.prod fun b => (exp_theta hh hΘ (p 0 b) (p 1 b) (p 2 b)).pow N)).uniq hi
    ((((exp_kappa hh hκ fun b => gp_add (p 0 b) (p 1 b)).mul (exp_kappa hh hκ fun b => gp_add (p 0 b) (p 2 b))).mul
      (exp_kappa hh hκ fun b => gp_add (p 1 b) (p 2 b))).mul
      (IsExp.prod fun b => exp_theta hh hΘ (gp_mv mu (p 0) b) (gp_mv mu (p 1) b) (gp_mv mu (p 2) b))) (by
      simp only [mv_add, ← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, smul_sub, smul_add]
      abel)
  let a : Fin (3 * n) → SP B m := fun j => ![x, y, z] (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  have s : ∀ t b, sL a (q t b) = ![x, y, z] t b := fun t b => by
    simp only [q, a, sL_uP, Equiv.symm_apply_apply]
  have := congrArg (evS a) e
  simp only [map_mul, map_prod, map_pow, evS_comp3] at this
  simp only [evS_comp, map_add, sL_mv, s] at this
  exact this

end Logs

end GlobalTheory.PlaceInt.TrKappa

open GlobalTheory.PlaceInt.TrKappa in

theorem GlobalTheory.PlaceInt.prod_trUnit_mul_shift_kappa : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (Θ : PS V 3 d) (jo : PS V 1 d), IsTheta B K h w0 Θ → IsIota B K h w0 jo → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (N : ℕ), Odd N → (∀ j k, ∑ i, star (mu i j) * mu i k = if j = k then (N : O) else 0) → ∀ κ : PS V n d, IsKappa B K h w0 mu N κ → ∀ α ∈ kerM B mu, ∀ u : Fin n → PS V 1 d, (∀ b, TrUnit B Θ jo N (α b) (u b)) → (∏ b, evV (n := n) ![pt V d b] (u b)) * shift B.G.F α κ = κ := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ _ h w0 hh Θ jo hΘ hj n mu N hN hmu κ hκ α hα u hu
  have hi : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  obtain ⟨hs, hk⟩ := hα
  let a : Fin n → SP B n := fun b => cS B (α b) (hs b)
  have ca : ∀ (x : Fin n → SP B n) b, sL x (a b) = a b := fun x b => sL_cS x _ _
  let o : Fin 0 → SP B n := Fin.elim0
  have hk0 : ∀ b, mv mu a b = 0 := by
    intro b
    have e : mv mu (fun b => (cS B (α b) (hs b) : SP B 0)) b = 0 :=
      SP.ext ((congrFun (matV_val B mu fun b => (cS B (α b) (hs b) : SP B 0)) b).symm.trans (congrFun hk b))
    have := congrArg (sL o) e
    simpa only [sL_mv, sL_cS, map_zero] using this
  have hNa : ∀ j, (N : O) • a j = 0 := by
    intro j
    have e : ∑ i, star (mu i j) • mv mu a i = 0 := by simp only [hk0, smul_zero, Finset.sum_const_zero]
    simp only [mv, Finset.smul_sum, smul_smul] at e
    rw [Finset.sum_comm] at e
    simp only [← Finset.sum_smul, hmu, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at e
    exact e
  have hneg : ∀ j, (-1 : O) • a j + a j = 0 := fun j => by
    nth_rewrite 2 [← one_smul O (a j)]
    rw [← add_smul, neg_add_cancel, zero_smul]
  let ψ : PS V n d →+* PS V n d := evS fun b => uP B b + a b
  have hit : ∀ (k : ℕ) f, ψ^[k] f = evS (fun b => uP B b + (k : O) • a b) f := by
    intro k
    induction k with
    | zero => intro f; simp only [Nat.cast_zero, zero_smul, add_zero]; exact (evS_uP f).symm
    | succ k ih =>
      intro f
      rw [Function.iterate_succ_apply, ih]
      simp only [ψ, evS_comp, map_add, sL_uP, ca, Nat.cast_succ, add_smul, one_smul, add_assoc]
  haveI : IsDomain (PS V n d) := NoZeroDivisors.to_isDomain _
  haveI : CharZero (PS V n d) := (MvPowerSeries.C : V →+* PS V n d).charZero_iff (MvPowerSeries.C_injective) |>.1 inferInstance
  have goal := core ψ (evS fun _ => (0 : SP B n)) (evS a) (evS fun b => (-1 : O) • a b)
    (∏ b, evS ![uP B b] (u b)) κ (∏ b, evS ![uP B b, a b, a b] Θ ^ N) (∏ b, evS ![a b] jo ^ N) N hN
    (fun f => by simp only [ψ, evS_comp, map_zero]) (fun f => by simp only [ψ, evS_comp, ca])
    (fun f => by simp only [evS_comp, map_zero]) (fun f => by simp only [evS_comp, ca])
    (fun f => by simp only [evS_comp, map_zero])
    (fun f => by simp only [ψ, evS_comp, map_add, sL_uP, ca, zero_add])
    (fun f => by simp only [ψ, evS_comp, map_add, sL_uP, ca, hneg])
    (by
      have e := kappa_zero hi hh hκ (m := n)
      rw [evS_zero] at e
      rw [MvPowerSeries.isUnit_iff_constantCoeff]
      have := congrArg MvPowerSeries.constantCoeff e
      rw [MvPowerSeries.constantCoeff_C, map_one] at this
      rw [this]
      exact isUnit_one)
    (IsUnit.prod_univ_iff.2 fun b => (hu b).unit.map _)
    (kappa_zero hi hh hκ)
    (by rw [hit]; simp only [hNa, add_zero]; exact evS_uP κ)
    (by
      rw [iter_prod]
      refine Finset.prod_eq_one fun b _ => ?_
      rw [← map_iter (evS ![uP B b]) (shift B.G.F fun _ => α b) ψ _ (u b) N, (hu b).order, map_one]
      intro f
      have e : shift B.G.F (fun _ => α b) f = evS ![uP B 0 + cS B (α b) (hs b)] f := by
        rw [smallPointSubstitution_single_eq_constTerms, shift]
        congr 1
        funext j; fin_cases j; rfl
      rw [e]
      simp only [ψ, evS_comp1, map_add, sL_uP, sL_cS]
      rfl)
    (by
      have e := kappa_cube hi hh hΘ hκ (uP B) a a
      simp only [hk0, theta_zero hi hh hΘ, Finset.prod_const_one, _root_.mul_one, evS_uP] at e
      simp only [ψ, evS_comp, map_add, sL_uP, ca]
      exact e)
    (by
      simp only [map_prod, ψ, evS_comp1, sL_uP, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun b _ => ?_
      have e : evS ![uP B (0 : Fin 2) + uP B 1] (u b) * MvPowerSeries.C (MvPowerSeries.constantCoeff (u b)) =
          evS ![uP B 0] (u b) * evS ![uP B 1] (u b) * evS ![uP B 0, uP B 1, cS B (α b) (hs b)] Θ ^ N := by
        simp only [smallPointSubstitution_single_eq_constTerms, smallPointSubstitution_triple_eq_constTerms]
        exact (hu b).mul
      have := congrArg (evS ![uP B b, a b]) e
      simp only [map_mul, map_pow, evS_comp1, evS_comp3, map_add, sL_uP, sL_cS, evS_C] at this
      rw [evS_zero1]
      exact this)
    (by
      have e := kappa_neg hi hh hj hκ a
      simpa only [hk0, iota_zero hi hh hj, Finset.prod_const_one, _root_.mul_one] using e)
    (by
      simp only [map_prod, evS_comp1, sL_uP, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun b _ => ?_
      have e : MvPowerSeries.C (MvPowerSeries.constantCoeff (u b)) * evS ![(cS B (α b) (hs b) : SP B 0)] jo ^ N *
          evS ![(-1 : O) • (cS B (α b) (hs b) : SP B 0)] (u b) = 1 := by
        simp only [smallPointSubstitution_single_eq_constTerms]
        exact (hu b).sym
      have := congrArg (evS o) e
      simp only [map_mul, map_pow, evS_comp1, map_smul, sL_cS, evS_C, map_one] at this
      rw [evS_zero1]
      exact this)
  simp only [smallPointSubstitution_single_eq_constTerms] at goal
  simp only [ψ, evS_eq] at goal
  exact goal
