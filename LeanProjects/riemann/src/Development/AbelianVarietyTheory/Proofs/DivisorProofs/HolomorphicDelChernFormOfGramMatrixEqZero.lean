import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtHolomorphicFrameChange
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.ChernDel

variable {n : ℕ}

theorem del_del_comm {u : V n → ℂ} {z : V n} (hu : ContDiffAt ℝ 2 u z) (ξ η : V n) :
    del (fun x => del u x ξ) z η = del (fun x => del u x η) z ξ := by
  have h := differentiableAt_fderiv_of_contDiffAt_two hu
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have key : ∀ a b : V n, del (fun x => del u x a) z b = (1 / 2 : ℂ) • (del (fun x => fderiv ℝ u x a) z b -
      Complex.I • del (fun x => fderiv ℝ u x (Complex.I • a)) z b) := by
    intro a b
    simp only [del_apply u]
    rw [del_const_smul _ ((h1 _).fun_sub ((h1 _).fun_const_smul Complex.I)),
      del_sub (h1 _) ((h1 _).fun_const_smul Complex.I), del_const_smul _ (h1 _)]
    rfl
  rw [key, key]
  simp only [del_apply, fderiv_fderiv_apply hu, hs.eq ξ, hs.eq (Complex.I • ξ), smul_eq_mul]
  ring

section Mat

variable {r : Type} [Fintype r] [DecidableEq r]

theorem mdel_conn {H : V n → Matrix r r ℂ} {z : V n} (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : V n) :
    mdel (fun x => conn H x ξ) z η = mdel (fun x => conn H x η) z ξ +
      (conn H z ξ * conn H z η - conn H z η * conn H z ξ) := by
  have h1 : MContDiffAt 1 H z := h.of_le one_le_two
  have hu' : IsUnit (H z)ᵀ.det := by rwa [det_transpose]
  have hc : mdel (fun x => mdel H x ξ) z η = mdel (fun x => mdel H x η) z ξ := by
    ext a b; exact del_del_comm (h a b) ξ η
  simp only [conn]
  rw [mdel_mul (h1.transpose.inv hu') (h.mdel (by norm_num) ξ).transpose,
    mdel_mul (h1.transpose.inv hu') (h.mdel (by norm_num) η).transpose,
    mdel_inv h1.transpose hu', mdel_inv h1.transpose hu', mdel_transpose (fun x => mdel H x ξ),
    mdel_transpose (fun x => mdel H x η), hc, mdel_transpose, mdel_transpose]
  simp only [Matrix.neg_mul, Matrix.mul_assoc]
  abel

theorem mdel_curv_comm {H : V n → Matrix r r ℂ} {z : V n} (h : MContDiffAt 3 H z) (hu : IsUnit (H z).det)
    {ξ η : V n} (hξ : conn H z ξ = 0) (hη : conn H z η = 0) (ζ : V n) :
    mdel (fun x => curv H x ξ ζ) z η = mdel (fun x => curv H x η ζ) z ξ := by
  have h2 : MContDiffAt 2 H z := h.of_le (by norm_num)
  have c2 : ∀ a, MContDiffAt 2 (fun x => conn H x a) z := fun a => h.conn hu (by norm_num) a
  have c1 : ∀ a, MContDiffAt 1 (fun x => conn H x a) z := fun a => (c2 a).of_le one_le_two
  have he : (fun x => mdel (fun y => conn H y ξ) x η) =ᶠ[𝓝 z] fun x => mdel (fun y => conn H y η) x ξ +
      (conn H x ξ * conn H x η + -(conn H x η * conn H x ξ)) := by
    filter_upwards [h2.eventually_two, h2.eventually_isUnit hu] with x h3 h4
    rw [mdel_conn h3 h4, sub_eq_add_neg]
  simp only [curv]
  rw [mdel_neg, mdel_neg, mdel_mdbar (c2 ξ), mdel_mdbar (c2 η), ← mdbar_mdel (c2 ξ), ← mdbar_mdel (c2 η),
    mdbar_congr he, mdbar_add ((c2 η).mdel (by norm_num) ξ) (((c1 ξ).mul (c1 η)).add ((c1 η).mul (c1 ξ)).neg),
    mdbar_add ((c1 ξ).mul (c1 η)) ((c1 η).mul (c1 ξ)).neg, mdbar_neg, mdbar_mul (c1 ξ) (c1 η),
    mdbar_mul (c1 η) (c1 ξ), hξ, hη]
  simp

end Mat

theorem delAt_congr {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : delAt α v = delAt β v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  exact congrArg (fun L => L (coordVec a) • bas n S)
    (GlobalTheory.del_congr (f := fun x => (bas n).repr (α x) S) (g := fun x => (bas n).repr (β x) S)
      (h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx))

theorem delAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {u : ι → V n → ℂ} (hu : ∀ i, DifferentiableAt ℝ (u i) v)
    (α : ι → Alt n) :
    delAt (fun x => ∑ i, u i x • α i) v = ∑ c, ∑ i, del (u i) v (coordVec c) • (dz c * α i) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  have : coefwise (fun f => del f v (coordVec c)) (fun x => ∑ i, u i x • α i) =
      ∑ i, del (u i) v (coordVec c) • α i := by
    refine (bas n).ext_elem fun S => ?_
    rw [FormMul.repr_coefwise]
    simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [del_sum fun i _ => (hu i).mul_const _, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [del_mul (hu i) (differentiableAt_const _), del_const]
    simp
  rw [this, Finset.mul_sum]
  simp only [mul_smul_comm]

theorem delAt_add {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    delAt (fun x => F x + G x) v = delAt F v + delAt G v := by
  rw [delAt, delAt, delAt, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_add]
  congr 1
  refine (bas n).ext_elem fun S => ?_
  simp only [map_add, Finsupp.add_apply, FormMul.repr_coefwise]
  rw [del_add (hF S) (hG S), ContinuousLinearMap.add_apply]

theorem delAt_const (α : Alt n) (v : V n) : delAt (fun _ => α) v = 0 := by
  simp [delAt, coefwise]

def closedAt (v : V n) : Subalgebra ℂ (V n → Ev n) where
  carrier := {F | (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x : Alt n) S) v) ∧
    delAt (fun x => (F x : Alt n)) v = 0}
  mul_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · simp only [Pi.mul_apply, Subalgebra.coe_mul, FormMul.repr_mul (F _ : Alt n)]
      exact DifferentiableAt.fun_sum fun p _ => ((hF p.1).mul (hG p.2)).mul_const _
    · obtain ⟨y, hy⟩ := FormMul.delAt_mul hF hG
      simp only [Pi.mul_apply, Subalgebra.coe_mul]
      rw [hy, hF0, hG0, zero_mul, mul_zero, add_zero]
  add_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · simp only [Pi.add_apply, Subalgebra.coe_add, map_add, Finsupp.add_apply]
      exact (hF S).add (hG S)
    · simp only [Pi.add_apply, Subalgebra.coe_add]
      rw [delAt_add hF hG, hF0, hG0, add_zero]
  algebraMap_mem' c := ⟨fun S => differentiableAt_const ((bas n).repr (algebraMap ℂ (Ev n) c : Alt n) S),
    delAt_const (algebraMap ℂ (Ev n) c : Alt n) v⟩

theorem mem_closedAt {v : V n} {F : V n → Ev n} : F ∈ closedAt v ↔
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x : Alt n) S) v) ∧ delAt (fun x => (F x : Alt n)) v = 0 :=
  Iff.rfl

theorem coeff_charpolyRev_map {R S r : Type} [CommRing R] [CommRing S] [Fintype r] [DecidableEq r] (f : R →+* S)
    (M : Matrix r r R) (j : ℕ) : (M.map f).charpolyRev.coeff j = f (M.charpolyRev.coeff j) := by
  rw [← Polynomial.coeff_map]
  congr 1
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  simp [Matrix.one_apply, apply_ite (Polynomial.map f)]

theorem mem_closedAt_of_symm {v : V n} {u : Fin n × Fin n → V n → ℂ} (hu : ∀ p, DifferentiableAt ℝ (u p) v)
    (hs : ∀ a b c, del (u (a, b)) v (coordVec c) = del (u (c, b)) v (coordVec a)) :
    (fun x => ∑ p, u p x • sym p) ∈ closedAt v := by
  refine mem_closedAt.2 ⟨fun S => ?_, ?_⟩
  · simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, map_sum, map_smul, Finsupp.finset_sum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    exact DifferentiableAt.fun_sum fun p _ => (hu p).mul_const _
  · simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul]
    rw [delAt_sum_smul hu]
    simp only [Fintype.sum_prod_type]
    set T : Alt n := ∑ c, ∑ a, ∑ b, del (u (a, b)) v (coordVec c) • (dz c * (sym (a, b) : Alt n)) with hT
    have h2 : T = -T := by
      conv_rhs => rw [hT, Finset.sum_comm]
      rw [hT]
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hs a b c, ← smul_neg]
      congr 1
      show dz c * (dz a * dzb b) = -(dz a * (dz c * dzb b))
      rw [← mul_assoc, ← mul_assoc, ← neg_mul]
      congr 1
      exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    have h3 : (2 : ℂ) • T = 0 := by rw [two_smul]; nth_rewrite 2 [h2]; exact add_neg_cancel T
    exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

variable {r : Type} [Fintype r] [DecidableEq r]

theorem delAt_chernAt_of_conn_eq_zero {H : V n → Matrix r r ℂ} {v : V n} (h : MContDiffAt 3 H v)
    (hu : IsUnit (H v).det) (h0 : ∀ a, conn H v (coordVec a) = 0) (j : ℕ) :
    delAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  have hm : ∀ i k, (fun x => ∑ p : Fin n × Fin n, curv H x (coordVec p.1) (coordVec p.2) i k • sym p) ∈ closedAt v :=
    fun i k => mem_closedAt_of_symm (u := fun p x => curv H x (coordVec p.1) (coordVec p.2) i k)
      (fun p => (h.curv hu (j := 1) (by norm_num) _ _).diff i k)
      fun a b c => congrFun (congrFun (mdel_curv_comm h hu (h0 a) (h0 c) (coordVec b)) i) k
  let M : Matrix r r (closedAt v) := Matrix.of fun i k => ⟨_, hm i k⟩
  have e : (fun w => chernAt H w j) = (kappa ^ j • (-M).charpolyRev.coeff j : closedAt v) := by
    funext w
    let ev : closedAt v →+* Ev n := (Pi.evalRingHom (fun _ => Ev n) w).comp (closedAt v).val.toRingHom
    have e1 := coeff_charpolyRev_map ev (-M) j
    have e2 := coeff_charpolyRev_map (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toRingHom (-curvPoly H w) j
    have e3 : (-M).map ev = (-curvPoly H w).map (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toRingHom := by
      ext i k : 2
      simp only [Matrix.map_apply, Matrix.neg_apply, map_neg]
      congr 1
      simp [M, ev, curvPoly, Fintype.sum_prod_type, Algebra.smul_def]
    rw [e3, e2] at e1
    show kappa ^ j • _ = kappa ^ j • ev _
    rw [← e1]
    rfl
  have := (kappa ^ j • (-M).charpolyRev.coeff j : closedAt v).2
  rw [← e] at this
  exact (mem_closedAt.1 this).2

theorem delAt_chernAt : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s, delAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  intro n r _ _ H s hs hH hu j v hv
  have h3 : MContDiffAt 3 H v := fun a b => ((hH a b).contDiffAt (hs.mem_nhds hv)).of_le (by norm_cast)
  have h2 : MContDiffAt 2 H v := h3.of_le (by norm_num)
  let L : r → r → V n →L[ℂ] ℂ := fun i k => ∑ a, conn H v (coordVec a) i k • EuclideanSpace.proj a
  let A : V n → Matrix r r ℂ := fun w => Matrix.of fun i k => (1 : Matrix r r ℂ) i k + L i k v - L i k w
  have hAv : A v = 1 := by ext i k; simp [A]
  have hAa : ∀ w i k, AnalyticAt ℂ (fun w => A w i k) w := fun w i k => analyticAt_const.sub ((L i k).analyticAt w)
  have hA3 : MContDiffAt 3 A v := fun i k => (hAa v i k).contDiffAt.restrict_scalars ℝ
  have hAu : IsUnit (A v).det := by rw [hAv, det_one]; exact isUnit_one
  have hA0 : ∀ η, mdbar A v η = 0 := fun η => by
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hAa v a b).differentiableAt]
    rfl
  have hAd : ∀ c, mdel A v (coordVec c) = -conn H v (coordVec c) := fun c => by
    ext i k
    rw [mdel_apply, del_eq_fderiv (hAa v i k).differentiableAt]
    have : HasFDerivAt (fun w => A w i k) (-L i k) v := (L i k).hasFDerivAt.const_sub _
    rw [this.fderiv]
    simp [L, Pi.single_apply]
  have hK : MContDiffAt 3 (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) v :=
    (hA3.transpose.mul h3).mul hA3.conjTranspose.transpose
  have hKu : IsUnit ((A v)ᵀ * H v * (A v)ᴴᵀ).det := by simpa [hAv] using hu v hv
  have he : (fun w => (chernAt H w j : Alt n)) =ᶠ[𝓝 v]
      fun w => (chernAt (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) w j : Alt n) := by
    filter_upwards [h2.eventually_two, h2.eventually_isUnit (hu v hv), hA3.eventually_isUnit hAu] with w a1 a2 a3
    rw [chernAt_changeFrame (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) H A w a1 a2 (hAa w) a3
      (Eventually.of_forall fun _ => rfl) j]
  rw [delAt_congr he]
  refine delAt_chernAt_of_conn_eq_zero hK hKu (fun a => ?_) j
  rw [conn_changeFrame (h3.of_le (by norm_num)) (hu v hv) (hA3.of_le (by norm_num)) hAu hA0, hAd, hAv]
  simp

end GlobalTheory.CxForm.ChernDel
