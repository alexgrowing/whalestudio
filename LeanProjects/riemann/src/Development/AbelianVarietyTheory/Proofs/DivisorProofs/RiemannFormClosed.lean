import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartFormEquation

open Matrix Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl riem)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (hermMat eval₂ bas IsType Alt delAt dbarAt dz dzb coefwise)
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FlatClosed

variable {n : ℕ}

theorem sum_sym_ι_mul_eq_zero {M : Type} [AddCommGroup M] [Module ℂ M] (y : Fin n → M) (K : Fin n → Fin n → ℂ)
    (hK : ∀ c b, K c b = K b c) :
    ∑ c, ∑ b, K c b • (ExteriorAlgebra.ι ℂ (y c) * ExteriorAlgebra.ι ℂ (y b)) = 0 := by
  set T := ∑ c, ∑ b, K c b • (ExteriorAlgebra.ι ℂ (y c) * ExteriorAlgebra.ι ℂ (y b)) with hT
  have e : T = -T := by
    conv_lhs => rw [hT, Finset.sum_comm]
    rw [hT, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hK b c, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (y b) (y c)), smul_neg]
  have h2 : (2 : ℂ) • T = 0 := by
    rw [two_smul]; nth_rewrite 2 [e]; exact add_neg_cancel T
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem del_sum_eq_zero (D : Fin n → Fin n → Fin n → ℂ) (hD : ∀ c a b, D c a b = D a c b) :
    ∑ c, dz c * ∑ a, ∑ b, D c a b • (dz a * dzb b) = (0 : Alt n) := by
  have e : ∀ c, dz c * ∑ a, ∑ b, D c a b • (dz a * dzb b) = ∑ a, ∑ b, D c a b • (dz c * dz a * dzb b) := by
    intro c; simp only [Finset.mul_sum, mul_smul_comm, mul_assoc]
  simp only [e]
  have e2 : ∑ c, ∑ a, ∑ b, D c a b • (dz c * dz a * dzb b) =
      ∑ b, (∑ c, ∑ a, D c a b • (dz c * dz a)) * (dzb b : Alt n) := by
    simp only [Finset.sum_mul, smul_mul_assoc]
    exact (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm
  rw [e2]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [show (∑ c, ∑ a, D c a b • (dz c * dz a) : Alt n) = 0 from
    sum_sym_ι_mul_eq_zero (fun c => (Pi.single (Sum.inl c) 1 : Fin n ⊕ Fin n → ℂ)) (fun c a => D c a b)
      (fun c a => hD c a b), zero_mul]

theorem dbar_sum_eq_zero (E : Fin n → Fin n → Fin n → ℂ) (hE : ∀ c a b, E c a b = E b a c) :
    ∑ c, dzb c * ∑ a, ∑ b, E c a b • (dz a * dzb b) = (0 : Alt n) := by
  have sw : ∀ c a, (dzb c * dz a : Alt n) = -(dz a * dzb c) := fun c a =>
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  have e : ∀ c, dzb c * ∑ a, ∑ b, E c a b • (dz a * dzb b) = ∑ a, ∑ b, -(E c a b • (dz a * (dzb c * dzb b))) := by
    intro c; simp only [Finset.mul_sum, mul_smul_comm, ← mul_assoc, sw, neg_mul, smul_neg]
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  have e2 : ∑ c, ∑ b, -(E c a b • (dz a * (dzb c * dzb b))) =
      -(dz a * ∑ c, ∑ b, E c a b • (dzb c * dzb b) : Alt n) := by
    simp only [Finset.mul_sum, mul_smul_comm, Finset.sum_neg_distrib]
  rw [e2, show (∑ c, ∑ b, E c a b • (dzb c * dzb b) : Alt n) = 0 from
    sum_sym_ι_mul_eq_zero (fun c => (Pi.single (Sum.inr c) 1 : Fin n ⊕ Fin n → ℂ)) (fun c b => E c a b)
      (fun c b => hE c a b), mul_zero, neg_zero]

theorem repr_pair_eq (β : Alt n) (a b : Fin n) :
    (bas n).repr β {a.castAdd n, b.natAdd n} = (eval₂ β (coordVec a) (coordVec b) -
      Complex.I * eval₂ β (Complex.I • coordVec a) (coordVec b)) / 2 := by
  have e (x y : Fin n) : (Pi.single x (1 : ℂ) : Fin n → ℂ) ⬝ᵥ hermMat β *ᵥ star (Pi.single y (1 : ℂ) : Fin n → ℂ) =
      hermMat β x y := HermFrame.form_single _ _ _
  simp only [eval₂, HermFrame.form, WithLp.ofLp_smul, EuclideanSpace.ofLp_single, star_smul, mulVec_smul,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, Complex.star_def, Complex.conj_I, e]
  simp only [hermMat, Matrix.of_apply]
  linear_combination ((2 - Complex.I ^ 2) / 2 * (bas n).repr β {a.castAdd n, b.natAdd n}
    - Complex.I ^ 2 / 2 * (bas n).repr β {b.castAdd n, a.natAdd n}) * Complex.I_sq

theorem eval₂_I_I (β : Alt n) (ξ η : V n) : eval₂ β (Complex.I • ξ) (Complex.I • η) = eval₂ β ξ η := by
  simp only [eval₂, HermFrame.form, WithLp.ofLp_smul]
  simp only [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, Complex.star_def, Complex.conj_I]
  linear_combination (Complex.I * (η.ofLp ⬝ᵥ hermMat β *ᵥ star ξ.ofLp - ξ.ofLp ⬝ᵥ hermMat β *ᵥ star η.ofLp)) *
    Complex.I_sq

section Sym
open Complex
variable {E : Type} [AddCommGroup E] [Module ℂ E] (D : E → E → E → ℝ)
  (hc : ∀ w x y, D w x y + D x y w + D y w x = 0) (ha : ∀ w x y, D w x y = -D w y x)
  (hJ : ∀ w x y, D w (I • x) (I • y) = D w x y) (hK : ∀ w x y, D w (I • x) y = -D w x (I • y))
include hc ha hJ hK

theorem sym_del (a b c : E) : D c a b - D (I • c) (I • a) b = D a c b - D (I • a) (I • c) b ∧
    D c (I • a) b + D (I • c) a b = D a (I • c) b + D (I • a) c b :=
  ⟨by linarith [hc c a b, ha a c b, hc (I • c) (I • a) b, ha (I • a) (I • c) b, hJ b c a],
    by linarith [hc c (I • a) b, ha (I • a) c b, hc (I • c) a b, ha a (I • c) b, hK b c a]⟩

theorem sym_dbar (a b c : E) : D c a b + D (I • c) (I • a) b = D b a c + D (I • b) (I • a) c ∧
    D (I • c) a b - D c (I • a) b = D (I • b) a c - D b (I • a) c :=
  ⟨by linarith [hc c a b, ha b a c, hK (I • c) a b, hK (I • b) a c, ha (I • b) a (I • c), hc (I • c) a (I • b),
      hJ a b c],
    by linarith [hK c a b, hK b a c, hc (I • c) a b, ha b (I • c) a, hc (I • b) a c, ha c (I • b) a, hK a c b,
      ha a (I • c) b]⟩

end Sym

theorem coefwise_eq {v : V n} {T : (V n → ℂ) → ℂ} (h₁ : ∀ f g, f =ᶠ[𝓝 v] g → T f = T g)
    (h₂ : ∀ (k : Fin n × Fin n → ℂ) (f : Fin n × Fin n → V n → ℂ), (∀ i, DifferentiableAt ℝ (f i) v) →
      T (fun u => ∑ i, k i • f i u) = ∑ i, k i • T (f i))
    {α : V n → Alt n} {c : Fin n → Fin n → V n → ℂ} (hc : ∀ a b, DifferentiableAt ℝ (c a b) v)
    (h : ∀ᶠ u in 𝓝 v, α u = ∑ a, ∑ b, c a b u • (dz a * dzb b)) :
    coefwise T α = ∑ a, ∑ b, T (c a b) • (dz a * dzb b) := by
  have e (S) : T (fun u => (bas n).repr (α u) S) =
      ∑ i : Fin n × Fin n, (bas n).repr (dz i.1 * dzb i.2) S • T (c i.1 i.2) := by
    rw [← h₂ _ (fun i => c i.1 i.2) fun i => hc _ _]
    refine h₁ _ _ (h.mono fun u hu => ?_)
    simp only [hu, map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
      mul_comm]
  refine (bas n).repr.injective (Finsupp.ext fun S => ?_)
  rw [coefwise, (bas n).repr_sum_self, e]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
      mul_comm]

variable {g : ℕ}

theorem riem_swap (x y : Fl g) : riem x y = -riem y x := by
  simp only [riem, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem riem_neg (x y : Fl g) : riem (-x) y = -riem x y := by
  simp only [riem, ← Finset.sum_neg_distrib, Pi.neg_apply]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem riem_fderiv {X : V n → Fl g} {v : V n} (hX : ContDiffAt ℝ ∞ X v) (x y : V n) :
    DifferentiableAt ℝ (fun u => riem (fderiv ℝ X u x) (fderiv ℝ X u y)) v ∧
    ∀ w, fderiv ℝ (fun u => riem (fderiv ℝ X u x) (fderiv ℝ X u y)) v w =
      riem (fderiv ℝ (fderiv ℝ X) v w x) (fderiv ℝ X v y) + riem (fderiv ℝ X v x) (fderiv ℝ (fderiv ℝ X) v w y) := by
  have hD : HasFDerivAt (fderiv ℝ X) (fderiv ℝ (fderiv ℝ X) v) v :=
    ((hX.fderiv_right (m := 1) (WithTop.coe_le_coe.2 (le_top (a := (2 : ℕ∞))))).differentiableAt one_ne_zero).hasFDerivAt
  have h (z : V n) (k : Fin g ⊕ Fin g) : HasFDerivAt (fun u => fderiv ℝ X u z k) _ v :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g ⊕ Fin g => ℝ) k).comp
      (ContinuousLinearMap.apply ℝ (Fl g) z)).hasFDerivAt.comp v hD
  have H : HasFDerivAt (fun u => riem (fderiv ℝ X u x) (fderiv ℝ X u y)) _ v :=
    HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      ((h x (.inr i)).fun_mul (h y (.inl i))).fun_sub ((h x (.inl i)).fun_mul (h y (.inr i)))
  refine ⟨H.differentiableAt, fun w => ?_⟩
  rw [H.fderiv]
  simp only [riem, ← Finset.sum_add_distrib, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  ring

theorem del_dbar_comb {p q : V n → ℝ} {v : V n} (hp : DifferentiableAt ℝ p v) (hq : DifferentiableAt ℝ q v) :
    DifferentiableAt ℝ (fun u => ((p u : ℂ) - Complex.I * q u) / 2) v ∧ ∀ w,
    GlobalTheory.del (fun u => ((p u : ℂ) - Complex.I * q u) / 2) v w =
      (((fderiv ℝ p v w - fderiv ℝ q v (Complex.I • w) : ℝ) : ℂ) -
        Complex.I * ((fderiv ℝ q v w + fderiv ℝ p v (Complex.I • w) : ℝ) : ℂ)) / 4 ∧
    GlobalTheory.dbar (fun u => ((p u : ℂ) - Complex.I * q u) / 2) v w =
      (((fderiv ℝ p v w + fderiv ℝ q v (Complex.I • w) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ p v (Complex.I • w) - fderiv ℝ q v w : ℝ) : ℂ)) / 4 := by
  have h₁ : HasFDerivAt (fun u => (p u : ℂ)) _ v := Complex.ofRealCLM.hasFDerivAt.comp v hp.hasFDerivAt
  have h₂ : HasFDerivAt (fun u => (q u : ℂ)) _ v := Complex.ofRealCLM.hasFDerivAt.comp v hq.hasFDerivAt
  have H : HasFDerivAt (fun u => ((p u : ℂ) - Complex.I * q u) / 2) _ v :=
    ((h₁.fun_sub (h₂.const_mul Complex.I)).mul_const (2 : ℂ)⁻¹).congr_of_eventuallyEq
      (Eventually.of_forall fun u => div_eq_mul_inv _ _)
  refine ⟨H.differentiableAt, fun w => ?_⟩
  rw [GlobalTheory.del_apply, GlobalTheory.dbar_apply, H.fderiv]
  constructor <;> simp <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem closed_of_eq_riem : ∀ (n g : ℕ) (X : V n → Fl g) (α : V n → Alt n) (v : V n), ContDiffAt ℝ ∞ X v →
    (∀ᶠ u in 𝓝 v, IsType 1 1 (α u) ∧ ∀ ξ ζ : V n,
      eval₂ (α u) ξ ζ = (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.riem (fderiv ℝ X u ξ) (fderiv ℝ X u ζ) : ℝ)) →
    delAt α v = 0 ∧ dbarAt α v = 0 := by
  intro n g X α v hX h
  set f : V n → V n → V n → ℝ := fun x y u => riem (fderiv ℝ X u x) (fderiv ℝ X u y) with hf
  have hs := hX.isSymmSndFDerivAt (by simpa using WithTop.coe_le_coe.2 (le_top (a := (2 : ℕ∞))))
  have hd (x y : V n) : DifferentiableAt ℝ (f x y) v := (riem_fderiv hX x y).1
  have hF (w x y : V n) : fderiv ℝ (f x y) v w = _ := (riem_fderiv hX x y).2 w
  have hc (w x y : V n) : fderiv ℝ (f x y) v w + fderiv ℝ (f y w) v x + fderiv ℝ (f w x) v y = 0 := by
    rw [hF, hF, hF, hs.eq y w, hs.eq x w, hs.eq y x, riem_swap (fderiv ℝ X v x), riem_swap (fderiv ℝ X v y),
      riem_swap (fderiv ℝ X v w)]
    ring
  have ha (w x y : V n) : fderiv ℝ (f x y) v w = -fderiv ℝ (f y x) v w := by
    rw [hF, hF, riem_swap (fderiv ℝ X v x), riem_swap (fderiv ℝ X v y)]
    ring
  have hJ (w x y : V n) : fderiv ℝ (f (Complex.I • x) (Complex.I • y)) v w = fderiv ℝ (f x y) v w := by
    rw [Filter.EventuallyEq.fderiv_eq (f := f x y) (h.mono fun u hu => ?_)]
    exact Complex.ofReal_injective (by rw [← hu.2, ← hu.2, eval₂_I_I])
  have hK (w x y : V n) : fderiv ℝ (f (Complex.I • x) y) v w = -fderiv ℝ (f x (Complex.I • y)) v w := by
    rw [← hJ, GlobalTheory.I_smul_I_smul, hF, hF, map_neg, map_neg, riem_neg, riem_neg]
    ring
  have hα : ∀ᶠ u in 𝓝 v, α u = ∑ a, ∑ b, (((f (coordVec a) (coordVec b) u : ℂ) -
      Complex.I * f (Complex.I • coordVec a) (coordVec b) u) / 2) • (dz a * dzb b) := h.mono fun u hu => by
    conv_lhs => rw [GlobalTheory.TotalPos.eq_sum_of_isType hu.1]
    simp only [repr_pair_eq, hu.2, hf]
  have key (a b : Fin n) := del_dbar_comb (hd (coordVec a) (coordVec b)) (hd (Complex.I • coordVec a) (coordVec b))
  constructor
  · have e (c : Fin n) := coefwise_eq (T := fun f => GlobalTheory.del f v (coordVec c)) (fun _ _ e => by rw [GlobalTheory.del_congr e])
      (fun k f hf => by
        rw [GlobalTheory.del_sum fun i _ => (hf i).fun_const_smul (k i), ContinuousLinearMap.sum_apply]
        exact Finset.sum_congr rfl fun i _ => by rw [GlobalTheory.del_const_smul _ (hf i)]; rfl) (fun a b => (key a b).1) hα
    simp only [delAt, e]
    refine del_sum_eq_zero _ fun c a b => ?_
    have := sym_del (fun w x y => fderiv ℝ (f x y) v w) hc ha hJ hK (coordVec a) (coordVec b) (coordVec c)
    rw [((key a b).2 _).1, ((key c b).2 _).1, this.1, this.2]
  · have e (c : Fin n) := coefwise_eq (T := fun f => GlobalTheory.dbar f v (coordVec c)) (fun _ _ e => by rw [GlobalTheory.dbar_congr e])
      (fun k f hf => by
        rw [GlobalTheory.dbar_sum fun i _ => (hf i).fun_const_smul (k i), ContinuousLinearMap.sum_apply]
        exact Finset.sum_congr rfl fun i _ => by rw [GlobalTheory.dbar_const_smul _ (hf i)]; rfl) (fun a b => (key a b).1) hα
    simp only [dbarAt, e]
    refine dbar_sum_eq_zero _ fun c a b => ?_
    have := sym_dbar (fun w x y => fderiv ℝ (f x y) v w) hc ha hJ hK (coordVec a) (coordVec b) (coordVec c)
    rw [((key a b).2 _).2, ((key a c).2 _).2, this.1, this.2]

end GlobalTheory.FlatClosed
