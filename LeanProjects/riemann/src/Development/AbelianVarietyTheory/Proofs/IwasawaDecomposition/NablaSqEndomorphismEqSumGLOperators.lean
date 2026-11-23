import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorDualRepDualHighestWeightAtEmbedding
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.FiniteDimensionalNablaSq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualWeylHighestWeightSpaceLineField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NablaDensity

theorem coeff_aeval_scale {k σ : Type} [Field k] (e : σ → k) (f : MvPolynomial σ k) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.aeval (fun v => MvPolynomial.C (e v) * MvPolynomial.X v) f) =
      (m.prod fun v j => e v ^ j) * MvPolynomial.coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    have hp : (u.prod fun i j => (MvPolynomial.C (e i) * MvPolynomial.X i : MvPolynomial σ k) ^ j) =
        MvPolynomial.C (u.prod fun v j => e v ^ j) * MvPolynomial.monomial u 1 := by
      calc (u.prod fun i j => (MvPolynomial.C (e i) * MvPolynomial.X i : MvPolynomial σ k) ^ j)
          = u.prod (fun i j => MvPolynomial.C (e i ^ j) * MvPolynomial.X i ^ j) := by
            simp only [mul_pow, MvPolynomial.C_pow]
        _ = MvPolynomial.C (u.prod fun i j => e i ^ j) *
              u.prod (fun i j => (MvPolynomial.X i : MvPolynomial σ k) ^ j) := by
            rw [Finsupp.prod_mul, map_finsuppProd]
        _ = MvPolynomial.C (u.prod fun v j => e v ^ j) * MvPolynomial.monomial u 1 := by
            rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
    have hmon : MvPolynomial.aeval (fun v => MvPolynomial.C (e v) * MvPolynomial.X v)
        (MvPolynomial.monomial u a : MvPolynomial σ k) =
        MvPolynomial.monomial u ((u.prod fun v j => e v ^ j) * a) := by
      rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, hp, MvPolynomial.C_mul_monomial,
        MvPolynomial.C_mul_monomial, mul_one, mul_comm]
    rw [hmon, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with hu
    · subst hu; rfl
    · simp
  | add p q hp hq => rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem rowAct_diagonal {k : Type} [Field k] {r c : ℕ} (d : Fin r → k) :
    Formalism.GradedWeylDivisibility.rowAct k (n := c) (Matrix.diagonal d) =
      MvPolynomial.aeval (fun v : Fin r × Fin c => MvPolynomial.C (d v.1) * MvPolynomial.X v) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, MvPolynomial.aeval_X, Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
  · simp

theorem prod_rowDeg {k : Type} [Field k] {r c : ℕ} (x : Fin r → k) (m : Fin r × Fin c →₀ ℕ) :
    (m.prod fun v j => x v.1 ^ j) = ∏ a, x a ^ Formalism.GradedWeylDivisibility.rowDeg m a := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  show ∏ y, x a ^ m (a, y) = _
  rw [Formalism.GradedWeylDivisibility.rowDeg, Finset.prod_pow_eq_pow_sum]

theorem coeff_sqAct_diag {k : Type} [Field k] {r : ℕ} (lam : DomWeight r) (t : Fin r → kˣ)
    (f : MvPolynomial (Fin r × Fin r) k) (m : Fin r × Fin r →₀ ℕ) :
    MvPolynomial.coeff m (sqAct k r lam (diagGL k r t) f) =
      (∏ a, (t a : k)) ^ lam.detShift * ((∏ a, (t a : k) ^ Formalism.GradedWeylDivisibility.rowDeg m a) * MvPolynomial.coeff m f) := by
  have e1 : ((diagGL k r t : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).transpose =
      Matrix.diagonal fun a => (t a : k) := by
    simp [diagGL]
  have e2 : ((Matrix.GeneralLinearGroup.det (diagGL k r t) : kˣ) : k) = ∏ a, (t a : k) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp [diagGL, Matrix.det_diagonal]
  unfold sqAct detPow
  rw [MvPolynomial.coeff_smul, e1, rowAct_diagonal, coeff_aeval_scale, prod_rowDeg (fun a => (t a : k)), smul_eq_mul,
    Units.val_zpow_eq_zpow_val, e2]

theorem weight_rowW_apply {r c : ℕ} (m : Fin r × Fin c →₀ ℕ) (a : Fin r) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r c) m a = Formalism.GradedWeylDivisibility.rowDeg m a := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type, Formalism.GradedWeylDivisibility.rowDeg, Finset.sum_comm]
  simp [Formalism.GradedWeylDivisibility.rowW, Pi.single_apply]

theorem weightLine : ∀ (k : Type) [Field k] [CharZero k] (N : ℕ) (lam : DomWeight N)
    (f : MvPolynomial (Fin N × Fin N) k), f ∈ nablaSq k N lam →
    (∀ t : Fin N → kˣ, sqAct k N lam (diagGL k N t) f = ((∏ a, t a ^ lam.w a : kˣ) : k) • f) →
    ∃ c : k, f = c • extremal k N lam := by
  intro k _ _ N lam f hf hwt
  classical
  have hhom : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f lam.natW := by
    intro m hm
    funext a
    rw [weight_rowW_apply]
    let u2 : kˣ := Units.mk0 2 two_ne_zero
    let t : Fin N → kˣ := Pi.mulSingle a u2
    have hpn : ∀ n : Fin N → ℕ, ∏ b, ((t b : kˣ) : k) ^ n b = 2 ^ n a := by
      intro n
      rw [Finset.prod_eq_single a]
      · simp [t, u2]
      · intro b _ hb
        simp [t, Pi.mulSingle_eq_of_ne hb]
      · simp
    have hp1 : ∏ b, ((t b : kˣ) : k) = 2 := by
      have := hpn (fun _ => 1)
      simpa using this
    have hpz : ((∏ b, t b ^ lam.w b : kˣ) : k) = 2 ^ lam.w a := by
      rw [Units.coe_prod]
      rw [Finset.prod_eq_single a]
      · simp [t, u2, Units.val_zpow_eq_zpow_val]
      · intro b _ hb
        simp [t, Pi.mulSingle_eq_of_ne hb]
      · simp
    have h1 := congrArg (MvPolynomial.coeff m) (hwt t)
    rw [coeff_sqAct_diag, MvPolynomial.coeff_smul, smul_eq_mul, hp1, hpn, hpz] at h1
    have h2 : (2 : k) ^ lam.detShift * 2 ^ Formalism.GradedWeylDivisibility.rowDeg m a = 2 ^ lam.w a := by
      have h1' : (2 : k) ^ lam.detShift * 2 ^ Formalism.GradedWeylDivisibility.rowDeg m a * MvPolynomial.coeff m f =
          2 ^ lam.w a * MvPolynomial.coeff m f := by
        rw [mul_assoc]; exact h1
      exact mul_right_cancel₀ hm h1'
    rw [← PI.WGB.natW_add_A lam a, zpow_add₀ two_ne_zero, zpow_natCast, mul_comm ((2 : k) ^ lam.natW a)] at h2
    have h3 : (2 : k) ^ Formalism.GradedWeylDivisibility.rowDeg m a = 2 ^ lam.natW a :=
      mul_left_cancel₀ (zpow_ne_zero _ two_ne_zero) h2
    have h4 : ((2 ^ Formalism.GradedWeylDivisibility.rowDeg m a : ℕ) : k) = ((2 ^ lam.natW a : ℕ) : k) := by
      push_cast; exact h3
    exact Nat.pow_right_injective le_rfl (Nat.cast_injective h4)
  exact GlobalTheory.Alc.hw_line_field k N lam.natW (PI.WGB.natW_anti_A lam) f hf hhom

variable (k : Type) [Field k] (N : ℕ) (lam : DomWeight N)

theorem sqAct_one (f : MvPolynomial (Fin N × Fin N) k) : sqAct k N lam 1 f = f := by
  have h1 : Formalism.GradedWeylDivisibility.rowAct k (n := N) (1 : Matrix (Fin N) (Fin N) k) =
      AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]
  simp [sqAct, detPow, h1]

def actL (g : GL (Fin N) k) : Module.End k (nablaSq k N lam) where
  toFun f := ⟨sqAct k N lam g f, (factSqStable k N lam g).1 f f.2⟩
  map_add' f f' := by
    apply Subtype.ext
    simp [sqAct, smul_add]
  map_smul' c f := by
    apply Subtype.ext
    simp [sqAct, smul_comm c]

theorem actL_coe (g : GL (Fin N) k) (f : nablaSq k N lam) :
    ((actL k N lam g f : nablaSq k N lam) : MvPolynomial (Fin N × Fin N) k) = sqAct k N lam g f := rfl

def rho : GL (Fin N) k →* Module.End k (nablaSq k N lam) where
  toFun := actL k N lam
  map_one' := by
    apply LinearMap.ext; intro f; apply Subtype.ext
    simp [actL_coe, sqAct_one]
  map_mul' g h := by
    apply LinearMap.ext; intro f; apply Subtype.ext
    simp only [Module.End.mul_apply, actL_coe]
    exact (factSqActMul k N lam g h f).1

def spanAlg : Subalgebra k (Module.End k (nablaSq k N lam)) :=
  Algebra.adjoin k (Set.range (rho k N lam))

instance spanAlg_tower : IsScalarTower k (spanAlg k N lam) (nablaSq k N lam) :=
  ⟨fun _ _ _ => rfl⟩

theorem spanAlg_smul (a : spanAlg k N lam) (v : nablaSq k N lam) :
    a • v = (a : Module.End k (nablaSq k N lam)) v := rfl

theorem rho_mem (g : GL (Fin N) k) : rho k N lam g ∈ spanAlg k N lam :=
  Algebra.subset_adjoin ⟨g, rfl⟩

theorem spanAlg_toSubmodule :
    Subalgebra.toSubmodule (spanAlg k N lam) = Submodule.span k (Set.range (rho k N lam)) := by
  rw [spanAlg, Algebra.adjoin_eq_span]
  congr 1
  rw [← MonoidHom.coe_mrange, Submonoid.closure_eq]

theorem extremal_mem : extremal k N lam ∈ nablaSq k N lam :=
  Formalism.GradedWeylDivisibility.hwMem k N N le_rfl lam.natW (PI.WGB.natW_anti_A lam)

theorem extremal_ne : extremal k N lam ≠ 0 :=
  Formalism.GradedWeylDivisibility.hwNe k N N le_rfl lam.natW

theorem nontrivial : Nontrivial (nablaSq k N lam) :=
  ⟨⟨⟨extremal k N lam, extremal_mem k N lam⟩, 0, fun h => extremal_ne k N lam (congrArg Subtype.val h)⟩⟩

theorem simple (hS : ∀ M : Submodule k (MvPolynomial (Fin N × Fin N) k), M ≤ nablaSq k N lam →
      (∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) → M = ⊥ ∨ M = nablaSq k N lam) :
    IsSimpleModule (spanAlg k N lam) (nablaSq k N lam) := by
  haveI := nontrivial k N lam
  refine { eq_bot_or_eq_top := fun S => ?_ }
  let M : Submodule k (MvPolynomial (Fin N × Fin N) k) :=
    (S.restrictScalars k).map (nablaSq k N lam).subtype
  have hMle : M ≤ nablaSq k N lam := by
    rintro _ ⟨v, _, rfl⟩
    exact v.2
  have hst : ∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M := by
    rintro g _ ⟨v, hv, rfl⟩
    refine ⟨rho k N lam g v, ?_, rfl⟩
    have := S.smul_mem (⟨rho k N lam g, rho_mem k N lam g⟩ : spanAlg k N lam) hv
    exact this
  rcases hS M hMle hst with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    have h2 : (v : MvPolynomial (Fin N × Fin N) k) ∈ M := ⟨v, hv, rfl⟩
    rw [h, Submodule.mem_bot] at h2
    rw [Submodule.mem_bot]
    exact Subtype.ext h2
  · right
    rw [eq_top_iff]
    intro v _
    have h2 : (v : MvPolynomial (Fin N × Fin N) k) ∈ M := by rw [h]; exact v.2
    obtain ⟨w, hw, hwv⟩ := h2
    have : w = v := Subtype.ext hwv
    exact this ▸ hw

theorem schur [CharZero k] (hS : ∀ M : Submodule k (MvPolynomial (Fin N × Fin N) k), M ≤ nablaSq k N lam →
      (∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) → M = ⊥ ∨ M = nablaSq k N lam)
    (ψ : nablaSq k N lam →ₗ[spanAlg k N lam] nablaSq k N lam) :
    ∃ c : k, ∀ v, ψ v = c • v := by
  have hsimp := simple k N lam hS
  have hcomm : ∀ g v, ψ (rho k N lam g v) = rho k N lam g (ψ v) := fun g v =>
    ψ.map_smul (⟨rho k N lam g, rho_mem k N lam g⟩ : spanAlg k N lam) v
  let h0 : nablaSq k N lam := ⟨extremal k N lam, extremal_mem k N lam⟩
  have hwt : ∀ t : Fin N → kˣ, sqAct k N lam (diagGL k N t) (ψ h0 : MvPolynomial (Fin N × Fin N) k) =
      ((∏ a, t a ^ lam.w a : kˣ) : k) • (ψ h0 : MvPolynomial (Fin N × Fin N) k) := by
    intro t
    have e1 : rho k N lam (diagGL k N t) h0 = ((∏ a, t a ^ lam.w a : kˣ) : k) • h0 :=
      Subtype.ext (GlobalTheory.AlgWtF.DDHw.sqAct_diag k N lam t)
    have e2 := hcomm (diagGL k N t) h0
    rw [e1, LinearMap.map_smul_of_tower] at e2
    have e3 := congrArg Subtype.val e2
    exact e3.symm
  obtain ⟨c, hc⟩ := weightLine k N lam _ (ψ h0).2 hwt
  refine ⟨c, fun w => ?_⟩
  let K : Submodule (spanAlg k N lam) (nablaSq k N lam) :=
    { carrier := {w | ψ w = c • w}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [map_add, ha, hb, smul_add]
      zero_mem' := by simp
      smul_mem' := by
        intro a x hx
        simp only [Set.mem_setOf_eq] at *
        rw [map_smul, hx, spanAlg_smul, spanAlg_smul, map_smul] }
  have hK0 : h0 ∈ K := Subtype.ext hc
  have hK : K = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
    · exfalso
      have : h0 ∈ (⊥ : Submodule (spanAlg k N lam) (nablaSq k N lam)) := h ▸ hK0
      rw [Submodule.mem_bot] at this
      exact extremal_ne k N lam (congrArg Subtype.val this)
    · exact h
  have : w ∈ K := hK ▸ Submodule.mem_top
  exact this

theorem mem_spanAlg [CharZero k] (hS : ∀ M : Submodule k (MvPolynomial (Fin N × Fin N) k), M ≤ nablaSq k N lam →
      (∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) → M = ⊥ ∨ M = nablaSq k N lam)
    (φ : Module.End k (nablaSq k N lam)) : φ ∈ spanAlg k N lam := by
  haveI := simple k N lam hS
  haveI := GlobalTheory.WeylDimGL.finiteDimensional_nablaSq k N lam
  let F : Module.End (Module.End (spanAlg k N lam) (nablaSq k N lam)) (nablaSq k N lam) :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := by
        intro ψ v
        obtain ⟨c, hc⟩ := schur k N lam hS ψ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  classical
  let b := Module.finBasis k (nablaSq k N lam)
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  have : (r : Module.End k (nablaSq k N lam)) = φ := by
    apply b.ext
    intro i
    have := hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [← spanAlg_smul]
    exact this.symm
  exact this ▸ r.2

end GlobalTheory.NablaDensity

open GlobalTheory.NablaDensity in

theorem GlobalTheory.NablaDensity.endo_eq_sum_sqAct : ∀ (k : Type) [Field k] [CharZero k] (N : ℕ) (lam : DomWeight N),
    (∀ M : Submodule k (MvPolynomial (Fin N × Fin N) k), M ≤ nablaSq k N lam →
      (∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) → M = ⊥ ∨ M = nablaSq k N lam) →
    ∀ φ : nablaSq k N lam →ₗ[k] nablaSq k N lam, ∃ (s : Finset (GL (Fin N) k)) (c : GL (Fin N) k → k),
      ∀ f : nablaSq k N lam, (φ f : MvPolynomial (Fin N × Fin N) k) = ∑ g ∈ s, c g • sqAct k N lam g f := by
  intro k _ _ N lam hS φ
  have hφ : φ ∈ Subalgebra.toSubmodule (spanAlg k N lam) := mem_spanAlg k N lam hS φ
  rw [spanAlg_toSubmodule, Finsupp.mem_span_range_iff_exists_finsupp] at hφ
  obtain ⟨c, hc⟩ := hφ
  refine ⟨c.support, c, fun f => ?_⟩
  rw [← hc, Finsupp.sum, LinearMap.sum_apply, Submodule.coe_sum]
  rfl
