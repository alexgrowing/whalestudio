import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

def thetaLinForm {g : ℕ} (n : Fin g → ℤ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun z := -(2 * Real.pi * Complex.I) * (ofIntVec n ⬝ᵥ z)
  map_add' z w := by rw [dotProduct_add, mul_add]
  map_smul' c z := by simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply]; ring

theorem thetaLinForm_apply {g : ℕ} (n : Fin g → ℤ) (z : Fin g → ℂ) :
    thetaLinForm n z = -(2 * Real.pi * Complex.I) * (ofIntVec n ⬝ᵥ z) := rfl

theorem autFactor_eq_zero_mul_exp {g : ℕ} (a b : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ) (n n' : Fin g → ℤ)
    (z : Fin g → ℂ) : autFactor a b τ n n' z = autFactor a b τ n n' 0 * cexp (thetaLinForm n z) := by
  have key : ∀ x y : ℂ, eC (x - y) = eC x * cexp (-(2 * Real.pi * Complex.I) * y) := by
    intro x y
    rw [eC, eC, ← Complex.exp_add]
    congr 1
    ring
  simp only [autFactor]
  rw [key (-(ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n)) / 2) (ofIntVec n ⬝ᵥ z), dotProduct_zero, sub_zero,
    thetaLinForm_apply]
  ring

theorem autFactor_ne_zero' {g : ℕ} (a b : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ) (n n' : Fin g → ℤ)
    (z : Fin g → ℂ) : autFactor a b τ n n' z ≠ 0 := by
  simp only [autFactor, eC]
  exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

theorem ofIntVec_single' {g : ℕ} (i : Fin g) : ofIntVec (Pi.single i 1 : Fin g → ℤ) = Pi.single i 1 := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [ofIntVec]
  · simp [ofIntVec, h]

theorem linForm_eq_dotProduct {g : ℕ} (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ) (z : Fin g → ℂ) :
    lam z = (fun i => lam (Pi.single i 1)) ⬝ᵥ z := by
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [map_sum]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : (Pi.single i (z i) : Fin g → ℂ) = z i • Pi.single i 1 := by
    ext j
    rcases eq_or_ne j i with rfl | h
    · simp
    · simp [h]
  rw [hs, map_smul, smul_eq_mul, mul_comm]

theorem two_pi_I_ne_zero' : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

theorem mem_periodLattice_of_exp_thetaLinForm {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (w : Fin g → ℂ) (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ n n' : Fin g → ℤ, cexp (thetaLinForm n w) = cexp (lam (τ *ᵥ ofIntVec n + ofIntVec n'))) :
    w ∈ periodLattice τ := by

  have hk : ∀ j, ∃ k : ℤ, lam (Pi.single j 1) = k * (2 * Real.pi * Complex.I) := by
    intro j
    have hj := h 0 (Pi.single j 1)
    rw [thetaLinForm_apply, ofIntVec_zero, zero_dotProduct, mul_zero, Complex.exp_zero, mulVec_zero,
      zero_add, ofIntVec_single'] at hj
    exact Complex.exp_eq_one_iff.mp hj.symm
  choose k hk using hk

  have hm : ∀ i, ∃ m : ℤ, -(2 * Real.pi * Complex.I) * w i =
      (2 * Real.pi * Complex.I) * (τ *ᵥ ofIntVec k) i + m * (2 * Real.pi * Complex.I) := by
    intro i
    have hi := h (Pi.single i 1) 0
    rw [thetaLinForm_apply, ofIntVec_single', single_dotProduct, _root_.one_mul, ofIntVec_zero, add_zero,
      linForm_eq_dotProduct lam] at hi
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hi
    refine ⟨m, ?_⟩
    rw [hm]
    congr 1
    simp only [dotProduct, mulVec, hk, ofIntVec, Pi.single_apply, mul_ite, _root_.mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hτ.apply i j]
    ring
  choose m hm using hm
  refine ⟨-k, -m, funext fun i => ?_⟩
  rw [ofIntVec_neg, ofIntVec_neg, mulVec_neg]
  show w i = -(τ *ᵥ ofIntVec k) i + -((m i : ℤ) : ℂ)
  apply mul_left_cancel₀ two_pi_I_ne_zero'
  linear_combination (-1 : ℂ) * hm i

theorem eq_zero_of_thetaLinForm {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (w : Fin g → ℂ) (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ n n' : Fin g → ℤ, thetaLinForm n w = lam (τ *ᵥ ofIntVec n + ofIntVec n')) : w = 0 := by
  have hlam : (fun j => lam (Pi.single j 1)) = 0 := by
    funext j
    have hj := h 0 (Pi.single j 1)
    rw [thetaLinForm_apply, ofIntVec_zero, zero_dotProduct, mul_zero, mulVec_zero, zero_add,
      ofIntVec_single'] at hj
    exact hj.symm
  funext i
  have hi := h (Pi.single i 1) 0
  rw [thetaLinForm_apply, ofIntVec_single', single_dotProduct, _root_.one_mul, ofIntVec_zero, add_zero,
    linForm_eq_dotProduct lam, hlam, zero_dotProduct] at hi
  exact (mul_eq_zero.mp hi).resolve_left (neg_ne_zero.mpr two_pi_I_ne_zero')

theorem fderiv_eq_mul_of_ratio {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (θ : κ → E → ℂ)
    (hθ : ∀ c, Differentiable ℂ (θ c)) (c : κ) (z w : E) (hc : θ c z ≠ 0) (v : κ → E → ℂ)
    (hv : ∀ c' y, θ c y ≠ 0 → v c' y = θ c' y / θ c y) (hw : ∀ c', fderiv ℂ (v c') z w = 0)
    (f : E → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range θ)) :
    fderiv ℂ f z w = (fderiv ℂ (θ c) z w / θ c z) * f z := by

  have hbase : ∀ c', fderiv ℂ (θ c') z w = (fderiv ℂ (θ c) z w / θ c z) * θ c' z := by
    intro c'
    have hev : ∀ᶠ y in 𝓝 z, θ c y ≠ 0 := (hθ c).continuous.continuousAt.eventually_ne hc
    have hq : DifferentiableAt ℂ (fun y => θ c' y / θ c y) z := by
      have h3 := ((hθ c') z).mul (((hθ c) z).inv hc)
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp [div_eq_mul_inv]
    have hvq : v c' =ᶠ[𝓝 z] fun y => θ c' y / θ c y := hev.mono fun y hy => hv c' y hy
    have hvd : DifferentiableAt ℂ (v c') z := hq.congr_of_eventuallyEq hvq
    have hprod : θ c' =ᶠ[𝓝 z] fun y => v c' y * θ c y := by
      filter_upwards [hev] with y hy
      rw [hv c' y hy, div_mul_cancel₀ _ hy]
    have hd := (hvd.hasFDerivAt.mul ((hθ c) z).hasFDerivAt).congr_of_eventuallyEq hprod
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hw c',
      mul_zero, add_zero]
    rw [hv c' z hc]
    ring

  have key : ∀ f ∈ Submodule.span ℂ (Set.range θ),
      Differentiable ℂ f ∧ fderiv ℂ f z w = (fderiv ℂ (θ c) z w / θ c z) * f z := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c', rfl⟩ := hx
      exact ⟨hθ c', hbase c'⟩
    | zero =>
      refine ⟨differentiable_const 0, ?_⟩
      simp
    | add x y _ _ hx hy =>
      refine ⟨hx.1.add hy.1, ?_⟩
      have hs : HasFDerivAt (x + y) (fderiv ℂ x z + fderiv ℂ y z) z :=
        ((hx.1 z).hasFDerivAt.add (hy.1 z).hasFDerivAt)
      rw [hs.fderiv, ContinuousLinearMap.add_apply, hx.2, hy.2, Pi.add_apply]
      ring
    | smul a x _ hx =>
      refine ⟨hx.1.const_smul a, ?_⟩
      have hs : HasFDerivAt (a • x) (a • fderiv ℂ x z) z := (hx.1 z).hasFDerivAt.const_smul a
      rw [hs.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul, hx.2, Pi.smul_apply, smul_eq_mul]
      ring
  exact (key f hf).2

theorem thetaBundle_kTriv :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice
        τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g →
        ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z ξ
        : Fin g → ℂ) (gam : ℂ), (∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n'
        : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
        ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → fderiv ℂ f z ξ = gam * f z) → ξ = 0) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
        g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c
        i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n'
        : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) /
        2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N
        : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z
        : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g →
        ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z
        : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)))) → (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u
        : HolUnif A L g), SmoothOfRelativeDimension g A.hom → (∀ w : Fin g → ℂ, (∀ (U
        : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex
        0).left ⁻¹ᵁ U → fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0) → w = 0) → ∃ (U
        : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex
        0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f *
        f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t
        i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t
        i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) → (∀ (A : Over (Sp ℂ)) [GrpObj A] (L
        : LB A.left), IsAbelianScheme A → L.IsLB → (∀ (R : Type) [CommRing R] [Algebra ℂ R], ∀ (x
        : Over.mk (spMap (algebraMap ℂ R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L
        x), c.IsGen) → x = 1) → Out.KTriv A L) → (∀ (A : Over (Sp ℂ)) [GrpObj A] (L
        : LB A.left), IsAbelianScheme A → L.IsLB → (∀ (R : Type) [CommRing R] [Algebra ℂ
        R], Algebra.FiniteType ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ
        R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1) → (∀ (R : Type) [CommRing
        R] [Algebra ℂ R], ∀ (x : Over.mk (spMap (algebraMap ℂ
        R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1)) → (∀ (A : Over (Sp
        ℂ)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → (∀ (R : Type) [CommRing
        R] [Algebra ℂ R], IsLocalRing R → Module.Finite ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ
        R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1) → (∀ (R : Type) [CommRing
        R] [Algebra ℂ R], Algebra.FiniteType ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ
        R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1)) → (∀ (A : Over (Sp
        ℂ)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → ∀ (g : ℕ) (u
        : HolUnif A L g) (a : u.Λ → ℂ) (B : u.Λ → ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∃ (U : A.left.Opens) (t
        : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left,
        U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex
        0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t
        i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t
        i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) → (∀ l, a l ≠ 0) → (∀ (l : u.Λ) i z, ⊤ ≤ (u.ex
        z).left ⁻¹ᵁ L.U i → u.fr i z = a l * cexp (B l z) * u.fr i (z + l)) → (∀ (w
        : Fin g → ℂ) (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ), (∀ l : u.Λ, cexp (B l w) = cexp (lam
        l)) → w ∈ u.Λ) → (∀ (w : Fin g → ℂ) (lam : (Fin g →
        ℂ) →ₗ[ℂ] ℂ), (∀ l : u.Λ, B l w = lam l) → w = 0) → (∀ (R : Type) [CommRing R] [Algebra ℂ
        R], IsLocalRing R → Module.Finite ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ
        R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1)) → (∀ (g : ℕ) (τ
        : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp ℂ)) (ex
        : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral
        X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
        (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left,
        U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex
        w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ
        : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D
        c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i
        : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D
        c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ)
        • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin
        N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso
        (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g →
        ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠
        0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z
        +
        w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∀ (L
        : LB X.left) (u : HolUnif X L g), L.IsLB → (u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ)
        ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex
        z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n +
        ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n'
        : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
        ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n'
        : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N
        : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex
        z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠
        0) ∧ u.fr i z = h z / F z)) → IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → Out.KTriv X L) := by
  intro hLat hSep hInd hSpan hCoord hKT hFT hLoc hUni g τ hτ N hN X ex D hX _ _ _ _ a₀ b₀ _ _ L u hL hu
    hAb hSm
  obtain ⟨hex, hΛ, hfr, -⟩ := hu
  subst hex
  obtain ⟨-, -, -, -, -, hD, hcov⟩ := hX

  have huniq : ∀ n n' m m' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = τ *ᵥ ofIntVec m + ofIntVec m' →
      n = m ∧ n' = m' := by
    intro n n' m m' h
    have h0 := (hLat g τ hτ).2.2 (n - m) (n' - m') (by
      rw [sub_eq_add_neg, sub_eq_add_neg, ofIntVec_add, ofIntVec_add, ofIntVec_neg, ofIntVec_neg,
        mulVec_add, mulVec_neg]
      rw [← sub_eq_zero] at h
      rw [← h]
      abel)
    exact ⟨sub_eq_zero.mp h0.1, sub_eq_zero.mp h0.2⟩
  have hmem : ∀ l : u.Λ, ∃ p : (Fin g → ℤ) × (Fin g → ℤ),
      (l : Fin g → ℂ) = τ *ᵥ ofIntVec p.1 + ofIntVec p.2 := by
    intro l
    obtain ⟨n, n', hn⟩ := (hΛ l).1 l.2
    exact ⟨(n, n'), hn⟩
  choose p hp using hmem
  have hpn : ∀ n n' : Fin g → ℤ, ∀ hl : τ *ᵥ ofIntVec n + ofIntVec n' ∈ u.Λ, (p ⟨_, hl⟩).1 = n := by
    intro n n' hl
    exact ((huniq _ _ _ _ (hp ⟨_, hl⟩)).1).symm
  have hlat : ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' ∈ u.Λ := fun n n' => (hΛ _).2 ⟨n, n', rfl⟩

  let θ : (Fin g → Fin N) → (Fin g → ℂ) → ℂ := fun c z =>
    theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)

  have hsub : ∀ y y' : PrimeSpectrum ℂ, y = y' := fun y y' => Subsingleton.elim y y'
  obtain ⟨c, hc⟩ : ∃ c, ⊤ ≤ (u.ex 0).left ⁻¹ᵁ D c := by
    let x₀ : PrimeSpectrum ℂ := ⟨⊥, Ideal.isPrime_bot⟩
    have hx : (u.ex 0).left.base x₀ ∈ (⨆ c, D c) := by
      rw [hcov]
      trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨c, fun y _ => ?_⟩
    rw [hsub y x₀]
    exact hc

  have hsep : ∀ w : Fin g → ℂ, (∀ (U : X.left.Opens) (f : Γ(X.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0) → w = 0 := by
    intro w hw
    have hθc : θ c 0 ≠ 0 := ((hD c).2.2.1 0).mp hc
    obtain ⟨r, hr, -⟩ := (hD c).2.2.2
    have hdiff := (hInd g τ hτ N (by omega)).1
    refine hSep g τ hτ N hN 0 w (fderiv ℂ (θ c) 0 w / θ c 0) fun f hf => ?_
    exact fderiv_eq_mul_of_ratio θ (fun c' => (hdiff c').1) c 0 w hθc
      (fun c' y => valAt' (u.ex y).left (D c) (r c')) (fun c' y hy => hr c' y hy)
      (fun c' => hw (D c) (r c') hc) f (hSpan g τ hτ N (by omega) f hf)
  have hcoord := hCoord X L g u hSm hsep
  have hane : ∀ l : u.Λ, autFactor a₀ b₀ τ (p l).1 (p l).2 0 ≠ 0 := fun l => autFactor_ne_zero' _ _ _ _ _ _
  have hrel : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
      u.fr i z = autFactor a₀ b₀ τ (p l).1 (p l).2 0 * cexp (thetaLinForm (p l).1 z) * u.fr i (z + l) := by
    intro l i z hz
    rw [← autFactor_eq_zero_mul_exp, hp l, ← add_assoc]
    exact hfr _ _ i z hz
  have hunimod : ∀ (w : Fin g → ℂ) (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ),
      (∀ l : u.Λ, cexp (thetaLinForm (p l).1 w) = cexp (lam l)) → w ∈ u.Λ := by
    intro w lam hl
    rw [hΛ]
    refine mem_periodLattice_of_exp_thetaLinForm hτ.1 w lam fun n n' => ?_
    have h1 := hl ⟨_, hlat n n'⟩
    rwa [hpn n n' (hlat n n')] at h1
  have hnondeg : ∀ (w : Fin g → ℂ) (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ),
      (∀ l : u.Λ, thetaLinForm (p l).1 w = lam l) → w = 0 := by
    intro w lam hl
    refine eq_zero_of_thetaLinForm (τ := τ) w lam fun n n' => ?_
    have h1 := hl ⟨_, hlat n n'⟩
    rwa [hpn n n' (hlat n n')] at h1
  exact hKT X L hAb hL (hFT X L hAb hL (hLoc X L hAb hL
    (hUni X L hAb hL g u (fun l => autFactor a₀ b₀ τ (p l).1 (p l).2 0) (fun l => thetaLinForm (p l).1)
      hcoord hane hrel hunimod hnondeg)))

end GlobalTheory
