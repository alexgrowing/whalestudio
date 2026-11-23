import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubstDualWeylExpressibleMatrixMulClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyDiagonalEqSumComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerRowOperatorMemDualWeylEndSubalgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyTransvectionEqSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfMemDualWeylLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictLowerMemClosureTransvectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictUpperMemClosureTransvectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGaussFactorisationCoeffSmulInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyEqEvalGenericRowSubstitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRowSubstitutionCoeffExponentLeDegreeStatement

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.GenCoef

theorem expr_mul_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y Y' : Matrix (Fin N) (Fin N) R), Expr O N ν R Y → Expr O N ν R Y' → Expr O N ν R (Y * Y') := GlobalTheory.T.rowSubstDualWeylExpressible_matrix_mul_closed

theorem rowSubst_diagonal_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (d : Fin N → R) (D : ℕ)
    (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D →
    rowSubst O N R (Matrix.diagonal d) f = ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (D + 1)),
      (∏ a, d a ^ w a) • MvPolynomial.map (algebraMap O R) (weightedHomogeneousComponent (rowW N N) w f) := GlobalTheory.T.matrixRowSubstitutionPoly_diagonal_eq_sum_components

theorem rowDiv_mem_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (a b : Fin N), a ≠ b → ∀ k : ℕ,
    ∃ p ∈ dwAlg O N ν, ∀ f : dualWeyl O N N ν,
      (p f : MvPolynomial (Fin N × Fin N) O) = rowDiv O a b k (f : MvPolynomial (Fin N × Fin N) O) := GlobalTheory.T.dividedPowerRowOperator_mem_dualWeylEndSubalgebra

theorem rowSubst_transvection_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (a b : Fin N) (r : R)
    (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D →
    rowSubst O N R (Matrix.transvection a b r) f =
      ∑ k ∈ Finset.range (D + 1), r ^ k • MvPolynomial.map (algebraMap O R) (rowDiv O b a k f) := GlobalTheory.T.matrixRowSubstitutionPoly_transvection_eq_sum

theorem totalDegree_le_of_mem_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O),
    f ∈ dualWeyl O N N ν → f.totalDegree ≤ ∑ a, ν a := GlobalTheory.T.totalDegree_le_of_mem_dualWeylLattice

theorem lower_mem_closure_of_parts : ∀ (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R), (∀ a b, a ≤ b → c a b = 0) →
    1 + c ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := GlobalTheory.T.one_add_strictLower_mem_closure_transvection'

theorem upper_mem_closure_of_parts : ∀ (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R), (∀ a b, b ≤ a → c a b = 0) →
    1 + c ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := GlobalTheory.T.one_add_strictUpper_mem_closure_transvection

theorem lduHom_pure_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (M : Type) [AddCommGroup M] [Module O M]
    (s : Finset (Fin N × Fin N →₀ ℕ)) (c : (Fin N × Fin N →₀ ℕ) → M),
    (∀ n, ∑ m ∈ s, (lduHom O N (monomial m 1)).coeff n • c m = 0) → ∀ m ∈ s, c m = 0 := GlobalTheory.T.genericGaussFactorisation_coeff_smul_injective

theorem rowSubst_eq_sum_genSub_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) O),
    rowSubst O N R Y f = ∑ m ∈ (GlobalTheory.HighWt.genSub O N f).support, (m.prod fun v k => Y v.1 v.2 ^ k) •
      MvPolynomial.map (algebraMap O R) ((GlobalTheory.HighWt.genSub O N f).coeff m) := GlobalTheory.T.matrixRowSubstitutionPoly_eq_eval_genericRowSubstitution

theorem genSub_coeff_le_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D →
    ∀ m, (GlobalTheory.HighWt.genSub O N f).coeff m ≠ 0 → ∀ v, m v ≤ D := GlobalTheory.T.genericRowSubstitution_coeff_exponent_le_degree

end GlobalTheory.GenCoef

namespace GlobalTheory.GenCoef

section Glue

variable {O : Type} [CommRing O] {N : ℕ} {ν : Fin N → ℕ} {R : Type} [CommRing R] [Algebra O R]

theorem expr_of_finset {κ : Type} (s : Finset κ) (Y : Matrix (Fin N) (Fin N) R) (r : κ → R)
    (p : κ → Module.End O (dualWeyl O N N ν)) (hp : ∀ i ∈ s, p i ∈ dwAlg O N ν)
    (h : ∀ f : dualWeyl O N N ν, rowSubst O N R Y (f : MvPolynomial (Fin N × Fin N) O) =
      ∑ i ∈ s, r i • MvPolynomial.map (algebraMap O R) (p i f : MvPolynomial (Fin N × Fin N) O)) :
    Expr O N ν R Y := by
  classical
  let e := s.equivFin
  refine ⟨s.card, fun j => r (e.symm j), fun j => p (e.symm j), fun j => hp _ (e.symm j).2, fun f => ?_⟩
  rw [h f, ← Finset.sum_coe_sort s]
  exact (Equiv.sum_comp e.symm (fun i : s => r i • MvPolynomial.map (algebraMap O R) (p i f : MvPolynomial (Fin N × Fin N) O))).symm

theorem expr_diagonal (d : Fin N → R) : Expr O N ν R (Matrix.diagonal d) := by
  classical
  refine expr_of_finset (Fintype.piFinset (fun _ : Fin N => Finset.range (∑ a, ν a + 1))) _ (fun w => ∏ a, d a ^ w a)
    (fun w => GlobalTheory.ExpFrame.rowProj O N ν w) (fun w _ => Algebra.subset_adjoin (Or.inr ⟨w, rfl⟩)) (fun f => ?_)
  rw [rowSubst_diagonal_of_parts O N R d _ _ (totalDegree_le_of_mem_of_parts O N ν _ f.2)]
  rfl

theorem expr_one : Expr O N ν R 1 := by
  have := expr_diagonal (O := O) (N := N) (ν := ν) (R := R) (fun _ => 1)
  rwa [Matrix.diagonal_one] at this

theorem expr_transvection (a b : Fin N) (hab : a ≠ b) (r : R) : Expr O N ν R (Matrix.transvection a b r) := by
  classical
  choose p hp hpf using rowDiv_mem_of_parts O N ν b a hab.symm
  refine expr_of_finset (Finset.range (∑ a, ν a + 1)) _ (fun k => r ^ k) p (fun k _ => hp k) (fun f => ?_)
  rw [rowSubst_transvection_of_parts O N R a b r _ _ (totalDegree_le_of_mem_of_parts O N ν _ f.2)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hpf k f]

theorem expr_of_mem_closure (Y : Matrix (Fin N) (Fin N) R)
    (hY : Y ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r}) :
    Expr O N ν R Y := by
  induction hY using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, r, hab, rfl⟩ := hx
    exact expr_transvection a b hab r
  | one => exact expr_one
  | mul x y _ _ hx hy => exact expr_mul_of_parts O N ν R x y hx hy

theorem expr_ldu : Expr O N ν (MvPolynomial (Fin N × Fin N) O) (lowGen O N * diagGen O N * upGen O N) := by
  classical
  have hL : lowGen O N = 1 + Matrix.of (fun a b => if b < a then (X (a, b) : MvPolynomial (Fin N × Fin N) O) else 0) := by
    ext a b
    by_cases h : a = b
    · subst h; simp [lowGen]
    · simp [lowGen, h, Matrix.one_apply_ne h]
  have hU : upGen O N = 1 + Matrix.of (fun a b => if a < b then (X (a, b) : MvPolynomial (Fin N × Fin N) O) else 0) := by
    ext a b
    by_cases h : a = b
    · subst h; simp [upGen]
    · simp [upGen, h, Matrix.one_apply_ne h]
  refine expr_mul_of_parts O N ν _ _ _ (expr_mul_of_parts O N ν _ _ _ ?_ (expr_diagonal _)) ?_
  · rw [hL]
    exact expr_of_mem_closure _ (lower_mem_closure_of_parts _ N _ fun a b hab => by simp [not_lt.mpr hab])
  · rw [hU]
    exact expr_of_mem_closure _ (upper_mem_closure_of_parts _ N _ fun a b hab => by simp [not_lt.mpr hab])

end Glue

end GlobalTheory.GenCoef

namespace GlobalTheory.GenCoef

theorem coef_mem (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) :
    ∃ p ∈ dwAlg O N ν, ∀ f : dualWeyl O N N ν,
      (p f : MvPolynomial (Fin N × Fin N) O) = (GlobalTheory.HighWt.genSub O N (f : MvPolynomial (Fin N × Fin N) O)).coeff m := by
  classical
  obtain ⟨n, r, p, hp, hY⟩ := expr_ldu (O := O) (N := N) (ν := ν)
  let D := ∑ a, ν a
  let Cm : (Fin N × Fin N →₀ ℕ) → (dualWeyl O N N ν →ₗ[O] MvPolynomial (Fin N × Fin N) O) := fun m =>
    { toFun := fun f => (GlobalTheory.HighWt.genSub O N (f : MvPolynomial (Fin N × Fin N) O)).coeff m
      map_add' := fun f g => by simp [GlobalTheory.HighWt.genSub]
      map_smul' := fun c f => by simp [GlobalTheory.HighWt.genSub] }
  let Φ : Module.End O (dualWeyl O N N ν) →ₗ[O] (dualWeyl O N N ν →ₗ[O] MvPolynomial (Fin N × Fin N) O) :=
    LinearMap.llcomp O _ _ _ (dualWeyl O N N ν).subtype
  let Asub : Submodule O (dualWeyl O N N ν →ₗ[O] MvPolynomial (Fin N × Fin N) O) :=
    (Subalgebra.toSubmodule (dwAlg O N ν)).map Φ
  let s0 : Finset (Fin N × Fin N →₀ ℕ) :=
    (Fintype.piFinset fun _ : Fin N × Fin N => Finset.range (D + 1)).map Finsupp.equivFunOnFinite.symm.toEmbedding
  let s := insert m s0
  have hs : ∀ m' : Fin N × Fin N →₀ ℕ, (∀ v, m' v ≤ D) → m' ∈ s := by
    intro m' h
    refine Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨⇑m', Fintype.mem_piFinset.2 fun v => Finset.mem_range.2 (Nat.lt_succ_of_le (h v)), ?_⟩)
    simp
  have hsum : ∀ f : dualWeyl O N N ν, rowSubst O N _ (lowGen O N * diagGen O N * upGen O N) (f : MvPolynomial (Fin N × Fin N) O) =
      ∑ m' ∈ s, lduHom O N (monomial m' 1) •
        MvPolynomial.map (algebraMap O (MvPolynomial (Fin N × Fin N) O)) (Cm m' f) := by
    intro f
    rw [rowSubst_eq_sum_genSub_of_parts]
    refine Finset.sum_subset (fun m' hm' => hs m' (genSub_coeff_le_of_parts O N D _ (totalDegree_le_of_mem_of_parts O N ν _ f.2) m'
      (MvPolynomial.mem_support_iff.1 hm'))) (fun m' _ hm' => ?_) |>.trans (Finset.sum_congr rfl fun m' _ => ?_)
    · simp [Cm, MvPolynomial.notMem_support_iff.1 hm']
    · simp only [Cm, LinearMap.coe_mk, AddHom.coe_mk, lduHom, aeval_monomial, map_one, one_mul]
      rfl
  have hcoef : ∀ k : Fin N × Fin N →₀ ℕ, ∑ m' ∈ s, (lduHom O N (monomial m' 1)).coeff k • Cm m' =
      ∑ i, (r i).coeff k • Φ (p i) := by
    intro k
    apply LinearMap.ext
    intro f
    apply MvPolynomial.ext
    intro j
    have key : ∀ (t q : MvPolynomial (Fin N × Fin N) O),
        ((t • MvPolynomial.map (algebraMap O (MvPolynomial (Fin N × Fin N) O)) q).coeff j).coeff k = t.coeff k * q.coeff j := by
      intro t q
      rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.algebraMap_eq, smul_eq_mul, mul_comm,
        MvPolynomial.coeff_C_mul, mul_comm]
    have h := congrArg (fun q : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) => (q.coeff j).coeff k)
      ((hsum f).symm.trans (hY f))
    simp only [MvPolynomial.coeff_sum, key] at h
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
    simpa [Φ] using h
  have hzero := lduHom_pure_of_parts O N _ s (fun m' => Asub.mkQ (Cm m')) (fun k => by
    simp only [← map_smul, ← map_sum]
    rw [hcoef k, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (hp i))) m (Finset.mem_insert_self _ _)
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzero
  obtain ⟨q, hq, hqe⟩ := Submodule.mem_map.1 hzero
  exact ⟨q, hq, fun f => congrArg (fun φ => φ f) hqe⟩

end GlobalTheory.GenCoef

namespace GlobalTheory.GenCoef

open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD GlobalTheory.ExpFrame

def atFactorHom (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (τ : ι) :
    Module.End O (dualWeyl O N N (res N (lam τ))) →ₐ[O] Module.End O (NablaT O N lam) where
  toFun p := atFactor τ p
  map_one' := by
    unfold atFactor
    rw [Module.End.one_eq_id, Function.update_eq_self]
    exact PiTensorProduct.map_id
  map_mul' p q := by
    unfold atFactor
    rw [← PiTensorProduct.map_mul]
    congr 1
    funext i
    by_cases h : i = τ
    · subst h; simp
    · simp [Function.update_of_ne h]; rfl
  map_zero' := by
    unfold atFactor
    have := PiTensorProduct.map_update_smul (R := O)
      (fun i : ι => (LinearMap.id : Module.End O (dualWeyl O N N (res N (lam i))))) τ (0 : O) 0
    simpa using this
  map_add' p q := by
    unfold atFactor
    exact PiTensorProduct.map_update_add (fun i : ι => (LinearMap.id : Module.End O (dualWeyl O N N (res N (lam i))))) τ p q
  commutes' c := by
    show atFactor τ _ = _
    unfold atFactor
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul,
      Module.End.one_eq_id, Function.update_eq_self, PiTensorProduct.map_id, Module.End.one_eq_id]

theorem atFactor_mem_alg (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (τ : ι)
    (p : Module.End O (dualWeyl O N N (res N (lam τ)))) (hp : p ∈ dwAlg O N (res N (lam τ))) :
    atFactor τ p ∈ alg O N lam := by
  have hle : dwAlg O N (res N (lam τ)) ≤ (alg O N lam).comap (atFactorHom O N lam τ) := by
    refine Algebra.adjoin_le ?_
    rintro _ (⟨g, rfl⟩ | ⟨w, rfl⟩)
    · show atFactor τ _ ∈ alg O N lam
      have : atFactor τ (Formalism.UG.dualWeylRep O N N (res N (lam τ)) g) = grp O N lam (Function.update 1 τ g) := by
        show PiTensorProduct.map _ = PiTensorProduct.map _
        congr 1
        funext i
        by_cases h : i = τ
        · subst h; simp
        · simp [Function.update_of_ne h]; rfl
      rw [this]
      exact Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)
    · show atFactor τ _ ∈ alg O N lam
      have hP : IsProj O N lam τ w (atFactor τ (rowProj O N (res N (lam τ)) w)) := by
        intro x y hy
        unfold atFactor
        rw [PiTensorProduct.map_tprod]
        congr 1
        funext σ
        by_cases h : σ = τ
        · subst h
          simp only [Function.update_self, LinearMap.restrict_apply, rowProj]
          exact Subtype.ext hy.symm
        · simp [Function.update_of_ne h]
      exact Algebra.subset_adjoin (Or.inr ⟨τ, w, hP⟩)
  exact hle hp

end GlobalTheory.GenCoef

namespace GlobalTheory.HighWt

open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD GlobalTheory.ExpFrame

theorem coefIn_of_domain : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (lam : ι → ℕ → ℕ), CoefIn O N lam := by
  intro O _ _ _ N ι _ _ lam τ m
  obtain ⟨p, hp, hpf⟩ := GlobalTheory.GenCoef.coef_mem O N (res N (lam τ)) m
  refine ⟨⟨_, GlobalTheory.GenCoef.atFactor_mem_alg O N lam τ p hp⟩, ?_⟩
  intro x y hy
  show atFactor τ p (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y)
  unfold atFactor
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext σ
  by_cases h : σ = τ
  · subst h
    simp only [Function.update_self]
    exact Subtype.ext ((hpf _).trans hy.symm)
  · simp [Function.update_of_ne h]

end GlobalTheory.HighWt

end
