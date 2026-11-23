import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinModuleTensorBdRPlusEqLattice
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsUnitIdentificationSingleIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem UpperTheory.KN.basis_change_matrices_algebra_map {O R R' M ι : Type} [CommRing O] [CommRing R] [CommRing R']
    [Algebra O R] [Algebra O R'] [AddCommGroup M] [Module O M] [Fintype ι] [DecidableEq ι]
    (f : R →ₐ[O] R') (b : Module.Basis ι O M) (jD : (ι → R') ≃ₗ[R'] R' ⊗[O] M) (u : R)
    (z : ι → R ⊗[O] M)
    (h : ∀ i, jD (fun j => f ((Pi.single i u : ι → R) j)) =
      TensorProduct.map f.toLinearMap LinearMap.id (z i)) :
    ∃ (m m' : Matrix ι ι R') (r : ι → ι → R), m' * m = 1 ∧ (∀ i, z i = ∑ k, r i k ⊗ₜ[O] b k) ∧
      ∀ i k, f (r i k) = f u * m i k := by
  let bA := Algebra.TensorProduct.basis R b
  let bD := Algebra.TensorProduct.basis R' b
  have hz : ∀ i, z i = ∑ k, bA.repr (z i) k ⊗ₜ[O] b k := by
    intro i
    conv_lhs => rw [← bA.sum_repr (z i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [bA, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  refine ⟨Matrix.of fun i k => bD.repr (jD (Pi.single i 1)) k, Matrix.of fun k i => jD.symm (bD k) i,
    fun i k => bA.repr (z i) k, ?_, hz, ?_⟩
  · ext k k'
    have h1 : jD.symm (bD k) = ∑ i, jD.symm (bD k) i • (Pi.single i 1 : ι → R') := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have h2 : bD k = ∑ i, jD.symm (bD k) i • jD (Pi.single i 1) := by
      conv_lhs => rw [← jD.apply_symm_apply (bD k), h1, map_sum]
      simp only [map_smul]
    have h3 := congrArg (fun x => bD.repr x k') h2
    simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
      Module.Basis.repr_self, Finsupp.single_apply] at h3
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact h3.symm
  · intro i k
    have e1 : (fun j => f ((Pi.single i u : ι → R) j)) = f u • (Pi.single i 1 : ι → R') := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    have e2 : TensorProduct.map f.toLinearMap LinearMap.id (z i) = ∑ k, f (bA.repr (z i) k) • bD k := by
      conv_lhs => rw [hz i, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [bD, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
    have h3 := h i
    rw [e1, e2, map_smul] at h3
    have h4 := congrArg (fun x => bD.repr x k) h3
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_sum_self] at h4
    exact h4.symm

theorem _root_.UpperTheory.KN.exists_unit_invertible_matrix_identification_basis :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (b : Module.Basis ι ↥(OL LL) ↥T.L.T), ∃ (m m' : Matrix ι ι (OD l ↥(OL LL))) (u : OA l ↥(OL LL)) (r : ι → ι → OA l ↥(OL LL)), IsUnit (toOD l ↥(OL LL) u) ∧ m' * m = 1 ∧ (∀ i, I.j (inclV l ↥(OL LL) ι (Pi.single i u)) = TWincl (inclO l ↥(OL LL)) T (∑ k, r i k ⊗ₜ[↥(OL LL)] b k)) ∧ ∀ i k, toOD l ↥(OL LL) (r i k) = toOD l ↥(OL LL) u * m i k := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I b
  obtain ⟨jD, hjD⟩ := GlobalTheory.DeRhamIdent.main l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I
  obtain ⟨u, hu, hz⟩ := UpperTheory.KN.exists_unit_identification_single_integral l a e ϖ LL ι P T I
  choose z hz using hz
  obtain ⟨m, m', r, h1, h2, h3⟩ := UpperTheory.KN.basis_change_matrices_algebra_map (toOD l ↥(OL LL)) b jD u z
    (fun i => hjD _ _ (hz i))
  refine ⟨m, m', u, r, hu, h1, fun i => (hz i).trans ?_, h3⟩
  exact congrArg (TWincl (inclO l ↥(OL LL)) T) (h2 i)
