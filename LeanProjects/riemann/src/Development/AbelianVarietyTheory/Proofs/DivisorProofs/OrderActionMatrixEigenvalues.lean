import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankLin
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
noncomputable section

namespace GlobalTheory.CommonEigField

open Module

theorem finrank_common_eig_map {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} {O : Type}
    (A : O → Matrix (Fin n) (Fin n) K) (m0 : O → K) :
    finrank K (⨅ a, LinearMap.ker (Matrix.toLin' (A a) - m0 a • LinearMap.id) : Submodule K (Fin n → K)) =
      finrank L (⨅ a, LinearMap.ker (Matrix.toLin' ((A a).map f) - f (m0 a) • LinearMap.id) :
        Submodule L (Fin n → L)) := by
  letI := f.toAlgebra
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 f.injective
  refine ReciprocityTheory.ChartRestriction.G.Chart.finrank_eig_bc (V := K) (k := L) (fun a => Matrix.toLin' (A a))
    (fun a => Matrix.toLin' ((A a).map f)) (fun a c => ?_) m0
  funext i
  simp only [Matrix.toLin'_apply, Function.comp_apply]
  exact (RingHom.map_mulVec f (A a) c i).symm

theorem finrank_eigK_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {n : ℕ}
    (ρ : orderC c →+* Module.End R (Fin n → R)) (σ : E →+* K) :
    finrank K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) =
      finrank K (⨅ a : orderC c, LinearMap.ker (Matrix.toLin' ((LinearMap.toMatrix' (ρ a)).map (algebraMap R K))
        - σ a • LinearMap.id) : Submodule K (Fin n → K)) := by
  classical
  let e := TensorProduct.piScalarRight R K K (Fin n)
  have hint : ∀ (a : orderC c) (y : K ⊗[R] (Fin n → R)),
      e ((ρ a).baseChange K y) = Matrix.toLin' ((LinearMap.toMatrix' (ρ a)).map (algebraMap R K)) (e y) := by
    intro a y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x v =>
      funext i
      simp only [LinearMap.baseChange_tmul, e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
        Matrix.toLin'_apply]
      rw [← LinearMap.toMatrix'_mulVec (ρ a) v]
      simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Matrix.map_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, _root_.mul_assoc]
    | add y z hy hz => simp only [map_add, hy, hz]
  have hmap : Submodule.map (e : K ⊗[R] (Fin n → R) →ₗ[K] (Fin n → K)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) =
      ⨅ a : orderC c, LinearMap.ker (Matrix.toLin' ((LinearMap.toMatrix' (ρ a)).map (algebraMap R K))
        - σ a • LinearMap.id) := by
    ext x
    rw [Submodule.mem_map_equiv]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [← e.injective.eq_iff, hint, LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply]
  rw [← e.finrank_map_eq, hmap]

theorem finrank_common_eig_basis {L : Type} [Field L] {W : Type*} [AddCommGroup W] [Module L W] {n : ℕ}
    (B : Module.Basis (Fin n) L W) {O : Type} (T : O → Module.End L W) (C : O → Matrix (Fin n) (Fin n) L)
    (hT : ∀ a i, T a (B i) = ∑ k, C a k i • B k) (m0 : O → L) :
    finrank L (⨅ a, Module.End.eigenspace (T a) (m0 a) : Submodule L W) =
      finrank L (⨅ a, LinearMap.ker (Matrix.toLin' (C a) - m0 a • LinearMap.id) : Submodule L (Fin n → L)) := by
  classical
  let e := B.equivFun
  have hint : ∀ a (w : W), e (T a w) = Matrix.toLin' (C a) (e w) := by
    intro a
    have h : T a = (e.symm.toLinearMap ∘ₗ Matrix.toLin' (C a)) ∘ₗ e.toLinearMap := by
      refine B.ext fun i => ?_
      rw [hT]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e, Module.Basis.equivFun_apply,
        Module.Basis.repr_self, Finsupp.single_eq_pi_single, Matrix.toLin'_apply, Matrix.mulVec_single_one,
        Module.Basis.equivFun_symm_apply, Matrix.col_apply]
    intro w
    rw [h]
    simp
  have hmap : Submodule.map (e : W →ₗ[L] (Fin n → L)) (⨅ a, Module.End.eigenspace (T a) (m0 a)) =
      ⨅ a, LinearMap.ker (Matrix.toLin' (C a) - m0 a • LinearMap.id) := by
    ext x
    rw [Submodule.mem_map_equiv]
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [← e.injective.eq_iff, hint, LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply]
  rw [← e.finrank_map_eq, hmap]

end GlobalTheory.CommonEigField

namespace GlobalTheory

open Module

theorem finrank_eigK_eq_finrank_eig_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E))
    (R : Subring ℂ) (n : ℕ)
    (ρ : orderC c →+* Module.End R (Fin n → R)) (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (B : Module.Basis (Fin n) ℂ W) (T : orderC c → Module.End ℂ W),
    (∀ a i, T a (B i) = ∑ k, ((ρ a (Pi.single i 1) k : R) : ℂ) • B k) →
    ∀ σ : E →+* FractionRing R, Module.finrank (FractionRing R) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) =
      Module.finrank ℂ (⨅ a : orderC c, Module.End.eigenspace (T a) (j (σ a)) : Submodule ℂ W) := by
  intro E _ _ _ c R n ρ j hj W _ _ B T hT σ
  rw [CommonEigField.finrank_eigK_eq, CommonEigField.finrank_common_eig_map j,
    CommonEigField.finrank_common_eig_basis B T
      (fun a => ((LinearMap.toMatrix' (ρ a)).map (algebraMap R (FractionRing R))).map j) ?_]
  intro a i
  rw [hT]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.map_apply, LinearMap.toMatrix'_apply, hj]

end GlobalTheory
