import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem equivFinsuppOfBasisLeft_lTensor_apply {F : Type} [Field F] {V M N : Type}
    [AddCommGroup V] [Module F V] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    {ι : Type} [DecidableEq ι] (b : Module.Basis ι F V) (f : M →ₗ[F] N) (x : V ⊗[F] M) (i : ι) :
    equivFinsuppOfBasisLeft b (f.lTensor V x) i = f (equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem algebraTensorModule_map_id_apply {F L : Type} [Field F] [Field L] [Algebra F L]
    {V M N : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (f : M →ₗ[F] N) (x : V ⊗[F] M) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) f x = f.lTensor V x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_tmul_one_of_frob_fixed_of_mem_fil_zero :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (x : V ⊗[Qp] B), φVB PD (LL := LL) (V := V) x = x → ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[Qp] (1 : B) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ x hφ hF
  classical
  let b := Module.Basis.ofVectorSpace Qp V
  have key : ∀ i, ∃ c : Qp, algebraMap Qp B c = equivFinsuppOfBasisLeft b x i := by
    intro i
    apply PD.fund
    · have h := equivFinsuppOfBasisLeft_lTensor_apply b PD.φ.toLinearMap x i
      rw [← algebraTensorModule_map_id_apply (L := LL)] at h
      have h2 : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) PD.φ.toLinearMap x = x := hφ
      rw [h2] at h
      exact h.symm
    · obtain ⟨y, hy⟩ := hF
      have h := equivFinsuppOfBasisLeft_lTensor_apply b
        (PD.ι.toLinearMap.restrictScalars Qp) x i
      rw [← algebraTensorModule_map_id_apply (L := LL)] at h
      have h' := equivFinsuppOfBasisLeft_lTensor_apply b
        ((PD.Fil 0).restrictScalars Qp).subtype y i
      rw [← algebraTensorModule_map_id_apply (L := LL), hy] at h'
      have h3 : PD.ι (equivFinsuppOfBasisLeft b x i)
          = ((PD.Fil 0).restrictScalars Qp).subtype (equivFinsuppOfBasisLeft b y i) :=
        h.symm.trans h'
      rw [h3]
      exact (equivFinsuppOfBasisLeft b y i).2
  choose c hc using key
  refine ⟨∑ i ∈ (equivFinsuppOfBasisLeft b x).support, c i • b i, ?_⟩
  have hx : x = (equivFinsuppOfBasisLeft b).symm (equivFinsuppOfBasisLeft b x) := by simp
  rw [equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum] at hx
  rw [TensorProduct.sum_tmul]
  refine hx.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [← hc i, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory
