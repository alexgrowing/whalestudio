import Mathlib
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteCoord

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct

noncomputable section

namespace AdeleBaseChange

open SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def evalAddHom (w : HeightOneSpectrum (𝓞 L)) : FiniteAdeleRing (𝓞 L) L →+ w.adicCompletion L where
  toFun y := y w
  map_zero' := rfl
  map_add' _ _ := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

theorem eventually_localCoord_mem (i : ι) (y : FiniteAdeleRing (𝓞 L) L) :
    ∀ᶠ v in cofinite, localCoord b v i (fun w ↦ y w.1) ∈ v.adicCompletionIntegers K := by
  have hfin : {w : HeightOneSpectrum (𝓞 L) |
      ¬ (y * algebraMap L (FiniteAdeleRing (𝓞 L) L) (traceDual b i)) w ∈
        w.adicCompletionIntegers L}.Finite :=
    Filter.eventually_cofinite.1 (y * algebraMap L (FiniteAdeleRing (𝓞 L) L) (traceDual b i)).2
  refine Filter.eventually_cofinite.2 ((hfin.image (below K)).subset fun v hv ↦ ?_)
  by_contra hv'
  refine hv (localCoord_mem b v i _ fun w ↦ ?_)
  by_contra hw
  exact hv' ⟨w.1, hw, (below_eq_iff w.1 v).2 w.2⟩

def finiteCoord (i : ι) : FiniteAdeleRing (𝓞 L) L →+ FiniteAdeleRing (𝓞 K) K where
  toFun y := ⟨fun v ↦ localCoord b v i (fun w ↦ y w.1), eventually_localCoord_mem b i y⟩
  map_zero' := FiniteAdeleRing.ext (K := K) fun v ↦ map_zero (localCoord b v i)
  map_add' y y' := FiniteAdeleRing.ext (K := K) fun v ↦
    map_add (localCoord b v i) (fun w : PlacesOver L v ↦ y w.1) (fun w : PlacesOver L v ↦ y' w.1)

theorem finiteCoord_apply (i : ι) (y : FiniteAdeleRing (𝓞 L) L) (v : HeightOneSpectrum (𝓞 K)) :
    finiteCoord b i y v = localCoord b v i (fun w ↦ y w.1) :=
  rfl

theorem continuous_finiteCoord (i : ι) : Continuous (finiteCoord b i) := by
  refine (RestrictedProduct.continuous_dom
    (R := fun w : HeightOneSpectrum (𝓞 L) ↦ w.adicCompletion L)
    (A := fun w ↦ (w.adicCompletionIntegers L : Set (w.adicCompletion L)))).2 fun S hS ↦ ?_
  set T : Set (HeightOneSpectrum (𝓞 L)) := Sᶜ ∪ {w | algebraMap L (w.adicCompletion L)
    (traceDual b i) ∉ w.adicCompletionIntegers L} with hTdef
  have hT : T.Finite := by
    refine Set.Finite.union ?_ ?_
    · exact le_principal_iff.1 hS
    · exact Filter.eventually_cofinite.1
        (algebraMap L (FiniteAdeleRing (𝓞 L) L) (traceDual b i)).2
  have hS' : cofinite ≤ 𝓟 (below K '' T)ᶜ := by
    rw [le_principal_iff, mem_cofinite, compl_compl]
    exact hT.image _
  let g : Πʳ w : HeightOneSpectrum (𝓞 L), [w.adicCompletion L, w.adicCompletionIntegers L]_[𝓟 S] →
      Πʳ v : HeightOneSpectrum (𝓞 K),
        [v.adicCompletion K, v.adicCompletionIntegers K]_[𝓟 (below K '' T)ᶜ] :=
    fun y ↦ ⟨fun v ↦ localCoord b v i (fun w ↦ y w.1), by
      rw [eventually_principal]
      intro v hv
      refine localCoord_mem b v i _ fun w ↦ ?_
      have hw : w.1 ∉ T := fun hw ↦ hv ⟨w.1, hw, (below_eq_iff w.1 v).2 w.2⟩
      simp only [hTdef, Set.mem_union, Set.mem_compl_iff, not_or, not_not, Set.mem_ofPred_eq] at hw
      exact mul_mem (eventually_principal.1 y.2 _ hw.1) hw.2⟩
  have hg : Continuous g := RestrictedProduct.continuous_rng_of_principal_iff_forall.2 fun v ↦
    (continuous_localCoord b v i).comp
      (continuous_pi fun w ↦ RestrictedProduct.continuous_eval w.1)
  exact (RestrictedProduct.continuous_inclusion hS').comp hg

local instance : Algebra K (FiniteAdeleRing (𝓞 L) L) :=
  ((algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap K L)).toAlgebra

local instance : IsScalarTower K L (FiniteAdeleRing (𝓞 L) L) :=
  .of_algebraMap_eq fun _ ↦ rfl

variable (K L) in

def finiteTensorMap : L ⊗[K] FiniteAdeleRing (𝓞 K) K →ₐ[L] FiniteAdeleRing (𝓞 L) L :=
  Algebra.TensorProduct.lift (Algebra.ofId L _)
    { finiteAdeleMap K L with commutes' := finiteAdeleMap_algebraMap } fun _ _ ↦ Commute.all _ _

theorem finiteTensorMap_tmul (l : L) (a : FiniteAdeleRing (𝓞 K) K) :
    finiteTensorMap K L (l ⊗ₜ a) = algebraMap L _ l * finiteAdeleMap K L a := by
  rw [finiteTensorMap, Algebra.TensorProduct.lift_tmul]
  rfl

theorem finiteCoord_algebraMap_mul (i : ι) (l : L) (a : FiniteAdeleRing (𝓞 K) K) :
    finiteCoord b i (algebraMap L _ l * finiteAdeleMap K L a) =
      algebraMap K _ (b.repr l i) * a := by
  refine FiniteAdeleRing.ext (K := K) fun v ↦ ?_
  rw [finiteCoord_apply]
  have : (fun w : PlacesOver L v ↦
      (algebraMap L (FiniteAdeleRing (𝓞 L) L) l * finiteAdeleMap K L a) w.1) =
      a v • algebraMap L (CompletionsOver L v) l := by
    funext w
    change algebraMap L (w.1.adicCompletion L) l *
        completionMap (below K w.1) w.1 (a (below K w.1)) =
      completionMap v w.1 (a v) * algebraMap L (w.1.adicCompletion L) l
    rw [completionMap_congr ((below_eq_iff w.1 v).2 w.2), mul_comm]
  rw [this, map_smul, localCoord_algebraMap, smul_eq_mul, mul_comm]
  rfl

theorem finiteTensorMap_sum_finiteCoord (y : FiniteAdeleRing (𝓞 L) L) :
    finiteTensorMap K L (∑ i, b i ⊗ₜ finiteCoord b i y) = y := by
  refine FiniteAdeleRing.ext (K := L) fun w ↦ ?_
  rw [map_sum]
  change evalAddHom w (∑ i, finiteTensorMap K L (b i ⊗ₜ finiteCoord b i y)) = y w
  rw [map_sum]
  have h := congrFun (sum_localCoord b (below K w) (fun w' ↦ y w'.1)) ⟨w, liesOver_below w⟩
  rw [Finset.sum_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [finiteTensorMap_tmul]
  exact mul_comm _ _

theorem sum_finiteCoord_finiteTensorMap (t : L ⊗[K] FiniteAdeleRing (𝓞 K) K) :
    ∑ i, b i ⊗ₜ finiteCoord b i (finiteTensorMap K L t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
    simp_rw [finiteTensorMap_tmul, finiteCoord_algebraMap_mul, ← Algebra.smul_def,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← TensorProduct.sum_tmul, b.sum_repr]
  | add s t hs ht =>
    simp_rw [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hs, ht]

variable (K L) in

def finiteTensorEquiv : L ⊗[K] FiniteAdeleRing (𝓞 K) K ≃ₐ[L] FiniteAdeleRing (𝓞 L) L :=
  AlgEquiv.ofBijective (finiteTensorMap K L)
    ⟨Function.LeftInverse.injective
      (g := fun y : FiniteAdeleRing (𝓞 L) L ↦ ∑ i, Module.finBasis K L i ⊗ₜ finiteCoord (Module.finBasis K L) i y)
      (sum_finiteCoord_finiteTensorMap (Module.finBasis K L)),
    Function.RightInverse.surjective (finiteTensorMap_sum_finiteCoord (Module.finBasis K L))⟩

theorem finiteTensorEquiv_tmul (l : L) (a : FiniteAdeleRing (𝓞 K) K) :
    finiteTensorEquiv K L (l ⊗ₜ a) = algebraMap L _ l * finiteAdeleMap K L a :=
  finiteTensorMap_tmul l a

theorem finiteTensorEquiv_symm_apply (y : FiniteAdeleRing (𝓞 L) L) :
    (finiteTensorEquiv K L).symm y = ∑ i, b i ⊗ₜ finiteCoord b i y := by
  rw [AlgEquiv.symm_apply_eq]
  exact (finiteTensorMap_sum_finiteCoord b y).symm

theorem finiteTensorEquiv_tmul_apply (l : L) (a : FiniteAdeleRing (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 L)) :
    finiteTensorEquiv K L (l ⊗ₜ a) w =
      tensorEquiv' L (below K w) (l ⊗ₜ a (below K w)) ⟨w, liesOver_below w⟩ := by
  rw [finiteTensorEquiv_tmul, tensorEquiv'_tmul]
  rfl

end AdeleBaseChange

end

end GroundTheory.Global
