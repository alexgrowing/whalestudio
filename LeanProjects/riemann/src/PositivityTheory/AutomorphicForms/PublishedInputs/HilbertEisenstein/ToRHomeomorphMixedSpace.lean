import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Imports
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits

noncomputable section

open NumberField NumberField.mixedEmbedding MeasureTheory GroundTheory.Global
open scoped FourierTransform Matrix Classical
open GlobalTheory.CuspRep

namespace UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

theorem toR_homeomorphMixedSpace (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : Ad F) :
    toR F (homeomorphMixedSpace F x.1) = UpperTheory.V.TR.pInf F x := by
  funext v
  rfl

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

instance isEmpty_isComplex : IsEmpty {w : InfinitePlace F // InfinitePlace.IsComplex w} :=
  ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.2 w.2) (IsTotallyReal.isReal w.1)⟩

theorem norm_sq_mixedToEuclidean (u : mixedSpace F) :
    ‖mixedToEuclidean F u‖ ^ 2 = ∑ v, (toR F u v) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, mixedToEuclidean, ContinuousLinearEquiv.trans_apply,
    inner_toMixed_symm]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, mapComplexCoord_apply]
  rw [← Equiv.sum_comp (Equiv.subtypeUnivEquiv (fun v => IsTotallyReal.isReal v)).symm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [toR, sq]

theorem norm_sq_toEuclid2 (u : Fin 2 → mixedSpace F) :
    ‖GroundTheory.Automorphic.Adele2.toEuclid2 F u‖ ^ 2 = ∑ v, ((toR F (u 0) v) ^ 2 + (toR F (u 1) v) ^ 2) := by
  rw [GroundTheory.Automorphic.Adele2.toEuclid2_apply, WithLp.prod_norm_sq_eq_of_L2, Finset.sum_add_distrib,
    ← norm_sq_mixedToEuclidean, ← norm_sq_mixedToEuclidean]
  rfl

def coordCLM (i : Fin 2) (v : InfinitePlace F) : (Fin 2 → mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => toR F (u i) v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem coordCLM_apply (i : Fin 2) (v : InfinitePlace F) (u : Fin 2 → mixedSpace F) :
    coordCLM F i v u = toR F (u i) v := rfl

def lin (v : InfinitePlace F) : (Fin 2 → mixedSpace F) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (coordCLM F 0 v) + Complex.I • Complex.ofRealCLM.comp (coordCLM F 1 v)

theorem lin_apply (v : InfinitePlace F) (u : Fin 2 → mixedSpace F) :
    lin F v u = (toR F (u 0) v : ℂ) + Complex.I * (toR F (u 1) v : ℂ) := by
  simp [lin, coordCLM_apply]

theorem hasTemperateGrowth_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) (f : ι → E → ℂ) (hf : ∀ i, (f i).HasTemperateGrowth) :
    (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h := (hf a).mul ih
    have e : (fun x => ∏ i ∈ insert a s, f i x) = (f a * fun x => ∏ i ∈ s, f i x) := by
      funext x
      simp [Finset.prod_insert ha]
    rw [e]
    exact h

def poly (u : Fin 2 → mixedSpace F) : ℂ := ∏ v, lin F v u

theorem hasTemperateGrowth_poly : (poly F).HasTemperateGrowth :=
  hasTemperateGrowth_prod _ (fun v u => lin F v u) fun v => (lin F v).hasTemperateGrowth

theorem exists_schwartz_arch :
    ∃ φ : SchwartzMap (Fin 2 → NumberField.mixedEmbedding.mixedSpace F) ℂ,
      ∀ u, φ u = arch (toR F (u 0)) (toR F (u 1)) := by
  refine ⟨SchwartzMap.smulLeftCLM ℂ (poly F)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (GroundTheory.Automorphic.Adele2.toEuclid2 F)
      (gaussianSchwartz _)), fun u => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_poly F)]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    gaussianSchwartz_apply, smul_eq_mul]
  rw [norm_sq_toEuclid2, arch, Finset.prod_mul_distrib, poly]
  congr 1
  all_goals first
    | exact Finset.prod_congr rfl fun v _ => lin_apply F v u
    | (rw [← Complex.exp_sum, Complex.ofReal_exp]
       congr 1
       push_cast
       rw [Finset.mul_sum])

section Support

open IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base

theorem finite_support_of_cond (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (hfin : IsOfFinOrder ω)
    (hc : ∀ w, UpperTheory.V.Sd.IsCondAt w ω (c w)) : {w | c w ≠ 0}.Finite := by
  obtain ⟨m, hm, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have ho := GlobalTheory.HeckeGal.isOpen_ker_of_pow ω.1 ω.2.1 hm fun x => congrArg (fun ξ : HChar F => ξ.1 x) h
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen ω.1.ker ho
  refine hS.subset fun w hw => ?_
  by_contra hwS
  apply hw
  refine Nat.le_zero.1 ((hc w).2 ?_)
  simp only [Set.mem_ofPred_eq]
  intro x hu _
  exact key w x hu fun h => absurd h hwS

end Support

end UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic
