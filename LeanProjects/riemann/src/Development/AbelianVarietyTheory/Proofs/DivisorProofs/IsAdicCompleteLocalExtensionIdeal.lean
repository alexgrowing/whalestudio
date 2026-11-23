import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
import Development.AbelianVarietyTheory.Proofs.HeightProofs.GaussRingCompletionRename
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne

noncomputable section

namespace GlobalTheory.TamOne.IntLocComplete

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def ovIncl : v.adicCompletionIntegers F →+* intLoc F E v :=
  RingHom.codRestrict (((Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := Fv F v) (B := E)) :
      Fv F v →+* Fv F v ⊗[F] E).comp (v.adicCompletionIntegers F).subtype) (intLoc F E v)
    fun a => by
      have := tmul_mem_intLoc (E := E) a.2 1
      simpa using this

abbrev ovAlg : Algebra (v.adicCompletionIntegers F) (intLoc F E v) := (ovIncl (E := E) v).toAlgebra

attribute [local instance] ovAlg

theorem tmul_eq_smul {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) (x : 𝓞 E) :
    (⟨a ⊗ₜ[F] (x : E), tmul_mem_intLoc ha x⟩ : intLoc F E v) =
      (⟨a, ha⟩ : v.adicCompletionIntegers F) • intLocIncl v x := by
  apply Subtype.ext
  rw [Algebra.smul_def]
  change a ⊗ₜ[F] (x : E) = (a ⊗ₜ[F] (1 : E)) * ((1 : Fv F v) ⊗ₜ[F] (x : E))
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem finite : Module.Finite (v.adicCompletionIntegers F) (intLoc F E v) := by
  classical
  let b := RingOfIntegers.basis E
  let N : Submodule (v.adicCompletionIntegers F) (intLoc F E v) :=
    Submodule.span _ (Set.range fun i => intLocIncl v (b i))
  have hincl : ∀ x : 𝓞 E, intLocIncl v x ∈ N := by
    intro x
    rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_zsmul]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have key : ∀ y : Fv F v ⊗[F] E, y ∈ intLoc F E v → ∃ h : y ∈ intLoc F E v, (⟨y, h⟩ : intLoc F E v) ∈ N := by
    intro y hy
    refine intLoc_induction (p := fun y => ∃ h : y ∈ intLoc F E v, (⟨y, h⟩ : intLoc F E v) ∈ N)
      (fun a ha x => ⟨tmul_mem_intLoc ha x, ?_⟩) ⟨zero_mem _, zero_mem N⟩
      (fun y z ⟨hy, hy'⟩ ⟨hz, hz'⟩ => ⟨add_mem hy hz, add_mem hy' hz'⟩)
      (fun y ⟨hy, hy'⟩ => ⟨neg_mem hy, neg_mem hy'⟩) hy
    rw [tmul_eq_smul v ha x]
    exact N.smul_mem _ (hincl x)
  refine ⟨⟨Finset.univ.image fun i => intLocIncl v (b i), ?_⟩⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, eq_top_iff]
  rintro ⟨y, hy⟩ -
  obtain ⟨_, h⟩ := key y hy
  exact h

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

attribute [local instance] ovAlg

theorem extIdeal_map_eq (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    (extIdeal v).map (intLocIncl (E := E) v) =
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers (maximalRealSubfield E))).map
        (algebraMap (v.adicCompletionIntegers (maximalRealSubfield E)) (intLoc (maximalRealSubfield E) E v)) := by
  rw [← GlobalTheory.GaussCompletion.map_asIdeal, extIdeal, Ideal.map_map, Ideal.map_map]
  congr 1
  ext s
  change (1 : Fv (maximalRealSubfield E) v) ⊗ₜ[maximalRealSubfield E]
      ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : 𝓞 E) : E) =
    ((algebraMap (𝓞 (maximalRealSubfield E)) (v.adicCompletionIntegers (maximalRealSubfield E)) s :
      v.adicCompletionIntegers (maximalRealSubfield E)) : Fv (maximalRealSubfield E) v) ⊗ₜ[maximalRealSubfield E] (1 : E)
  exact GlobalTheory.SelfDualGenus.locEmb_algebraMap v s

theorem isAdicComplete : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      IsAdicComplete ((extIdeal v).map (intLocIncl (E := E) v)) (intLoc (maximalRealSubfield E) E v) := by
  intro E _ _ _ _ v
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := finite (E := E) v
  rw [extIdeal_map_eq]
  exact GlobalTheory.isAdicComplete_map_of_finite _ _

end GlobalTheory.TamOne.IntLocComplete
