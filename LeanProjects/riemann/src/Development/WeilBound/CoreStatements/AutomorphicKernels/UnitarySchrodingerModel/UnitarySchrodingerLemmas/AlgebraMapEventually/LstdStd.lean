import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open NumberField IsDedekindDomain GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace PositivityTheory.PfSWUS.SwsLstd

open PositivityTheory.PfSWUS.SwFockk

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isCO_lstd (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) : PositivityTheory.SiegelWeilFormula.Gen.IsCO (lstd F E n v) := by
  obtain ⟨hc, ho⟩ := GlobalTheory.ThK.isCompact_isOpen_intLoc (F := F) (E := E) v
  have e : (lstd F E n v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) =
      Set.univ.pi fun _ => (GlobalTheory.AdelicU.intLoc F E v : Set (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) := by
    ext y
    simp only [Set.mem_univ_pi]
    rfl
  refine ⟨?_, ?_⟩
  · rw [e]; exact isOpen_set_pi Set.finite_univ fun _ _ => ho
  · rw [e]; exact isCompact_univ_pi fun _ => hc

theorem eventually_algebraMap_mem (c : F) :
    ∀ᶠ v in Filter.cofinite, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) c ∈ v.adicCompletionIntegers F :=
  (FiniteAdeleRing.algebraMap (𝓞 F) F c).2

theorem eventually_mem_intLoc_iff {d : ℕ} (bs : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ z : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E, z ∈ GlobalTheory.AdelicU.intLoc F E v ↔
      ∀ k, (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs).repr z k ∈ v.adicCompletionIntegers F := by
  classical
  have hint : ∀ y : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : F) • y) := fun y => by
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic y)).exists_integral_multiple
    exact ⟨m, hm, by rwa [Int.cast_smul_eq_zsmul]⟩
  choose m hm hmi using hint
  let b := RingOfIntegers.basis E
  have h1 : ∀ᶠ v in Filter.cofinite, ∀ i k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)
      (bs.repr ((b i : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k => eventually_algebraMap_mem _
  have h2 : ∀ᶠ v in Filter.cofinite, ∀ k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) ((m (bs k) : F))⁻¹ ∈
      v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => eventually_algebraMap_mem _
  filter_upwards [h1, h2] with v hv1 hv2 z
  set B := Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs
  constructor
  · intro hz
    refine GlobalTheory.AdelicU.intLoc_induction (p := fun y => ∀ k, B.repr y k ∈ v.adicCompletionIntegers F)
      ?_ ?_ ?_ ?_ hz
    · intro a ha x k
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
      refine mul_mem ha ?_
      have hx : (x : E) = ∑ i, (b.repr x i) • ((b i : 𝓞 E) : E) := by
        conv_lhs => rw [← b.sum_repr x]
        simp only [map_sum, map_zsmul, RingOfIntegers.coe_eq_algebraMap]
      rw [hx, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
      refine Subring.sum_mem _ fun i _ => ?_
      rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
      exact zsmul_mem (hv1 i k) _
    · intro k; simp
    · intro y z hy hz k; rw [map_add, Finsupp.add_apply]; exact add_mem (hy k) (hz k)
    · intro y hy k; rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hy k)
  · intro hz
    rw [← B.sum_repr z]
    refine Subring.sum_mem _ fun k _ => ?_
    have hm0 : ((m (bs k) : ℤ) : F) ≠ 0 := by exact_mod_cast hm (bs k)
    have e : B.repr z k • B k = (algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) ((m (bs k) : F))⁻¹ * B.repr z k) ⊗ₜ[F]
        ((⟨(m (bs k) : F) • bs k, hmi (bs k)⟩ : 𝓞 E) : E) := by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← Algebra.smul_def,
        TensorProduct.smul_tmul]
      congr 1
      change bs k = ((m (bs k) : F))⁻¹ • ((m (bs k) : F) • bs k)
      rw [smul_smul, inv_mul_cancel₀ hm0, one_smul]
    rw [e]
    exact GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (mul_mem (hv2 k) (hz k)) (⟨(m (bs k) : F) • bs k, hmi (bs k)⟩ : 𝓞 E)

theorem lstdStd : LstdStd := by
  intro F E _ _ _ _ _ n
  refine ⟨fun v => isCO_lstd n v, fun d bs => ?_⟩
  filter_upwards [eventually_mem_intLoc_iff bs] with v hv
  ext y
  change (∀ i, y i ∈ GlobalTheory.AdelicU.intLoc F E v) ↔ _
  simp only [PositivityTheory.PfSWUS.Loc.latO, Set.mem_ofPred_eq]
  exact forall_congr' fun a => hv (y a)

end PositivityTheory.PfSWUS.SwsLstd

end
