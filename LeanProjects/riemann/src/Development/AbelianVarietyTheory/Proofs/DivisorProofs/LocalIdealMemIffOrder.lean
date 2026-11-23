import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedCompW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdealCountLeOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemStabLocStdLatticeIffHtFinEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open GlobalTheory.TateUnr

noncomputable section

namespace GlobalTheory.TateUnr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_tmul_mem_intLoc_of_valuation {v : Pl F} {e : E}
    (he : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w.valuation E e ≤ 1) :
    (1 : Fv F v) ⊗ₜ[F] e ∈ intLoc F E v := by
  classical
  let J : Ideal (𝓞 E) := (1 : Submodule (𝓞 E) E).colon {e}
  have key : ¬ J.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal := by
    intro hle
    obtain ⟨Q, hJQ, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal J hle
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [← hQv]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
    let w : HeightOneSpectrum (𝓞 E) := ⟨Q, hQ, hQ0⟩
    have hw : w.under (𝓞 F) = v := HeightOneSpectrum.ext hQv
    have h1 : e ∈ HeightOneSpectrum.valuationSubringAtPrime E w := by
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]; exact he w hw
    obtain ⟨a, s, hs, hae⟩ := h1
    have hsJ : s ∈ J := by
      rw [Submodule.mem_colon_singleton, Submodule.mem_one]
      refine ⟨a, ?_⟩
      have hs0 : algebraMap (𝓞 E) E s ≠ 0 := by
        intro h0
        apply hs
        rw [(IsFractionRing.injective (𝓞 E) E) (h0.trans (map_zero _).symm)]
        exact zero_mem _
      rw [Algebra.smul_def, hae, mul_left_comm, mul_inv_cancel₀ hs0, mul_one]
    exact hs (hJQ hsJ)
  obtain ⟨d, hdJ, hdv⟩ := Set.not_subset.1 key
  rw [SetLike.mem_coe, Ideal.mem_comap, Submodule.mem_colon_singleton, Submodule.mem_one] at hdJ
  obtain ⟨x, hx⟩ := hdJ
  have hv : v.valuation F (d : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hdv
  have hd0 : (d : F) ≠ 0 := fun e => by simp [e] at hv
  have h4 : algebraMap F (Fv F v) (d : F)⁻¹ ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (d : F)⁻¹).trans_le (by rw [map_inv₀, hv, inv_one])
  have hx' : ((x : 𝓞 E) : E) = (d : F) • e := by
    refine hx.trans ?_
    rw [algebraMap_smul]
    exact (algebraMap_smul F d e).symm
  have h := tmul_mem_intLoc (E := E) h4 x
  convert h using 1
  rw [hx', Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, inv_smul_smul₀ hd0]

theorem mem_intLoc_of_toCompl {v : Pl F} {y : Fv F v ⊗[F] E}
    (hy : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : w.under (𝓞 F) = v), Valued.v (toCompl hw y) ≤ 1) :
    y ∈ intLoc F E v := by
  obtain ⟨e, he⟩ := exists_sub_mem_intLoc v y
  have h1 : (1 : Fv F v) ⊗ₜ[F] e ∈ intLoc F E v := by
    refine one_tmul_mem_intLoc_of_valuation fun w hw => ?_
    have h2 : toCompl hw ((1 : Fv F v) ⊗ₜ[F] e) = toCompl hw y - toCompl hw (y - (1 : Fv F v) ⊗ₜ[F] e) := by
      rw [map_sub, sub_sub_cancel]
    have h3 : Valued.v (toCompl hw (y - (1 : Fv F v) ⊗ₜ[F] e)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (InertChart.toCompl_mem hw he)
    have h4 := Valuation.map_sub_le _ (hy w hw) h3
    rw [← h2, toCompl_tmul, map_one, one_mul] at h4
    have h5 : Valued.v (algebraMap E (w.adicCompletion E) e) = w.valuation E e :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w e
    rw [← h5]
    exact h4
  have := add_mem he h1
  rwa [sub_add_cancel] at this

theorem one_tmul_mul_mem_locId {v : Pl F} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} {i : E} (hi : i ∈ 𝔞)
    {z : Fv F v ⊗[F] E} (hz : z ∈ intLoc F E v) : (1 : Fv F v) ⊗ₜ[F] i * z ∈ locId v 𝔞 := by
  refine intLoc_induction (p := fun z => (1 : Fv F v) ⊗ₜ[F] i * z ∈ locId v 𝔞) (fun a ha x => ?_)
    (by rw [mul_zero]; exact zero_mem _) (fun y z hy hz => by rw [mul_add]; exact add_mem hy hz)
    (fun y hy => by rw [mul_neg]; exact neg_mem hy) hz
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  refine tmul_mem_locId ha ?_
  have := (𝔞 : Submodule (𝓞 E) E).smul_mem x hi
  rwa [Algebra.smul_def, mul_comm] at this

theorem mem_locId_iff_count_le_ordV : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : Pl F) (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 𝔞 ≠ 0 → ∀ l : idelesAt E (evFin F v),
    (compFin F E v (l.1 : AE F E) ∈ locId v 𝔞 ↔
      ∀ w : aboveF (L := E) F v, FractionalIdeal.count E w.1 𝔞 ≤ ordV v l w) := by
  intro F E _ _ _ _ _ v 𝔞 h𝔞 l
  have hval : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : w.under (𝓞 F) = v),
      Valued.v (toCompl hw (compFin F E v (l.1 : AE F E))) = WithZero.exp (-ordW hw l) := fun w hw => by
    rw [← compW_apply]; exact valued_compW hw l
  constructor
  · intro hY w
    have hw := mem_aboveF.1 w.2
    have h0 : ∀ y ∈ locId v 𝔞, Valued.v (toCompl hw y) ≤ WithZero.exp (-FractionalIdeal.count E w.1 𝔞) := by
      intro y hY
      induction hY using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨c, hc, x, hx, rfl⟩ := hy
        have h2 : Valued.v (algebraMap E (w.1.adicCompletion E) x) = w.1.valuation E x :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w.1 x
        rw [toCompl_tmul, map_mul, h2]
        have h3 : Valued.v (complMap hw c) ≤ 1 :=
          (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (complMap_mem hw hc)
        exact (mul_le_mul' h3 (GlobalTheory.UnrTate.valuation_le_of_mem w.1 hx)).trans_eq (one_mul _)
      | zero => rw [map_zero, map_zero]; exact zero_le'
      | add y z _ _ hy hz => rw [map_add]; exact Valuation.map_add_le _ hy hz
      | neg y _ hy => rw [map_neg, Valuation.map_neg]; exact hy
    have h1 := h0 _ hY
    rw [hval, WithZero.exp_le_exp] at h1
    change FractionalIdeal.count E w.1 𝔞 ≤ ordW hw l
    linarith
  · intro h
    have key : ∀ z ∈ 𝔞 * 𝔞⁻¹, (1 : Fv F v) ⊗ₜ[F] z * compFin F E v (l.1 : AE F E) ∈ locId v 𝔞 := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz (fun i hi j hj => ?_) (fun x y hx hy => ?_)
      · rw [← mul_one (1 : Fv F v), ← Algebra.TensorProduct.tmul_mul_tmul, mul_assoc]
        refine one_tmul_mul_mem_locId hi (mem_intLoc_of_toCompl fun w hw => ?_)
        have h2 : Valued.v (algebraMap E (w.adicCompletion E) j) = w.valuation E j :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w j
        rw [map_mul, map_mul, hval, toCompl_tmul, map_one, one_mul, h2]
        have hc := h ⟨w, mem_aboveF.2 hw⟩
        change FractionalIdeal.count E w 𝔞 ≤ ordW hw l at hc
        calc w.valuation E j * WithZero.exp (-ordW hw l)
            ≤ WithZero.exp (-FractionalIdeal.count E w 𝔞⁻¹) * WithZero.exp (-FractionalIdeal.count E w 𝔞) :=
              mul_le_mul' (GlobalTheory.UnrTate.valuation_le_of_mem w hj) (WithZero.exp_le_exp.2 (by linarith))
          _ = 1 := by
              rw [FractionalIdeal.count_inv, neg_neg, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
      · rw [TensorProduct.tmul_add, add_mul]; exact add_mem hx hy
    have h1 : (1 : E) ∈ 𝔞 * 𝔞⁻¹ := by
      rw [mul_inv_cancel₀ h𝔞]; exact FractionalIdeal.one_mem_one _
    have := key 1 h1
    rwa [← Algebra.TensorProduct.one_def, one_mul] at this

end GlobalTheory.TateUnr
