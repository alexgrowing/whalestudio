import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompMemOfIsStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleRestrictedProductStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleRestrictedProductHaarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerNormalizedHaarRestrictedStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeMeas

open GlobalTheory.RestrMeas

theorem integral_comp_euler : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n r s : ℕ} {X : Spc F E n}, B.IsGood σ → X.IsHerm σ B r s →
    ∀ {K : Subgroup (UA σ X.J)}, IsStab B K →
    ∀ (μK : Measure K) (μ : Measure (AE F E)ˣ), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ (μKI : Measure (KAt K (evI F))) (μI : Measure (idelesAt E (evI F))), IsNormK K (evI F) μKI → μI.IsHaarMeasure →
    ∀ (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))) (μv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))),
    (∀ v, IsNormK K (evFin F v) (μKv v)) → (∀ v, IsNormE E v (μv v)) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ (T : Finset (Pl F)) (H : UA σ X.J → (AE F E)ˣ → ℂ) (Q : Pl F → UA σ X.J → (AE F E)ˣ → ℂ)
      (g : Pl F → (AE F E)ˣ → ℂ),
      Integrable (fun p : KAt K (evI F) × idelesAt E (evI F) => H p.1.1 p.2.1) (μKI.prod μI) →
      (∀ k ∈ KAt K (evI F), Integrable (fun l : idelesAt E (evI F) => H k l.1) μI) →
      (∀ v ∈ T, Integrable (fun p : KAt K (evFin F v) × idelesAt E (evFin F v) => Q v p.1.1 p.2.1) ((μKv v).prod (μv v))) →
      (∀ v ∈ T, ∀ k ∈ KAt K (evFin F v), Integrable (fun l : idelesAt E (evFin F v) => Q v k l.1) (μv v)) →
      (∀ v ∉ T, ∀ l l' : (AE F E)ˣ, l ∈ idelesAt E (evFin F v) → l⁻¹ * l' ∈ unitsAt E v → g v l' = g v l) →
      (∀ᶠ v in cofinite, ∀ l ∈ unitsAt E v, g v l = 1) →
      (∀ v ∉ T, Integrable (fun l : idelesAt E (evFin F v) => g v l.1) (μv v)) →
      Summable (fun v : {v : Pl F // v ∉ T} => ∫ l : idelesAt E (evFin F v.1), ‖g v.1 l.1‖ ∂(μv v.1) - 1) →
      (∀ k : K, Integrable (fun l => H (compArch σ X.J k.1) (unitArch F E l) *
          (∏ v ∈ T, Q v (compAt σ X.J v k.1) (unitAt E v l)) * ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l)) μ) ∧
      Integrable (fun k : K => ∫ l, H (compArch σ X.J k.1) (unitArch F E l) *
          (∏ v ∈ T, Q v (compAt σ X.J v k.1) (unitAt E v l)) * ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l) ∂μ) μK ∧
      ∫ k : K, ∫ l, H (compArch σ X.J k.1) (unitArch F E l) *
          (∏ v ∈ T, Q v (compAt σ X.J v k.1) (unitAt E v l)) * ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l) ∂μ ∂μK =
        κ * (∫ k : KAt K (evI F), ∫ l : idelesAt E (evI F), H k.1 l.1 ∂μI ∂μKI) *
          (∏ v ∈ T, ∫ k : KAt K (evFin F v), ∫ l : idelesAt E (evFin F v), Q v k.1 l.1 ∂(μv v) ∂(μKv v)) *
          ∏' v : {v : Pl F // v ∉ T}, ∫ l : idelesAt E (evFin F v.1), g v.1 l.1 ∂(μv v.1) := by
  intro F E _ _ _ _ _ σ B n r s X hB hX K hK μK μ hμK hμ μKI μI hKI hμI μKv μv hKv hv
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI : ∀ v : Pl F, IsTopologicalGroup (idelesAt E (evFin F v)) := fun v => (idelesAt_facts E (evFin F v)).1
  haveI : ∀ v : Pl F, LocallyCompactSpace (idelesAt E (evFin F v)) := fun v => (idelesAt_facts E (evFin F v)).2.1
  haveI : ∀ v : Pl F, SecondCountableTopology (idelesAt E (evFin F v)) := fun v => (idelesAt_facts E (evFin F v)).2.2.1
  haveI : ∀ v : Pl F, T2Space (idelesAt E (evFin F v)) := fun v => (idelesAt_facts E (evFin F v)).2.2.2.1
  haveI : ∀ v : Pl F, BorelSpace (idelesAt E (evFin F v)) := fun v => (idelesAt_facts E (evFin F v)).2.2.2.2
  haveI : ∀ w : Unit, ((fun _ : Unit => μI) w).IsHaarMeasure := fun _ => hμI
  haveI : ∀ v : Pl F, (μv v).IsHaarMeasure := fun v => (hv v).1
  obtain ⟨ν, hν, -⟩ := (GlobalTheory.T.idele_restricted_product_structure (F := F) (E := E)).existsUnique_isHaarProd (fun _ => μI) μv
    (Eventually.of_forall fun v => (hv v).2)
  haveI := hν.2.2.1
  haveI := hμ
  have hsc : μ = Measure.haarScalarFactor μ ν • ν := Measure.isMulLeftInvariant_eq_smul μ ν
  have hcpos : 0 < Measure.haarScalarFactor μ ν := Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν
  set c := Measure.haarScalarFactor μ ν
  obtain ⟨κK, hκK, hKp⟩ := GlobalTheory.T.stabilizer_normalized_haar_restricted B hB hX hK μK hμK μKI hKI μKv hKv
  refine ⟨(c : ℝ) * κK, mul_pos (by exact_mod_cast hcpos) hκK, ?_⟩
  intro T H Q g hH hHk hQ hQk hg1 hg2 hg3 hg4
  have idel : ∀ (h : (AE F E)ˣ → ℂ) (q : Pl F → (AE F E)ˣ → ℂ),
      Integrable (fun l : idelesAt E (evI F) => h l.1) μI →
      (∀ v ∈ T, Integrable (fun l : idelesAt E (evFin F v) => q v l.1) (μv v)) →
      Integrable (fun l => h (unitArch F E l) * (∏ v ∈ T, q v (unitAt E v l)) *
          ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l)) μ ∧
      ∫ l, h (unitArch F E l) * (∏ v ∈ T, q v (unitAt E v l)) * ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l) ∂μ =
        (c : ℂ) * ((∫ l : idelesAt E (evI F), h l.1 ∂μI) * (∏ v ∈ T, ∫ l : idelesAt E (evFin F v), q v l.1 ∂(μv v)) *
          ∏' v : {v : Pl F // v ∉ T}, ∫ l : idelesAt E (evFin F v.1), g v.1 l.1 ∂(μv v.1)) := by
    intro h q hh hq
    obtain ⟨hi, he⟩ := GlobalTheory.T.idele_restricted_product_haar μI hμI μv hv ν hν.2.2.2 T h q g hh hq hg2 hg3 hg4
    rw [hsc]
    refine ⟨hi.smul_measure_nnreal, ?_⟩
    rw [integral_smul_nnreal_measure, he, NNReal.smul_def, Complex.real_smul]
  have hmem := fun (k : K) => GlobalTheory.ThK.ConeEuler.StabComp.comp_mem_of_isStab F E σ B n X K hK k.1 k.2
  have hA : ∀ k : K, compArch σ X.J k.1 ∈ KAt K (evI F) := fun k => ⟨(hmem k).2, compArch_mem k.1⟩
  have hV : ∀ (k : K) v, compAt σ X.J v k.1 ∈ KAt K (evFin F v) := fun k v => ⟨(hmem k).1 v, compAt_mem v k.1⟩
  have inner := fun k : K => idel (H (compArch σ X.J k.1)) (fun v => Q v (compAt σ X.J v k.1))
    (hHk _ (hA k)) (fun v hvT => hQk v hvT _ (hV k v))
  haveI : IsFiniteMeasure μKI := ⟨by rw [hKI.2]; exact ENNReal.one_lt_top⟩
  have ha : Integrable (fun k : KAt K (evI F) => ∫ l : idelesAt E (evI F), H k.1 l.1 ∂μI) μKI :=
    hH.integral_prod_left
  have hb : ∀ v ∈ T, Integrable (fun k : KAt K (evFin F v) =>
      ∫ l : idelesAt E (evFin F v), Q v k.1 l.1 ∂(μv v)) (μKv v) := fun v hvT => by
    haveI : IsFiniteMeasure (μKv v) := ⟨by rw [(hKv v).2]; exact ENNReal.one_lt_top⟩
    exact (hQ v hvT).integral_prod_left
  obtain ⟨hi, he⟩ := hKp T (fun k => ∫ l : idelesAt E (evI F), H k l.1 ∂μI)
    (fun v k => ∫ l : idelesAt E (evFin F v), Q v k l.1 ∂(μv v)) ha hb
  have hfun : (fun k : K => ∫ l, H (compArch σ X.J k.1) (unitArch F E l) *
      (∏ v ∈ T, Q v (compAt σ X.J v k.1) (unitAt E v l)) * ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l) ∂μ) =
      fun k : K => ((c : ℂ) * ∏' v : {v : Pl F // v ∉ T}, ∫ l : idelesAt E (evFin F v.1), g v.1 l.1 ∂(μv v.1)) *
        ((∫ l : idelesAt E (evI F), H (compArch σ X.J k.1) l.1 ∂μI) *
          ∏ v ∈ T, ∫ l : idelesAt E (evFin F v), Q v (compAt σ X.J v k.1) l.1 ∂(μv v)) := by
    funext k
    rw [(inner k).2]
    ring
  refine ⟨fun k => (inner k).1, ?_, ?_⟩
  · rw [hfun]
    exact hi.const_mul _
  · rw [hfun, integral_const_mul, he]
    push_cast
    ring

end GlobalTheory.ConeMeas
