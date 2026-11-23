import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesInjective
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitarySelfDualFrameToBaseLatticeFra
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowGood

open Matrix
open scoped TensorProduct

section Res

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def tr {F1 : Subfield E} (h : F1 = maximalRealSubfield E) : AL E →+* E ⊗[F1] Formalism.L2.Herm.Af F1 :=
  (GlobalTheory.LevSplit.swp F1 E).comp (GlobalTheory.Mem.R3.swapCast h).symm.toRingHom

theorem tr_rfl (z : AL E) : tr (rfl : maximalRealSubfield E = maximalRealSubfield E) z = z := by
  exact (Algebra.TensorProduct.comm _ _ _).apply_symm_apply z

theorem tr_int {F1 : Subfield E} (h : F1 = maximalRealSubfield E) {z : AL E} (hz : z ∈ ALint E) :
    tr h z ∈ Formalism.L2.Herm.intAf F1 E := by
  subst h
  rw [tr_rfl]
  have key : ReciprocityTheory.Aut.ALint E ≤ Formalism.L2.Herm.intAf (maximalRealSubfield E) E := by
    unfold ReciprocityTheory.Aut.ALint
    rw [Subring.closure_le]
    rintro x (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨(y : E), y, rfl⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact key hz

theorem proj_le_one (s : SplitPlace E) {z : AL E} (hz : z ∈ Formalism.L2.Herm.intAf (maximalRealSubfield E) E) :
    Valued.v (s.proj z) ≤ 1 := by
  have key : Formalism.L2.Herm.intAf (maximalRealSubfield E) E ≤
      (s.v.adicCompletionIntegers (maximalRealSubfield E)).toSubring.comap s.proj := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro x (⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap, ValuationSubring.mem_toSubring,
        IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      exact s.split_le_one b
    · rw [SetLike.mem_coe, Subring.mem_comap, ValuationSubring.mem_toSubring]
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact ha s.v
  have := key hz
  rwa [Subring.mem_comap, ValuationSubring.mem_toSubring,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem res_eq {F1 : Subfield E} (h : F1 = maximalRealSubfield E) (s : SplitPlace E) (z : AL E)
    (y : Formalism.L2.Herm.intAf F1 E) (hy : (y : E ⊗[F1] Formalism.L2.Herm.Af F1) = tr h z) (a : 𝓞 E)
    (ha : Valued.v (s.proj z - s.i (a : E)) < 1) : resS F1 s.w y = Ideal.Quotient.mk _ a := by
  subst h
  have key : ∀ (t : E ⊗[maximalRealSubfield E] Formalism.L2.Herm.Af (maximalRealSubfield E))
      (ht : t ∈ Formalism.L2.Herm.intAf (maximalRealSubfield E) E),
      ∃ c : 𝓞 E, Valued.v (s.proj t - s.i (c : E)) < 1 ∧
        resS (maximalRealSubfield E) s.w ⟨t, ht⟩ = Ideal.Quotient.mk _ c := by
    intro t ht
    refine Subring.closure_induction
      (p := fun t ht => ∃ c : 𝓞 E, Valued.v (s.proj t - s.i (c : E)) < 1 ∧
        resS (maximalRealSubfield E) s.w ⟨t, ht⟩ = Ideal.Quotient.mk _ c) ?_ ?_ ?_ ?_ ?_ ?_ ht
    · rintro x (⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
      · refine ⟨b, ?_, ?_⟩
        · simp [ReciprocityTheory.Aut.SplitPlace.proj]
        · have e : (⟨_, Subring.subset_closure (Or.inl ⟨⟨_, b, rfl⟩, rfl⟩)⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) =
              Formalism.L2.DIV.oToS (maximalRealSubfield E) E b :=
            Subtype.ext (Formalism.L2.DIV.oToS_coe (F := maximalRealSubfield E) b).symm
          rw [e, Formalism.L2.DIV.resS_oToS]
      · obtain ⟨D0, hD0, hD0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot s.v.ne_bot
        obtain ⟨r, hr⟩ := Formalism.UG.P.csApprox_local s.v D0 hD0ne (a s.v) (ha s.v)
        have hlt : s.v.intValuation D0 < 1 := by
          exact (s.v.intValuation_lt_one_iff_mem D0).mpr hD0
        have hi : s.i (((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r : 𝓞 E)) : E) =
            algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) r := by
          rw [ReciprocityTheory.Aut.split_coe_algebraMap, AlgHom.commutes,
            IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
              (s.v.adicCompletion (maximalRealSubfield E)) r]
        refine ⟨algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r, ?_, ?_⟩
        · have hp : s.proj ((1 : E) ⊗ₜ[maximalRealSubfield E] a) = a s.v := by
            simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
              Algebra.TensorProduct.lift_tmul, map_one, one_mul]
            rfl
          rw [hp, hi]
          exact hr.trans hlt
        · have hsplit : (⟨_, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) =
              Formalism.L2.DIV.adS (maximalRealSubfield E) E (⟨a, ha⟩ - Formalism.L2.DIV.oToAd (maximalRealSubfield E) r) +
                Formalism.L2.DIV.oToS (maximalRealSubfield E) E (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r) := by
            rw [← Formalism.L2.DIV.adS_oToAd, ← map_add, sub_add_cancel]
            exact Subtype.ext (Formalism.L2.DIV.adS_coe (E := E) ⟨a, ha⟩).symm
          rw [hsplit, map_add, Formalism.L2.DIV.resS_oToS, Formalism.L2.DIV.resS_adS_eq_zero s.w s.v s.w_under.symm, zero_add]
          show Valued.v (a s.v - algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) r) < 1
          exact hr.trans hlt
    · refine ⟨0, by simp, ?_⟩
      change resS (maximalRealSubfield E) s.w 0 = _
      simp
    · refine ⟨1, by simp, ?_⟩
      change resS (maximalRealSubfield E) s.w 1 = _
      simp
    · rintro x y hx hy ⟨c1, h1, e1⟩ ⟨c2, h2, e2⟩
      refine ⟨c1 + c2, ?_, ?_⟩
      · have : s.proj (x + y) - s.i ((c1 + c2 : 𝓞 E) : E) = (s.proj x - s.i (c1 : E)) + (s.proj y - s.i (c2 : E)) := by
          push_cast
          rw [map_add, map_add]
          ring
        rw [this]
        exact Valuation.map_add_lt _ h1 h2
      · change resS (maximalRealSubfield E) s.w (⟨x, hx⟩ + ⟨y, hy⟩) = _
        rw [map_add, e1, e2, map_add]
    · rintro x hx ⟨c1, h1, e1⟩
      refine ⟨-c1, ?_, ?_⟩
      · have : s.proj (-x) - s.i ((-c1 : 𝓞 E) : E) = -(s.proj x - s.i (c1 : E)) := by
          push_cast
          rw [map_neg, map_neg]
          ring
        rw [this, Valuation.map_neg]
        exact h1
      · change resS (maximalRealSubfield E) s.w (-⟨x, hx⟩) = _
        rw [map_neg, e1, map_neg]
    · rintro x y hx hy ⟨c1, h1, e1⟩ ⟨c2, h2, e2⟩
      refine ⟨c1 * c2, ?_, ?_⟩
      · have : s.proj (x * y) - s.i ((c1 * c2 : 𝓞 E) : E) =
            s.proj x * (s.proj y - s.i (c2 : E)) + (s.proj x - s.i (c1 : E)) * s.i (c2 : E) := by
          push_cast
          rw [map_mul, map_mul]
          ring
        rw [this]
        have hx1 : Valued.v (s.proj x) ≤ 1 := proj_le_one s hx
        have hc2 : Valued.v (s.i (c2 : E)) ≤ 1 := s.split_le_one c2
        refine Valuation.map_add_lt _ ?_ ?_
        · rw [Valuation.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' hx1) h2
        · rw [Valuation.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_right' hc2) h1
      · change resS (maximalRealSubfield E) s.w (⟨x, hx⟩ * ⟨y, hy⟩) = _
        rw [map_mul, e1, e2, map_mul]
  obtain ⟨c, hc1, hc2⟩ := key y.1 y.2
  have hyz : (y : E ⊗[maximalRealSubfield E] Formalism.L2.Herm.Af (maximalRealSubfield E)) = z := by rw [hy, tr_rfl]
  rw [hyz] at hc1
  have hca : Valued.v (s.i ((c - a : 𝓞 E) : E)) < 1 := by
    have : s.i ((c - a : 𝓞 E) : E) = (s.proj z - s.i (a : E)) - (s.proj z - s.i (c : E)) := by
      push_cast
      rw [map_sub]
      ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha hc1)
  have hmem : c - a ∈ s.w.asIdeal := (s.split_mem_ideal (c - a)).mpr hca
  have hyy : (⟨y.1, y.2⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) = y := rfl
  rw [hyy] at hc2
  rw [hc2]
  exact Ideal.Quotient.eq.mpr hmem

end Res

section Padic

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {g : ℕ} [Fact g.Prime]

end Padic

end GlobalTheory.RowGood

end

noncomputable section

namespace GlobalTheory.RowGood

open Matrix
open scoped TensorProduct

end GlobalTheory.RowGood

end
