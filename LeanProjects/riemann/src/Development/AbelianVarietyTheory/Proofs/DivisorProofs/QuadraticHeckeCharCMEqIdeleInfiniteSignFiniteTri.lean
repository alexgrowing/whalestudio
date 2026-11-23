import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupDivEqMulDivMulInvDiv
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EtaInfSign

open GlobalTheory.QuadSymbol

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem mem_normGroup_of_pos (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ)
    (hy : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion)) :
    y ∈ normGroup (maximalRealSubfield E) E v.Completion := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq (maximalRealSubfield E) E
  rw [mem_normGroup_iff_form b h0 h1]
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hy' : 0 < e y := hy
  refine ⟨e.symm (Real.sqrt (e y)), 0, e.injective ?_⟩
  simp only [map_sub, map_pow, map_mul, map_zero, RingEquiv.apply_symm_apply]
  rw [zero_pow two_ne_zero, mul_zero, sub_zero, Real.sq_sqrt hy'.le]

theorem not_mem_normGroup_of_neg (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ)
    (hy : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion) < 0) :
    y ∉ normGroup (maximalRealSubfield E) E v.Completion := by
  intro hmem
  have hneg : (-y) ∈ normGroup (maximalRealSubfield E) E v.Completion := by
    refine mem_normGroup_of_pos E v (-y) ?_
    rw [Units.val_neg, map_neg]
    exact neg_pos.2 hy
  have h1 : (-1 : (v.Completion)ˣ) ∈ normGroup (maximalRealSubfield E) E v.Completion := by
    have : (-1 : (v.Completion)ˣ) = y * (-y)⁻¹ := by
      rw [inv_neg, mul_neg, mul_inv_cancel]
    rw [this]
    exact mul_mem hmem (inv_mem hneg)
  exact eta_eq_neg_one_iff.1 (GlobalTheory.GalOfCusp.eta_neg_one E v) h1

theorem eta_real (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ) :
    eta (maximalRealSubfield E) E v.Completion y =
      if 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion)
      then 1 else -1 := by
  split_ifs with h
  · exact eta_eq_one_iff.2 (mem_normGroup_of_pos E v y h)
  · have h0 : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion) ≠ 0 :=
      fun h' => y.ne_zero ((InfinitePlace.Completion.extensionEmbeddingOfIsReal _).injective (h'.trans (map_zero _).symm))
    exact eta_eq_neg_one_iff.2 (not_mem_normGroup_of_neg E v y (lt_of_le_of_ne (not_lt.1 h) h0))

theorem embedding_comp_algebraMap (w : InfinitePlace E) :
    (w.comap (algebraMap (maximalRealSubfield E) E)).embedding =
      w.embedding.comp (algebraMap (maximalRealSubfield E) E) := by
  have hw : w.comap (algebraMap (maximalRealSubfield E) E) =
      InfinitePlace.mk (w.embedding.comp (algebraMap (maximalRealSubfield E) E)) := by
    conv_lhs => rw [← InfinitePlace.mk_embedding w]
    rw [InfinitePlace.comap_mk]
  rw [hw]
  rcases InfinitePlace.embedding_mk_eq (w.embedding.comp (algebraMap (maximalRealSubfield E) E)) with h | h
  · exact h
  · rw [h]
    exact ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal _)

theorem extensionEmbedding_completionMap (w : InfinitePlace E)
    (x : (w.comap (algebraMap (maximalRealSubfield E) E)).Completion) :
    InfinitePlace.Completion.extensionEmbedding w
      (NumberField.LiesOver.completionMap (v := w.comap (algebraMap (maximalRealSubfield E) E)) (w := w) x) =
    ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal _) x : ℝ) : ℂ) := by
  induction x using InfinitePlace.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
        NumberField.LiesOver.continuous_completionMap)
      (Complex.continuous_ofReal.comp (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous)
  | ih a =>
    rw [NumberField.LiesOver.completionMap_coe, InfinitePlace.Completion.extensionEmbedding_coe,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, InfinitePlace.embedding_of_isReal_apply,
      embedding_comp_algebraMap]
    simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]

theorem unitDir_ofReal (r : ℝ) (hr : r ≠ 0) (u : ℂˣ) (hu : (u : ℂ) = r) :
    GlobalTheory.ConsEta.unitDir u = Units.map (Int.castRingHom ℂ).toMonoidHom (if 0 < r then 1 else -1) := by
  ext
  change (u : ℂ) / (‖(u : ℂ)‖ : ℂ) = _
  rw [hu, Complex.norm_real, Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_of_pos h, div_self (Complex.ofReal_ne_zero.2 hr)]
    simp
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hr), Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.2 hr)]
    simp

end GlobalTheory.EtaInfSign

open GlobalTheory.QuadSymbol in

theorem GlobalTheory.EtaInfSign.quadChar_eq_infSign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    (∀ v, (b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 v = 1) →
    (GlobalTheory.GalOfCusp.quadChar E).1 b = GlobalTheory.ConsEta.infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) := by
  intro E _ _ _ b hb
  have hfin : GlobalTheory.IdeleNormChar.finComp b = 1 := funext fun v => Units.ext (hb v)
  have hL : (GlobalTheory.GalOfCusp.quadChar E).1 b = Units.map (Int.castRingHom ℂ).toMonoidHom
      (∏ v : InfinitePlace (maximalRealSubfield E),
        eta (maximalRealSubfield E) E v.Completion (GlobalTheory.IdeleNormChar.infComp b v)) := by
    change Units.map _ (etaProd _ E (GlobalTheory.IdeleNormChar.finComp b) (GlobalTheory.IdeleNormChar.infComp b)) = _
    unfold etaProd
    rw [hfin]
    have h1 : (fun v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) =>
        eta (maximalRealSubfield E) E (v.adicCompletion _) ((1 : FinFam (maximalRealSubfield E)) v)) = fun _ => 1 :=
      funext fun v => eta_eq_one_iff.2 (one_mem _)
    rw [h1, finprod_one, one_mul]
  rw [hL, map_prod, GlobalTheory.ConsEta.infSign, MonoidHom.finset_prod_apply]
  symm
  refine Fintype.prod_equiv (IsCMField.equivInfinitePlace E) _ _ fun w => ?_
  rw [IsCMField.equivInfinitePlace_apply, GlobalTheory.EtaInfSign.eta_real]
  have hv := IsTotallyReal.isReal (w.comap (algebraMap (maximalRealSubfield E) E))
  refine GlobalTheory.EtaInfSign.unitDir_ofReal _ ?_ _ ?_
  · intro h'
    exact (GlobalTheory.IdeleNormChar.infComp b _).ne_zero
      ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective (by rw [map_zero]; exact h'))
  · exact GlobalTheory.EtaInfSign.extensionEmbedding_completionMap E w _
