import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictDef
import Development.WeilBound.CoreStatements.TorusUniformisation.SiegelCompactSupport.ExistsRouteDatumTranslationCombinationGoodPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaHeisenbergTranslatesSeparate
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.Member.ZakTransform MeasureTheory Topology
open GlobalTheory.EmbChart (tensAt compFin_tensAt tensAt_mul_right tensAt_tmul)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem modu_eq (u : (AF F)ˣ) : ((distribHaarChar (AF F) u : NNReal) : ℝ) = GroundTheory.Global.IdeleGroup.ideleModule F u := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := inferInstance
  have : (GroundTheory.Global.adeleMeasure F).Regular := by
    obtain ⟨K⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (AdeleRing (𝓞 F) F)))
    exact Measure.regular_of_isAddLeftInvariant K.isCompact K.interior_nonempty K.isCompact.measure_lt_top.ne
  have h0 := (GroundTheory.Global.IdeleGroup.ideleModule F u).2
  have key : distribHaarChar (AdeleRing (𝓞 F) F) u = NNReal.mk _ h0.le := by
    refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := GroundTheory.Global.adeleMeasure F)
      (s := GroundTheory.Global.fundamentalSet F) ?_ ?_ ?_
    · rw [GroundTheory.Global.adeleMeasure_fundamentalSet]; exact one_ne_zero
    · rw [GroundTheory.Global.adeleMeasure_fundamentalSet]; exact ENNReal.one_ne_top
    · rw [← ENNReal.ofReal_eq_coe_nnreal h0.le]
      exact GroundTheory.Global.adeleMeasure_smul (K := F) u (GroundTheory.Global.fundamentalSet F)
  exact congrArg NNReal.toReal key

theorem modu_single (u : (AF F)ˣ) (x : (Fv F v)ˣ) (h : (u : AF F) = 1 - sgl v 1 + sgl v x) :
    ((distribHaarChar (AF F) u : NNReal) : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) x := by
  rw [modu_eq, GroundTheory.Global.IdeleGroup.ideleModule_apply]
  have h1 : ∀ w, (u : AF F).1 w = 1 := fun w => by
    rw [h]
    change (1 : Ainf F) w - (0 : Ainf F) w + (0 : Ainf F) w = 1
    rw [sub_add_cancel]
    rfl
  have h2 : ∀ w, (u : AF F).2 w = 1 - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v 1) + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v x) :=
    fun w => by rw [h]; rfl
  have h3 : GroundTheory.Global.IdeleGroup.infiniteModule u = 1 := Finset.prod_eq_one fun w _ => by
    change ‖(u : AF F).1 w‖ ^ _ = 1
    rw [h1, norm_one, one_pow]
  have h4 : GroundTheory.Global.IdeleGroup.finiteModule u = ‖(x : Fv F v)‖ := by
    change ∏ᶠ w, ‖(u : AF F).2 w‖ = _
    rw [finprod_eq_single _ v fun w hw => by rw [h2, evalV_singleFin_ne hw, evalV_singleFin_ne hw, sub_add_cancel, norm_one],
      h2, evalV_singleFin_self, evalV_singleFin_self, sub_self, zero_add]
  rw [h3, h4, one_mul, GlobalTheory.SplitWeil.nabs]
  have := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v (x : Fv F v) x.ne_zero
  rw [Units.mk0_val] at this
  exact (congrArg NNReal.toReal this).symm

theorem off_of_at {z : AE F E} (h : At (evFin F v) (z - 1)) : (1 - ep v) • z = (1 - ep v) • (1 : AE F E) := by
  have := (at_iff _).1 h
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, this, sub_self]

theorem norm_eq (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {z : AE F E} {x : Fv F v} (hz : At (evFin F v) (z - 1))
    (h1 : piW t z = x) (h2 : piW (t.comp σ) z = 1) : Algebra.norm (AF F) z = 1 - sgl v 1 + sgl v x := by
  have hi : Function.Injective (algebraMap (AF F) (AE F E)) := Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  apply hi
  rw [GlobalTheory.Doubling.algebraMap_norm_eq h]
  change z * cA σ z = _
  have e : ∀ a : AF F, algebraMap (AF F) (AE F E) a = a • (1 : AE F E) := fun a => Algebra.algebraMap_eq_smul_one a
  have es : ∀ a, sgl v a = ep v * sgl v a := fun a => by
    rw [ep_mul]
    exact congrArg (sgl v) (evalV_singleFin_self v a).symm
  have ev : ∀ a, evFin F v (sgl v a) = a := evalV_singleFin_self v
  have o := off_of_at hz
  refine AE_ext h t ?_ ?_ ?_
  · rw [← smul_mul_assoc, o, smul_mul_assoc, one_mul, ← map_smul, o, map_smul, map_one, e, smul_smul]
    congr 1
    change _ = (1 - ep v) * (1 - ep v + sgl v x)
    rw [es x]
    linear_combination (1 - sgl v x) * (-ep_ep (v := v))
  · rw [map_mul, piW_cA, h1, h2, e, piW_smul, map_add, map_sub, ev, ev, map_one, map_one]
    ring
  · rw [map_mul, piW_cA, comp_conj_conj h, h1, h2, e, piW_smul, map_add, map_sub, ev, ev, map_one, map_one]
    ring

theorem eq_locIdele (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {z : (AE F E)ˣ} {x : (Fv F v)ˣ} (hz : At (evFin F v) ((z : AE F E) - 1))
    (h1 : piW t z = x) (h2 : piW (t.comp σ) z = 1) :
    z = locIdele F (splitPrime t) (Units.map (complMap (splitPrime_under t)).toMonoidHom x) := by
  classical
  let y : (Fv F v ⊗[F] E)ˣ := Units.map (compFin F E v).toMonoidHom z
  have e1 : z = GlobalTheory.Doubling.ideleAt F E v y := Units.ext (by
    change (z : AE F E) = 1 - tensAt E v 1 + tensAt E v (compFin F E v z)
    have o := off_of_at hz
    rw [← ep_smul, ← map_one (compFin F E v), ← ep_smul]
    rw [sub_smul, sub_smul, one_smul, one_smul] at o
    rw [← o, sub_add_cancel])
  rw [e1, ideleAt_eq_prod_locIdele]
  have hm : splitPrime t ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset :=
    (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.2 (splitPrime_under t)
  rw [Finset.prod_eq_single_of_mem ⟨splitPrime t, hm⟩ (Finset.mem_attach _ _)]
  · congr 1
    exact Units.ext ((ConjPlace.toCompl_eq h _ rfl _).trans (congrArg _ h1))
  · rintro ⟨w, hw⟩ - hb
    have hne : w ≠ splitPrime t := fun e => hb (Subtype.ext e)
    have hw' := (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 hw
    obtain ⟨ρ, hρ, -⟩ := existsUnique_splitPrime_eq h hne hw' (splitPrime_under t)
    obtain rfl : ρ = t.comp σ := (eq_or_eq_comp_conj h t ρ).resolve_left fun k => hne (hρ.symm.trans (k ▸ rfl))
    rw [← map_one (locIdele F w)]
    congr 1
    exact Units.ext ((ConjPlace.toCompl_eq h _ hρ _).trans ((congrArg _ h2).trans (map_one _)))

theorem usm_chrW (t : E →ₐ[F] Fv F v) {χ : Chr F E} (hχ : Continuous χ) : USm (chrW χ t) := by
  let μ : (Fv F v)ˣ →* Circle := (χ.comp (locIdele F (splitPrime t))).comp (Units.map (complMap (splitPrime_under t)).toMonoidHom)
  have hμ : Continuous μ := (hχ.comp (continuous_locIdele _)).comp
    (Continuous.units_map _ (SplitChart.continuous_complMap (splitPrime_under t)))
  refine ⟨fun x => Circle.norm_coe (μ x), Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_⟩
  filter_upwards [eventually_char_eq_one μ hμ] with x hx
  change Circle.toUnits (μ x) = 1
  rw [hx.1, map_one]

theorem section_statement : SecSt := by
  intro F E _ _ _ _ _ σ h v t
  refine ⟨⟨fun x => tensAt E v ((splitAlgEquiv h t).symm x), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun χ hχ => usm_chrW t hχ.1⟩
  · intro x
    rw [at_iff, ep_smul, compFin_tensAt]
  · intro x
    change splitProj t (compFin F E v (tensAt E v _)) = _
    rw [compFin_tensAt, splitProj_symm]
  · intro x
    change splitProj (t.comp σ) (compFin F E v (tensAt E v _)) = _
    rw [compFin_tensAt, splitProj_comp_symm]
  · intro z hz h1 h2
    refine AE_ext h t ?_ (h1.trans (map_zero _).symm) (h2.trans (map_zero _).symm)
    rw [sub_smul, one_smul, (at_iff _).1 hz, sub_self, smul_zero]
  · intro z
    exact ⟨piW_cA t z, by rw [piW_cA, comp_conj_conj h]⟩
  · intro z hz u hu
    rw [← map_smul, hz u hu, map_zero]
  · exact fun a z => ⟨piW_smul _ a z, piW_smul _ a z⟩
  · exact fun x => ⟨piW_inc _ x, piW_inc _ x⟩
  · intro z hz
    rw [← ev_trace h t, ← (at_iff _).1 hz, map_smul, smul_eq_mul, ep_mul]
    exact congrArg (sgl v) (evalV_singleFin_self v _).symm
  · intro z x hz h1 h2
    refine ⟨fun χ => ?_, modu_single _ x (norm_eq h t hz h1 h2)⟩
    rw [eq_locIdele h t hz h1 h2]
    rfl

end PositivityTheory.KCo
