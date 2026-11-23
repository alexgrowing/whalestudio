import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.BlockMatrixIdentity.BlockMatOne
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl PositivityTheory.Affgl.CT Topology Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.ConstTerm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

omit [IsTotallyComplex E] in

theorem continuous_map_pFin :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd :
    Continuous fun x : InfiniteAdeleRing E × IsDedekindDomain.FiniteAdeleRing (𝓞 E) E => x.2))

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)).comp
    (continuous_fst : Continuous fun x : InfiniteAdeleRing E × IsDedekindDomain.FiniteAdeleRing (𝓞 E) E => x.1)

theorem continuous_map_pInf :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)

theorem continuous_of_isOpen_stab (φ : Sm E a) (hU : IsOpen {k | finRep E a k φ = φ}) : Continuous φ.1 := by
  rw [continuous_iff_continuousAt]
  intro g
  have hF : ContinuousAt (fun h : GA E a => chart φ.1 g (toL (GeneralLinearGroup.map (pInf E) h).val)) 1 := by
    have h1 : ContinuousAt (chart φ.1 g) (toL ((GeneralLinearGroup.map (pInf E) (1 : GA E a)).val)) := by
      rw [map_one]
      exact (contDiffAt_chart φ.2 g isUnit_one).continuousAt
    have h0 : Continuous (fun h : GA E a =>
        ((GeneralLinearGroup.map (n := Fin a) (pInf E) h : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))) :=
      Units.continuous_val.comp continuous_map_pInf
    have h2 : Continuous (fun h : GA E a => toL (GeneralLinearGroup.map (pInf E) h).val) := h0
    exact ContinuousAt.comp (f := fun h : GA E a => toL (GeneralLinearGroup.map (pInf E) h).val) h1 h2.continuousAt
  have hev : ∀ᶠ h in 𝓝 (1 : GA E a), GeneralLinearGroup.map (pFin E) h ∈ {k | finRep E a k φ = φ} := by
    refine (continuous_map_pFin.continuousAt (x := (1 : GA E a))).eventually (hU.mem_nhds ?_)
    rw [map_one]
    change finRep E a 1 φ = φ
    simp
  have hG : ContinuousAt (fun h : GA E a => φ.1 (g * h)) 1 := by
    refine hF.congr ?_
    filter_upwards [hev] with h hh
    have e := congrArg (fun ψ : Sm E a => ψ.1 (g * infGL E a (GeneralLinearGroup.map (pInf E) h))) hh
    change φ.1 (g * infGL E a _ * finGL E a _) = φ.1 _ at e
    rw [mul_assoc, infGL_mul_finGL] at e
    rw [e, chart_val]
  have h2 : ContinuousAt (fun x : GA E a => g⁻¹ * x) g := (continuous_const.mul continuous_id).continuousAt
  have h3 : ContinuousAt (fun h : GA E a => φ.1 (g * h)) (g⁻¹ * g) := by rwa [inv_mul_cancel]
  simpa [Function.comp_def] using h3.comp h2

omit [IsTotallyComplex E] in

theorem continuous_unip : Continuous (unip : (BlockIx a r → Ad E) → GA E a) := by
  have hn : Continuous (fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E))) :=
    continuous_matrix fun i j => by
      simp only [nilM, Matrix.of_apply]
      split_ifs with h
      · exact continuous_apply _
      · exact continuous_const
  exact Units.continuous_iff.2 ⟨continuous_const.add hn, continuous_const.sub hn⟩

omit [IsTotallyComplex E] in

theorem exists_isCompact_sub_mem :
    ∃ C : Set (BlockIx a r → Ad E), IsCompact C ∧ ∀ x, ∃ n ∈ ratN E a r, x - n ∈ C := by
  obtain ⟨K, hK, h⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  choose y hy using h
  refine ⟨Set.pi Set.univ fun _ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  exact ⟨fun p => algebraMap E (Ad E) (y (x p)), ⟨fun p => y (x p), rfl⟩, fun p _ => hy (x p)⟩

omit [IsTotallyComplex E] in

theorem periodic_integrand (φ : GA E a → ℂ) (hl : ∀ (γ : GL (Fin a) E) (g : GA E a), φ (ratGL E a γ * g) = φ g)
    (g : GA E a) {n : BlockIx a r → Ad E} (hn : n ∈ ratN E a r) (x : BlockIx a r → Ad E) :
    φ (unip (n + x) * g) = φ (unip x * g) := by
  obtain ⟨y, rfl⟩ := hn
  have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) y =
      fun p => algebraMap E (Ad E) (y p) := rfl
  rw [e, unip_add, unip_algebraMap, mul_assoc, hl]

theorem integrableOn_fundamentalDomain :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : Sm E a),
      (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) →
      IsOpen {k | finRep E a k φ = φ} →
      ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
        (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratN E a r) 𝓕 μ →
        μ 𝓕 < ⊤ ∧ ∀ g : GA E a, IntegrableOn (fun x => φ.1 (unip x * g)) 𝓕 μ := by
  intro E _ _ _ a r φ hl hU _ _ μ 𝓕 hμ hF
  obtain ⟨C, hC, hcov⟩ := exists_isCompact_sub_mem (E := E) (a := a) (r := r)
  have hφ := continuous_of_isOpen_stab φ hU
  haveI : Countable (ratN E a r) := by
    have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.countable_iff.2 inferInstance
    exact Function.Surjective.countable
      (f := (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)).rangeRestrict)
      (AddMonoidHom.rangeRestrict_surjective _)
  have hfin : μ 𝓕 < ⊤ := by
    have h1 : 𝓕 ⊆ ⋃ n : ratN E a r, (n +ᵥ C) ∩ 𝓕 := fun x hx => by
      obtain ⟨n, hn, h⟩ := hcov x
      refine Set.mem_iUnion.2 ⟨⟨n, hn⟩, ⟨x - n, h, ?_⟩, hx⟩
      simp [AddSubgroup.vadd_def]
    calc μ 𝓕 ≤ ∑' n : ratN E a r, μ ((n +ᵥ C) ∩ 𝓕) := (measure_mono h1).trans (measure_iUnion_le _)
      _ = μ C := (hF.measure_eq_tsum C).symm
      _ < ⊤ := hC.measure_lt_top
  refine ⟨hfin, fun g => ?_⟩
  have hc : Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) :=
    hφ.comp (continuous_unip.mul continuous_const)
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine Measure.integrableOn_of_bounded hfin.ne hc.aestronglyMeasurable (M := B) (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨n, hn, h⟩ := hcov x
  have := periodic_integrand φ.1 hl g hn (x - n)
  rw [add_sub_cancel] at this
  rw [this]
  exact hB _ h

end GlobalTheory.CompanionTheory.ConstTerm

end
