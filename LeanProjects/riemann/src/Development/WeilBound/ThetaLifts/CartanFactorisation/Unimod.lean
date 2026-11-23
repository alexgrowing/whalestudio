import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodular
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomain

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_scale (h : IsCMExt F E σ) (ε : ℤˣ) : ∃ c : E, c ≠ 0 ∧ σ c = ((ε : ℤ) : E) * c := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact ⟨1, one_ne_zero, by simp⟩
  · by_contra hn
    push Not at hn
    have hid : ∀ x, σ x = x := fun x => by
      by_contra hx
      refine hn (x - σ x) (sub_ne_zero.2 (Ne.symm hx)) ?_
      simp [GlobalTheory.SiegelSet.sigma_sigma h]
    haveI := h.2.1
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hc : w.IsComplex := IsTotallyComplex.isComplex w
    refine (InfinitePlace.not_isReal_iff_isComplex.2 hc) ?_
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    have := h.2.2.2 w.embedding x
    rw [hid] at this
    simpa using this.symm

theorem exists_hr (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ}
    (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) (hd : J.det ≠ 0) :
    ∃ J', IsHermND σ J' ∧ UG (cA σ) (incM F J) = HR (AF F) σ J' := by
  obtain ⟨c, hc, hσc⟩ := exists_scale h ε
  have hσ := GlobalTheory.SiegelSet.sigma_sigma h
  refine ⟨c • J.map σ, ⟨fun i j => ?_, ?_⟩, GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ hc⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ, hσc]
    rw [hJ j i]; ring
  · rw [Matrix.det_smul, show J.map σ = (σ : E →+* E).mapMatrix J from rfl, ← RingHom.map_det]
    exact mul_ne_zero (pow_ne_zero _ hc) ((map_ne_zero _).2 hd)

theorem unimodLC (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ}
    (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) (hd : J.det ≠ 0) : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.IsUnimodularLC (UA σ J) := by
  obtain ⟨J', hJ', e⟩ := exists_hr h hJ hd
  have key : ∀ S : Subgroup (GL (Fin n) (AE F E)), S = HR (AF F) σ J' →
      @GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.IsUnimodularLC S _ _ (borel S) := by
    rintro S rfl
    exact (GlobalTheory.AdelicStabUnimod.unimodularOver_adele F E σ h n J' hJ').1
  exact key _ e

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  haveI := (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).to_subtype
  exact Function.Injective.countable
    (f := fun γ : ratU σ J => (⟨γ.1.1, Subgroup.mem_subgroupOf.1 γ.2⟩ :
      Set.range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))))
    fun γ γ' h => Subtype.val_injective (Subtype.val_injective (congrArg Subtype.val h :))

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  haveI : Nontrivial (AF F ⊗[F] E) := by
    haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    infer_instance
  (inclR (F := F) (E := E) (AF F)).injective

theorem discrete_ratU (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ}
    (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) (hd : J.det ≠ 0) : DiscreteTopology (ratU σ J) := by
  obtain ⟨J', -, e⟩ := exists_hr h hJ hd
  haveI : DiscreteTopology (HFinIn (AF F) σ J') := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J'
  have mem : ∀ γ : ratU σ J, γ.1.1 ∈ HFin (AF F) σ J' := fun γ => by
    obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.1 γ.2
    have h1 : γ.1.1 ∈ HR (AF F) σ J' := e ▸ γ.1.2
    refine Subgroup.mem_map.2 ⟨u, ?_, hu⟩
    rw [← show _ = γ.1.1 from hu] at h1
    change Formalism.UG.cT (sigR (AF F) σ) (u.1.map (inclR (AF F))) * J'.map (inclR (AF F)) * u.1.map (inclR (AF F)) =
      J'.map (inclR (AF F)) at h1
    change Formalism.UG.cT (σ : E →+* E) u.1 * J' * u.1 = J'
    apply Matrix.map_injective (inclR_inj (F := F))
    simp only [Matrix.map_mul]
    exact h1
  let f : ratU σ J → HFinIn (AF F) σ J' := fun γ => ⟨⟨γ.1.1, e ▸ γ.1.2⟩, Subgroup.mem_subgroupOf.2 (mem γ)⟩
  have hc : Continuous f := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  exact DiscreteTopology.of_continuous_injective hc fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun z : HFinIn (AF F) σ J' => z.1.1) hab))

theorem sigmaFinite_of_lc {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.IsUnimodularLC G) (μ : Measure G) [μ.IsHaarMeasure] : SigmaFinite μ := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
  infer_instance

theorem sFinite_haar (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ}
    (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) (hd : J.det ≠ 0) (μ : Measure (UA σ J)) [μ.IsHaarMeasure] :
    SigmaFinite μ :=
  sigmaFinite_of_lc (unimodLC h hJ hd) μ

theorem unimodularity_holds : Unimod := by
  intro F E _ _ _ _ _ σ h n J ε hJ hd
  obtain ⟨h1, h2, h3, h4, h5, ⟨μ, hμ⟩, h7⟩ := unimodLC h hJ hd
  haveI := countable_ratU σ J
  haveI := discrete_ratU h hJ hd
  obtain ⟨𝓕, -, h𝓕⟩ := (GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_of_discrete (ratU σ J)).2.2 μ hμ
  exact ⟨inferInstance, ⟨μ, 𝓕, hμ, h𝓕⟩, h7⟩

end PositivityTheory.ThKF

end
