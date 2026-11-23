import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnipotentInvariantCompactlySupportedWeight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.PiCovol

theorem isFD_pi {ι Y : Type} [Fintype ι] [AddCommGroup Y] [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
    {G : AddSubgroup Y} {D : Set Y} (hF : IsAddFundamentalDomain G D ν) :
    IsAddFundamentalDomain (AddSubgroup.pi Set.univ fun _ : ι => G) (Set.univ.pi fun _ : ι => D)
      (Measure.pi fun _ : ι => ν) := by
  have hq (i : ι) := Measure.quasiMeasurePreserving_eval (fun _ : ι => ν) i
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.univ_pi_eq_iInter]
    exact NullMeasurableSet.iInter fun i => hF.nullMeasurableSet.preimage (hq i)
  · have := (ae_all_iff (μ := (Measure.pi fun _ : ι => ν))).2 fun i => (hq i).ae hF.ae_covers
    filter_upwards [this] with z hz
    choose a ha using hz
    exact ⟨⟨fun i => a i, fun i _ => (a i).2⟩, fun i _ => ha i⟩
  · intro a b hab
    obtain ⟨i, hi⟩ : ∃ i, a.1 i ≠ b.1 i := by
      by_contra! h
      exact hab (Subtype.ext (funext h))
    have h := hF.aedisjoint (i := ⟨a.1 i, a.2 i trivial⟩) (j := ⟨b.1 i, b.2 i trivial⟩)
      fun e => hi (congrArg Subtype.val e)
    refine measure_mono_null ?_ ((hq i).preimage_null h)
    rintro z ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩
    exact ⟨⟨u i, hu i trivial, congrFun hu' i⟩, ⟨v i, hv i trivial, congrFun hv' i⟩⟩

theorem map_eq_of_isFD {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (P : Measure V) [P.IsAddHaarMeasure] (G : AddSubgroup V) [Countable G] {D : Set V}
    (hD : IsAddFundamentalDomain G D P) (h0 : P D ≠ 0) (h1 : P D ≠ ⊤) (e : V ≃ₜ+ V)
    (hG : ∀ v ∈ G, e.symm v ∈ G) (hG' : ∀ v ∈ G, e v ∈ G) : P.map e = P := by
  haveI : (P.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map P
  set c := Measure.addHaarScalarFactor (P.map e) P with hc
  have h : P.map e = c • P := Measure.isAddLeftInvariant_eq_smul _ P
  have hm : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hpre : IsAddFundamentalDomain G (e ⁻¹' D) P := by
    refine hD.preimage_of_equiv (f := e) ⟨hm.measurable, ?_⟩
      (e := fun b : G => (⟨e.symm b, hG _ b.2⟩ : G)) ⟨fun b b' h => ?_, fun a => ?_⟩ fun b v => ?_
    · rw [h]; exact Measure.smul_absolutelyContinuous
    · exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))
    · exact ⟨⟨e a, hG' _ a.2⟩, Subtype.ext (e.symm_apply_apply _)⟩
    · change e (e.symm b + v) = b + e v
      simp
  have e1 : P (e ⁻¹' D) = P D := hpre.measure_eq hD
  have e2 : P (e ⁻¹' D) = c * P D := by rw [← hm.map_apply, h]; rfl
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have : (c : ℝ≥0∞) * P D = 1 * P D := by rw [← e2, e1, one_mul]
    exact (ENNReal.mul_left_inj h0 h1).1 this
  have : c = 1 := by exact_mod_cast hc1
  rw [h, this, one_smul]

end GlobalTheory.CompanionTheory.SiegelND.PiCovol

open GlobalTheory.CompanionTheory.SiegelND.PiCovol in

theorem GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix : ∀ (F : Type) [Field F] [NumberField F] (ν : Measure (AF F)), GlobalTheory.CompanionTheory.Hypotheses₂.OneV.IsCovolOne ν → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → (Measure.pi fun _ : ι => ν).map (fun x => (A.map (algebraMap F (AF F))).mulVec x) = Measure.pi fun _ : ι => ν := by
  intro F _ _ ν hν ι _ _ A hA
  obtain ⟨hH, D, hD, hD1⟩ := hν
  haveI := hH
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  set G₀ : AddSubgroup (AF F) := (algebraMap F (AF F)).toAddMonoidHom.range with hG₀
  set G : AddSubgroup (ι → AF F) := AddSubgroup.pi Set.univ fun _ : ι => G₀ with hGdef
  have hmemG : ∀ v : ι → AF F, v ∈ G ↔ ∃ ξ : ι → F, v = fun i => algebraMap F (AF F) (ξ i) := by
    intro v
    constructor
    · intro hv
      choose ξ hξ using fun i => hv i trivial
      exact ⟨ξ, funext fun i => (hξ i).symm⟩
    · rintro ⟨ξ, rfl⟩ i _
      exact ⟨ξ i, rfl⟩
  haveI : Countable G := by
    have : Function.Surjective (fun ξ : ι → F => (⟨fun i => algebraMap F (AF F) (ξ i), (hmemG _).2 ⟨ξ, rfl⟩⟩ : G)) := by
      rintro ⟨v, hv⟩
      obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
      exact ⟨ξ, rfl⟩
    exact this.countable
  have hFD := isFD_pi (ι := ι) ν hD
  have hmass : (Measure.pi fun _ : ι => ν) (Set.univ.pi fun _ : ι => D) = 1 := by
    rw [Measure.pi_pi]; simp [hD1]
  have hrat : ∀ (B : Matrix ι ι F) (ξ : ι → F), (B.map (algebraMap F (AF F))).mulVec (fun i => algebraMap F (AF F) (ξ i)) =
      fun i => algebraMap F (AF F) (B.mulVec ξ i) := by
    intro B ξ
    funext i
    exact (RingHom.map_mulVec (algebraMap F (AF F)) B ξ i).symm
  have hu := GlobalTheory.CompanionTheory.SW.SdCoord.isUnit_det_map (R := AF F) A hA
  have hinv : (A.map (algebraMap F (AF F)))⁻¹ = A⁻¹.map (algebraMap F (AF F)) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  have := map_eq_of_isFD (Measure.pi fun _ : ι => ν) G hFD (by rw [hmass]; simp) (by rw [hmass]; simp)
    (GlobalTheory.CompanionTheory.SW.SdCoord.matE _ hu) ?_ ?_
  · exact this
  · intro v hv
    obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
    refine (hmemG _).2 ⟨A⁻¹.mulVec ξ, ?_⟩
    change (A.map (algebraMap F (AF F)))⁻¹.mulVec _ = _
    rw [hinv, hrat]
  · intro v hv
    obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
    refine (hmemG _).2 ⟨A.mulVec ξ, ?_⟩
    exact hrat A ξ
