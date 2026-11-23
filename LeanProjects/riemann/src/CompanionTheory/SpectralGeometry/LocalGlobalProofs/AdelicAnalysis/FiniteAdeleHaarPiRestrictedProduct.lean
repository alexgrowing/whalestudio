import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.AfBox

theorem eq_of_invariant_of_open {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ ν : Measure G) [ν.IsAddHaarMeasure] [μ.IsAddLeftInvariant] {C : Set G} (hC : IsOpen C)
    (h0 : (0 : G) ∈ C) (hμ : μ C = 1) (hν : ν C = 1) : μ = ν := by
  haveI : IsFiniteMeasureOnCompacts μ := by
    refine ⟨fun K hK => ?_⟩
    have hU : ∀ k : G, IsOpen ((fun x => -k + x) ⁻¹' C) := fun k =>
      hC.preimage (continuous_const.add continuous_id)
    obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => (fun x => -k + x) ⁻¹' C)
      (fun k _ => (hU k).mem_nhds (by simpa using h0))
    have hm : ∀ k : G, μ ((fun x => -k + x) ⁻¹' C) = 1 := fun k => by
      rw [measure_preimage_add, hμ]
    calc μ K ≤ μ (⋃ k ∈ t, (fun x => -k + x) ⁻¹' C) := measure_mono ht
      _ ≤ ∑ k ∈ t, μ ((fun x => -k + x) ⁻¹' C) := measure_biUnion_finset_le _ _
      _ = t.card := by simp [hm]
      _ < ⊤ := by simp
  have h := Measure.isAddLeftInvariant_eq_smul μ ν
  have hc : Measure.addHaarScalarFactor μ ν = 1 := by
    have h2 : μ C = (Measure.addHaarScalarFactor μ ν • ν) C := by rw [← h]
    rw [Measure.smul_apply, hμ, hν] at h2
    simpa [ENNReal.smul_def, eq_comm] using h2
  rw [hc, one_smul] at h
  exact h

theorem map_restrict_invariant {G T : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd T]
    (m : Measure G) [m.IsAddLeftInvariant] (H : AddSubgroup G) (hH : MeasurableSet (H : Set G))
    (ρ : G →+ T) (hρ : Measurable ρ) (hs : ∀ t, ∃ h ∈ H, ρ h = t) :
    ((m.restrict H).map ρ).IsAddLeftInvariant := by
  constructor
  intro g
  obtain ⟨h, hh, rfl⟩ := hs g
  have e : (m.restrict H).map (fun x => h + x) = m.restrict H := by
    have hp : (fun x => h + x) ⁻¹' (H : Set G) = H := by
      ext x
      simp [H.add_mem_cancel_left hh]
    have := Measure.restrict_map (μ := m) (measurable_const_add h) hH
    rw [map_add_left_eq_self, hp] at this
    exact this.symm
  rw [Measure.map_map (measurable_const_add _) hρ]
  have hc : (fun x => ρ h + x) ∘ ρ = ρ ∘ (fun x => h + x) := by
    ext x
    simp
  rw [hc, ← Measure.map_map hρ (measurable_const_add _), e]

theorem measure_inter_preimage {G T : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (m : Measure G) [m.IsAddLeftInvariant] (H : AddSubgroup G) (hH : MeasurableSet (H : Set G))
    (ρ : G →+ T) (hρ : Measurable ρ) (hs : ∀ t, ∃ h ∈ H, ρ h = t)
    (ν : Measure T) [ν.IsAddHaarMeasure] {C : Set T} (hC : IsOpen C) (h0 : (0 : T) ∈ C)
    (hm : m ((H : Set G) ∩ ρ ⁻¹' C) = 1) (hν : ν C = 1) {B : Set T} (hB : MeasurableSet B) :
    m ((H : Set G) ∩ ρ ⁻¹' B) = ν B := by
  haveI := map_restrict_invariant m H hH ρ hρ hs
  have hmap : ∀ D : Set T, MeasurableSet D → ((m.restrict H).map ρ) D = m ((H : Set G) ∩ ρ ⁻¹' D) := by
    intro D hD
    rw [Measure.map_apply hρ hD, Measure.restrict_apply (hρ hD), Set.inter_comm]
  have he := eq_of_invariant_of_open ((m.restrict H).map ρ) ν hC h0
    (by rw [hmap C hC.measurableSet, hm]) hν
  rw [← he, hmap B hB]

variable {F : Type} [Field F] [NumberField F]

def offS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) : AddSubgroup (ι → Af F) where
  carrier := {x | ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F}
  add_mem' := fun {a b} ha hb v hv i => by
    simpa using add_mem (ha v hv i) (hb v hv i)
  zero_mem' := fun v _ i => by simp
  neg_mem' := fun {a} ha v hv i => by
    simpa using neg_mem (ha v hv i)

def compS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (ι → Af F) →+ ∀ v : S, ι → Fv F v.1 where
  toFun x := fun v i => evalV F v.1 (x i)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem continuous_compS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (compS (F := F) ι S) :=
  continuous_pi fun v => continuous_pi fun i =>
    (RestrictedProduct.continuous_eval v.1).comp (continuous_apply i)

open Classical in

def liftS {S : Finset (HeightOneSpectrum (𝓞 F))} (t : ∀ v : S, Fv F v.1) : Af F :=
  ⟨fun w => if hw : w ∈ S then t ⟨w, hw⟩ else (0 : Fv F w), by
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with w hw
    have : w ∉ S := by simpa using hw
    simp [this]⟩

open Classical in
theorem evalV_liftS_of_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (t : ∀ v : S, Fv F v.1) (v : S) :
    evalV F v.1 (liftS t) = t v := by
  have : evalV F v.1 (liftS t) = dite (v.1 ∈ S) (fun hw => t ⟨v.1, hw⟩) (fun _ => (0 : Fv F v.1)) := rfl
  rw [this, dif_pos v.2]

open Classical in
theorem evalV_liftS_of_notMem {S : Finset (HeightOneSpectrum (𝓞 F))} (t : ∀ v : S, Fv F v.1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : evalV F v (liftS t) = 0 := by
  have : evalV F v (liftS t) = dite (v ∈ S) (fun hw => t ⟨v, hw⟩) (fun _ => (0 : Fv F v)) := rfl
  rw [this, dif_neg hv]

theorem exists_offS_compS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : ∀ v : S, ι → Fv F v.1) : ∃ h ∈ offS (F := F) ι S, compS ι S h = t := by
  refine ⟨fun i => liftS fun v => t v i, fun v hv i => ?_, ?_⟩
  · rw [evalV_liftS_of_notMem _ hv]
    exact zero_mem (v.adicCompletionIntegers F)
  · funext v i
    exact evalV_liftS_of_mem (fun v => t v i) v

theorem isOpen_integral : IsOpen {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)

theorem isOpen_offS (ι : Type) [Finite ι] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (offS (F := F) ι S : Set (ι → Af F)) := by
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) ?_
  have ho : IsOpen (Set.pi Set.univ fun _ : ι => {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F}) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integral
  refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
  · intro i _ v
    exact zero_mem (v.adicCompletionIntegers F)
  · intro x hx v _ i
    exact hx i (Set.mem_univ i) v

theorem pi_box : ∀ (F : Type) [Field F] [NumberField F] (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (ι : Type) [Fintype ι] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (ι → Fv F v)), (∀ v, MeasurableSet (A v)) → (Measure.pi fun _ : ι => lf) {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A v) ∧ ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} = ∏ v ∈ S, (Measure.pi fun _ : ι => lam v) (A v) := by
  intro F _ _ lam hlam lf hlf h1 ι _ S A hA
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  have hloc := fun v => GlobalTheory.T.completion_is_local_ring F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  let ν : Measure (∀ v : S, ι → Fv F v.1) := Measure.pi fun v : S => Measure.pi fun _ : ι => lam v.1
  let O : Set (∀ v : S, ι → Fv F v.1) :=
    Set.pi Set.univ fun v : S => Set.pi Set.univ fun _ : ι => (v.1.adicCompletionIntegers F : Set (Fv F v.1))
  have hOo : IsOpen O := isOpen_set_pi Set.finite_univ fun v _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
  have hO0 : (0 : ∀ v : S, ι → Fv F v.1) ∈ O := fun v _ i _ => zero_mem (v.1.adicCompletionIntegers F)
  have hνO : ν O = 1 := by
    simp only [ν, O]
    rw [Measure.pi_pi]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [Measure.pi_pi]
    exact Finset.prod_eq_one fun _ _ => (hlam v.1).2
  have hmO : (Measure.pi fun _ : ι => lf) ((offS (F := F) ι S : Set (ι → Af F)) ∩ compS ι S ⁻¹' O) = 1 := by
    have : ((offS (F := F) ι S : Set (ι → Af F)) ∩ compS ι S ⁻¹' O) =
        Set.pi Set.univ fun _ : ι => {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F} := by
      ext x
      constructor
      · rintro ⟨hx1, hx2⟩ i _ v
        by_cases hv : v ∈ S
        · exact hx2 ⟨v, hv⟩ (Set.mem_univ _) i (Set.mem_univ _)
        · exact hx1 v hv i
      · intro hx
        exact ⟨fun v _ i => hx i (Set.mem_univ i) v, fun v _ i _ => hx i (Set.mem_univ i) v.1⟩
    rw [this, Measure.pi_pi]
    exact Finset.prod_eq_one fun _ _ => h1
  have hset : {x : ι → Af F | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A v) ∧ ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} =
      (offS (F := F) ι S : Set (ι → Af F)) ∩ compS ι S ⁻¹' (Set.pi Set.univ fun v : S => A v.1) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx2, fun v _ => hx1 v.1 v.2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨fun v hv => hx2 ⟨v, hv⟩ (Set.mem_univ _), hx1⟩
  rw [hset, measure_inter_preimage (Measure.pi fun _ : ι => lf) (offS (F := F) ι S)
    (isOpen_offS ι S).measurableSet (compS ι S) (continuous_compS ι S).measurable
    (exists_offS_compS ι S) ν hOo hO0 hmO hνO (MeasurableSet.univ_pi fun v => hA v.1)]
  simp only [ν]
  rw [Measure.pi_pi]
  exact Finset.prod_coe_sort S fun v => (Measure.pi fun _ : ι => lam v) (A v)

end GlobalTheory.CompanionTheory.SW.AfBox
