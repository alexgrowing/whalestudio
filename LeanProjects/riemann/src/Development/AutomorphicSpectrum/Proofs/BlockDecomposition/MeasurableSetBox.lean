import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitIdelesOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesCompactOfLocalBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleAbsDetUnitaryAdelicEqOne

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SigL

section Abstract

variable {M X : Type} [MeasurableSpace M] [MeasurableSpace X]

theorem abs_integral (f : M → X) (hf : Measurable f) {B : Set M} (hB : MeasurableSet B) (P : Measure M)
    (u : X → ℂ) (hu : AEStronglyMeasurable u ((P.restrict B).map f)) (Ξ : M → ℂ)
    (h1 : ∀ z ∈ B, Ξ z = u (f z)) (h2 : ∀ z, z ∉ B → Ξ z = 0) :
    (Integrable Ξ P → Integrable u ((P.restrict B).map f)) ∧ ∫ z, Ξ z ∂P = ∫ z, u z ∂((P.restrict B).map f) := by
  refine ⟨fun hi => ?_, ?_⟩
  · rw [integrable_map_measure hu hf.aemeasurable]
    refine (hi.integrableOn (s := B)).congr ?_
    filter_upwards [ae_restrict_mem hB] with z hz
    exact h1 z hz
  · rw [integral_map hf.aemeasurable hu, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) h2]
    exact setIntegral_congr_fun hB h1

theorem abs_map (f : M → X) (hf : Measurable f) {B : Set M} (hB : MeasurableSet B) (P : Measure M)
    (T : M → M) (hT : Measurable T) (k : ℝ≥0) (Θ : X → X) (hΘ : Measurable Θ) (hBT : T ⁻¹' B = B)
    (hc : ∀ z, Θ (f z) = f (T z)) (hP : P.map T = k • P) :
    ((P.restrict B).map f).map Θ = k • (P.restrict B).map f := by
  rw [Measure.map_map hΘ hf]
  have e1 : Θ ∘ f = f ∘ T := funext hc
  rw [e1, ← Measure.map_map hf hT]
  have h1 : (P.restrict B).map T = k • P.restrict B := by
    have e2 := Measure.restrict_map (μ := P) hT hB
    rw [hBT, hP] at e2
    rw [← e2, Measure.restrict_smul]
  rw [h1, Measure.map_smul]

open Pointwise in
theorem abs_finite [AddCommGroup M] [TopologicalSpace M] [ContinuousAdd M] [TopologicalSpace X] [T2Space X]
    [OpensMeasurableSpace X] [OpensMeasurableSpace M] [T2Space M]
    (f : M → X) (hf : Measurable f) (ι : X → M) (hι : Continuous ι) {B : Set M} (hB : MeasurableSet B) (P : Measure M)
    [IsFiniteMeasureOnCompacts P] (T : Set M) (hT : IsCompact T) (h : ∀ z ∈ B, z - ι (f z) ∈ T) :
    IsFiniteMeasureOnCompacts ((P.restrict B).map f) := by
  refine ⟨fun C hC => ?_⟩
  have hCm : MeasurableSet C := hC.measurableSet
  have hK : IsCompact ((ι '' C) + T) := (hC.image hι).add hT
  rw [Measure.map_apply hf hCm, Measure.restrict_apply (hf hCm)]
  refine lt_of_le_of_lt (measure_mono ?_) hK.measure_lt_top
  rintro z ⟨hz, hzB⟩
  exact Set.mem_add.2 ⟨ι (f z), ⟨_, hz, rfl⟩, z - ι (f z), h z hzB, by abel⟩

theorem rh_one {A R : Type} [Ring A] [Ring R] (f : A →+* R) {e : A} (he : f e = 1) (y : A) : f ((1 - e) * y) = 0 := by
  rw [map_mul, map_sub, map_one, he, sub_self, zero_mul]

theorem rh_zero {A R : Type} [Ring A] [Ring R] (f : A →+* R) {e : A} (he : f e = 0) (y : A) : f ((1 - e) * y) = f y := by
  rw [map_mul, map_sub, map_one, he, sub_zero, one_mul]

theorem rh_map_zero {A R : Type} [Ring A] [Ring R] (f : A →+* R) : f 0 = 0 := map_zero f

end Abstract

end GlobalTheory.CompanionTheory.SigL

namespace GlobalTheory.CompanionTheory.SigL

variable {D : D7} {a b c r t : ℕ}

theorem topRing (D : D7) : IsTopologicalRing (AE D) :=
  isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)

def offS (S : Finset (Pl D)) : AddSubgroup (AE D) where
  carrier := {z | ∀ v ∉ S, cv D v z ∈ intLoc D.host.F D.host.E v}
  add_mem' := fun hx hy v hv => by rw [RingHom.map_add]; exact add_mem (hx v hv) (hy v hv)
  zero_mem' := fun v _ => by rw [RingHom.map_zero]; exact zero_mem _
  neg_mem' := fun hx v hv => by rw [RingHom.map_neg]; exact neg_mem (hx v hv)

theorem isOpen_offS (S : Finset (Pl D)) : IsOpen (offS S : Set (AE D)) := by
  haveI := topRing D
  have h0 : IsOpen {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v} :=
    GlobalTheory.ThK.ConeEuler.UnitsOpen.isOpen_integral_everywhere
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (h0.mem_nhds ?_) ?_)
  · intro v
    rw [rh_map_zero]
    exact zero_mem _
  · intro z hz v _
    exact hz v

theorem isOpen_intOff (S : Finset (Pl D)) : IsOpen {x : Mx D a b | IntOff S x} := by
  have h : {x : Mx D a b | IntOff S x} = ⋂ i, ⋂ j, (fun x : Mx D a b => x i j) ⁻¹' (offS S : Set (AE D)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h i j v hv => h v hv i j, fun h v hv i j => h i j v hv⟩
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_offS S).preimage (continuous_id.matrix_elem i j)

theorem measurableSet_box (S : Finset (Pl D)) :
    MeasurableSet {z : Mx D a r × Mx D a t | IntOff S z.1 ∧ IntOff S z.2} := by
  obtain ⟨g1, g2⟩ := top_pair (D := D) a r t
  have o : OpensMeasurableSpace (Mx D a r × Mx D a t) := g1.opensMeasurable
  exact (((isOpen_intOff S).preimage continuous_fst).inter ((isOpen_intOff S).preimage continuous_snd)).measurableSet

open Classical in

theorem exists_box (S : Finset (Pl D)) {e : AE D} (hS : IsIdem S e) (a b : ℕ) :
    ∃ T : Set (Mx D a b), IsCompact T ∧ ∀ x, IntOff S x → (1 - e) • x ∈ T := by
  have hL : ∀ v : Pl D, IsCompact (if v ∈ S then ({0} : Set (Fv D.host.F v ⊗[D.host.F] D.host.E))
      else (intLoc D.host.F D.host.E v : Set (Fv D.host.F v ⊗[D.host.F] D.host.E))) := fun v => by
    by_cases h : v ∈ S
    · rw [if_pos h]; exact isCompact_singleton
    · rw [if_neg h]; exact (GlobalTheory.ThK.isCompact_isOpen_intLoc v).1
  have hfin : ∀ᶠ v : Pl D in Filter.cofinite, (if v ∈ S then ({0} : Set (Fv D.host.F v ⊗[D.host.F] D.host.E))
      else (intLoc D.host.F D.host.E v : Set (Fv D.host.F v ⊗[D.host.F] D.host.E))) ⊆
        (intLoc D.host.F D.host.E v : Set (Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    apply hv
    have h' : v ∉ S := h
    rw [if_neg h']
  obtain ⟨K, hK, hz⟩ := GlobalTheory.IdeleCyl.exists_isCompact_box D.host.F D.host.E (fun _ => {0}) _
    (fun _ => isCompact_singleton) hL hfin
  refine ⟨{x | ∀ i j, x i j ∈ K}, ?_, fun x hx i j => ?_⟩
  · have e1 : {x : Mx D a b | ∀ i j, x i j ∈ K} = Set.univ.pi fun _ => Set.univ.pi fun _ => K := by
      ext x
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [e1]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  · refine hz _ (fun w => ?_) (fun v => ?_)
    · change compInf D.host.F D.host.E w ((1 - e) * x i j) ∈ ({0} : Set _)
      rw [rh_one _ (hS.1 w)]
      exact rfl
    · change cv D v ((1 - e) * x i j) ∈ _
      have hv := hS.2 v
      by_cases h : v ∈ S
      · rw [if_pos h] at hv
        rw [rh_one _ hv, if_pos h]
        exact rfl
      · rw [if_neg h] at hv
        rw [rh_zero _ hv, if_neg h]
        exact hx v h i j

theorem measurable_toX {e : AE D} (he : e * e = e) : Measurable (toX (a := a) (r := r) (t := t) he) := by
  haveI := topRing D
  obtain ⟨g1, g2⟩ := top_pair (D := D) a r t
  have o : OpensMeasurableSpace (Mx D a r × Mx D a t) := g1.opensMeasurable
  exact Measurable.subtype_mk
    ((continuous_fst.const_smul e).prodMk (continuous_snd.const_smul e)).measurable

end GlobalTheory.CompanionTheory.SigL
