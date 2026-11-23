import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructureStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.HaarCoord

theorem measurePreserving_skew_add {A B : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [μ.IsAddLeftInvariant] {f : B → A} (hf : Measurable f) :
    MeasurePreserving (fun p : A × B => (f p.2 + p.1, p.2)) (μ.prod ν) (μ.prod ν) := by
  have h : MeasurePreserving (fun p : B × A => (id p.1, f p.1 + p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (g := fun b a => f b + a)
      ((hf.comp measurable_fst).add measurable_snd) (Filter.Eventually.of_forall fun b => map_add_left_eq_self μ (f b))
  exact Measure.measurePreserving_swap.comp (h.comp Measure.measurePreserving_swap)

theorem isMulRightInvariant_map {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Mul G] (P : Measure X) (e : X ≃ᵐ G)
    (h : ∀ q, ∃ T : X → X, MeasurePreserving T P P ∧ ∀ p, e (T p) = e p * e q) : (P.map e).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨T, hT, hTe⟩ := h (e.symm g)
  have hg : (fun x : G => x * g) = e ∘ T ∘ e.symm := by
    funext x
    simp only [Function.comp, hTe, e.apply_symm_apply]
  rw [hg]
  have h1 : MeasurePreserving e P (P.map e) := ⟨e.measurable, rfl⟩
  exact (h1.comp (hT.comp (h1.symm e))).map_eq

theorem coord_mul {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (c c' : skewA D ρ) (b b' : Mx D ρ V₀.rank)
    (u u' : GL (Fin ρ) (AE D)) :
    d.nC ((skewConj u.1 c' + cComm V₀ b (u.1 ⬝ b')) + c) * (d.nB (u.1 ⬝ b' + b) * d.levi (u * u')) =
      d.nC c * (d.nB b * d.levi u) * (d.nC c' * (d.nB b' * d.levi u')) := by
  have h1 : d.levi u * (d.nC c' * (d.nB b' * d.levi u')) =
      d.nC (skewConj u.1 c') * (d.nB (u.1 ⬝ b') * d.levi (u * u')) := by
    rw [← mul_assoc, d.levi_mul_nC, mul_assoc, ← mul_assoc (d.levi u), d.levi_mul_nB, mul_assoc, map_mul]
  rw [mul_assoc, mul_assoc, h1, ← mul_assoc (d.nB b), ← d.nC_mul_nB, mul_assoc, ← mul_assoc (d.nB b), d.nB_mul_nB,
    ← d.nC_mul_nB, add_comm _ c, add_comm _ b, d.nC_add, d.nC_add]
  simp only [mul_assoc]

theorem measurableAdd₂_addSubgroup {A : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] (H : AddSubgroup A) :
    MeasurableAdd₂ H :=
  ⟨Measurable.subtype_mk ((measurable_subtype_coe.comp measurable_fst).add (measurable_subtype_coe.comp measurable_snd))⟩

theorem measurePreserving_triple {A B U : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [AddGroup B]
    [MeasurableSpace B] [MeasurableAdd₂ B] [Mul U] [MeasurableSpace U] [MeasurableMul U]
    (l : Measure A) (μ : Measure B) (ν : Measure U) [SFinite l] [SFinite μ] [SFinite ν] [l.IsAddLeftInvariant]
    [μ.IsAddLeftInvariant] [ν.IsMulRightInvariant] {f : B × U → A} (hf : Measurable f) {g : U → B} (hg : Measurable g)
    (u' : U) :
    MeasurePreserving (fun p : A × (B × U) => (f p.2 + p.1, (g p.2.2 + p.2.1, p.2.2 * u')))
      (l.prod (μ.prod ν)) (l.prod (μ.prod ν)) := by
  have T1 := measurePreserving_skew_add l (μ.prod ν) hf
  have T2 := (MeasurePreserving.id l).prod (measurePreserving_skew_add μ ν hg)
  have T3 := (MeasurePreserving.id l).prod ((MeasurePreserving.id μ).prod (measurePreserving_mul_right ν u'))
  exact T3.comp (T2.comp T1)

theorem continuous_UX_val (D : D7) (ρ : ℕ) : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_UX_mul {D : D7} {ρ n : ℕ} (b' : Mx D ρ n) : Continuous fun u : UX D ρ => (u.1.1 ⬝ b' : Mx D ρ n) :=
  (continuous_UX_val D ρ).matrix_mul continuous_const

theorem continuous_skewConj {D : D7} {ρ : ℕ} (c' : skewA D ρ) : Continuous fun a : Mx D ρ ρ => skewConj a c' := by
  have h1 : Continuous fun a : Mx D ρ ρ => (a ⬝ c'.1 : Mx D ρ ρ) := continuous_id.matrix_mul continuous_const
  have h2 : Continuous fun a : Mx D ρ ρ => (a ⬝ c'.1 ⬝ adj a : Mx D ρ ρ) := h1.matrix_mul continuous_adj
  exact Continuous.subtype_mk h2 _

theorem continuous_cComm {D : D7} (V₀ : HSp D) (ρ : ℕ) :
    Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank => cComm V₀ x.1 x.2 := by
  have := (lattice_Mx D ρ ρ).1
  have : ContinuousSub (Mx D ρ ρ) := IsTopologicalAddGroup.to_continuousSub
  have hp : Continuous (plus V₀ : Mx D ρ V₀.rank → _) := continuous_const.matrix_mul continuous_adj
  have h1 : Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank => (x.2 ⬝ plus V₀ x.1 : Mx D ρ ρ) :=
    continuous_snd.matrix_mul (hp.comp continuous_fst)
  have h2 : Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank => (x.1 ⬝ plus V₀ x.2 : Mx D ρ ρ) :=
    continuous_fst.matrix_mul (hp.comp continuous_snd)
  have h3 : Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank =>
      (half D • (x.2 ⬝ plus V₀ x.1 - x.1 ⬝ plus V₀ x.2) : Mx D ρ ρ) := (h1.sub h2).const_smul (half D)
  exact Continuous.subtype_mk h3 _

set_option synthInstance.maxHeartbeats 200000 in
theorem continuous_shift {D : D7} (V₀ : HSp D) (ρ : ℕ) (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) :
    Continuous fun y : Mx D ρ V₀.rank × UX D ρ => skewConj y.2.1.1 c' + cComm V₀ y.1 (y.2.1.1 ⬝ b') := by
  have := (lattice_Mx D ρ ρ).1
  have h1 : Continuous fun y : Mx D ρ V₀.rank × UX D ρ => skewConj y.2.1.1 c' :=
    (continuous_skewConj c').comp (f := fun y : Mx D ρ V₀.rank × UX D ρ => y.2.1.1)
      ((continuous_UX_val D ρ).comp continuous_snd)
  have h2 : Continuous fun y : Mx D ρ V₀.rank × UX D ρ => cComm V₀ y.1 (y.2.1.1 ⬝ b') :=
    (continuous_cComm V₀ ρ).comp (f := fun y : Mx D ρ V₀.rank × UX D ρ => (y.1, (y.2.1.1 ⬝ b' : Mx D ρ V₀.rank)))
      (continuous_fst.prodMk ((continuous_UX_mul b').comp continuous_snd))
  exact h1.add h2

set_option synthInstance.maxHeartbeats 200000 in
theorem measurable_shift {D : D7} (V₀ : HSp D) (ρ : ℕ) (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) :
    Measurable fun y : Mx D ρ V₀.rank × UX D ρ => skewConj y.2.1.1 c' + cComm V₀ y.1 (y.2.1.1 ⬝ b') := by
  obtain ⟨b1, b2, b3, b4, -⟩ := lattice_Mx D ρ V₀.rank
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  exact (continuous_shift V₀ ρ c' b').measurable

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 400000 in

theorem isMulRightInvariant_map_coord : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → ((lC.prod (vb.μ.prod vU.ν)).map e).IsMulRightInvariant := by
  intro D V V₀ ρ d vb vU e he lC hC hS
  obtain ⟨a1, a2, a3, a4, -⟩ := lattice_Mx D ρ ρ
  obtain ⟨b1, b2, b3, b4, -⟩ := lattice_Mx D ρ V₀.rank
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := vb.covol.1
  have := vU.unit.1
  have : vU.ν.IsMulRightInvariant := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ vU.unit
  have : SFinite vb.μ := inferInstance
  have : SFinite vU.ν := inferInstance
  have : MeasurableAdd₂ (Mx D ρ ρ) := inferInstance
  have : MeasurableAdd₂ (skewA D ρ) := measurableAdd₂_addSubgroup _
  have : MeasurableAdd₂ (Mx D ρ V₀.rank) := inferInstance
  have : MeasurableMul (UX D ρ) := inferInstance
  refine isMulRightInvariant_map _ e ?_
  rintro ⟨c', b', u'⟩
  refine ⟨_, measurePreserving_triple lC vb.μ vU.ν (measurable_shift V₀ ρ c' b') (continuous_UX_mul b').measurable u', ?_⟩
  rintro ⟨c, b, u⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, he, he, he]
  exact coord_mul d c c' b b' u.1 u'.1

end GlobalTheory.Unf.HaarCoord
