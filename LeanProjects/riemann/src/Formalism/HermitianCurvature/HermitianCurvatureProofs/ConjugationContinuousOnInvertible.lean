import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlochKatoDuality

open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL

noncomputable section
namespace Formalism.FourierDecayAlt.P.B2x1

variable {k r : ℕ}

def adjF (x : Mt k r) : Mt k r := (Matrix.of x : Mat k r).adjugate
def detF (x : Mt k r) : ℂ := (Matrix.of x : Mat k r).det

theorem detF_cont : Continuous (detF (k := k) (r := r)) := Continuous.matrix_det (continuous_id (X := Mat k r))
theorem adjF_cont : Continuous (adjF (k := k) (r := r)) := Continuous.matrix_adjugate (continuous_id (X := Mat k r))

theorem invM_smul : (invM : Mt k r → Mt k r) = fun x => (detF x)⁻¹ • adjF x := by
  funext x
  show (Ring.inverse (Matrix.of x : Mat k r).det • (Matrix.of x : Mat k r).adjugate : Mat k r) = _
  rw [Ring.inverse_eq_inv']; rfl

theorem invM_meas : Measurable (invM : Mt k r → Mt k r) := by
  rw [invM_smul]; exact detF_cont.measurable.inv.smul adjF_cont.measurable

theorem invM_contOn : ContinuousOn (invM : Mt k r → Mt k r) {x | detF x ≠ 0} := by
  rw [invM_smul]
  exact (detF_cont.continuousOn.inv₀ (fun x hx => hx)).smul adjF_cont.continuousOn

theorem lmulM_cont (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  unfold lmulM
  exact (continuous_const (y := a)).matrix_mul (continuous_id (X := Mat k r))

theorem rmulF_cont {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Continuous (rmulF a) := by
  unfold rmulF
  exact (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).matrix_mul continuous_const

theorem conjM_cont (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  unfold conjM
  exact ((continuous_const (y := a)).matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem mulM_cont : Continuous (mulM : Mt k r × Mt k r → Mt k r) := by
  unfold mulM
  exact Continuous.matrix_mul (A := fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r))
    (B := fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) continuous_fst continuous_snd

theorem exists_pos {X : Type*} [TopologicalSpace X] [SigmaCompactSpace X] [MeasurableSpace X] (μ : Measure X) (h0 : μ ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ K ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h0
  have : μ Set.univ = 0 := by
    rw [← iUnion_compactCovering X]
    exact measure_iUnion_null (fun n => hcon _ (isCompact_compactCovering _ n))
  exact Measure.measure_univ_eq_zero.mp this

def amb (U : Set (Mat k r)) : Set (Mt k r) := {x | Matrix.of x ∈ U}

theorem amb_closed {U : Set (Mat k r)} (hU : IsClosedSubgroup U) : IsClosed (amb U) := hU.closed

def Gp (U : Set (Mat k r)) (_hU : IsClosedSubgroup U) : Type := {x : Mt k r // x ∈ amb U}

variable {U : Set (Mat k r)} {hU : IsClosedSubgroup U}

instance : TopologicalSpace (Gp U hU) := inferInstanceAs (TopologicalSpace {x : Mt k r // x ∈ amb U})
instance : MeasurableSpace (Gp U hU) := inferInstanceAs (MeasurableSpace {x : Mt k r // x ∈ amb U})
instance : BorelSpace (Gp U hU) := inferInstanceAs (BorelSpace {x : Mt k r // x ∈ amb U})
instance : SecondCountableTopology (Gp U hU) :=
  inferInstanceAs (SecondCountableTopology {x : Mt k r // x ∈ amb U})
instance : T2Space (Gp U hU) := inferInstanceAs (T2Space {x : Mt k r // x ∈ amb U})

def inc (x : Gp U hU) : Mt k r := x.1

theorem inc_mem (x : Gp U hU) : Matrix.of (inc x) ∈ U := x.2

theorem inc_cont : Continuous (inc : Gp U hU → Mt k r) := continuous_subtype_val

theorem inc_closedEmb : IsClosedEmbedding (inc : Gp U hU → Mt k r) :=
  (amb_closed hU).isClosedEmbedding_subtypeVal

theorem inc_memb : MeasurableEmbedding (inc : Gp U hU → Mt k r) :=
  MeasurableEmbedding.subtype_coe (amb_closed hU).measurableSet

theorem range_inc : Set.range (inc : Gp U hU → Mt k r) = amb U := Subtype.range_coe

instance : LocallyCompactSpace (Gp U hU) := inc_closedEmb.locallyCompactSpace

instance : Group (Gp U hU) where
  mul a b := ⟨mulM (a.1, b.1), hU.mul_mem _ a.2 _ b.2⟩
  one := ⟨(1 : Mat k r), hU.one_mem⟩
  inv a := ⟨invM a.1, hU.inv_mem _ a.2⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc (Matrix.of a.1 : Mat k r) (Matrix.of b.1) (Matrix.of c.1))
  one_mul a := Subtype.ext (Matrix.one_mul (Matrix.of a.1 : Mat k r))
  mul_one a := Subtype.ext (Matrix.mul_one (Matrix.of a.1 : Mat k r))
  inv_mul_cancel a := Subtype.ext (Matrix.nonsing_inv_mul (Matrix.of a.1 : Mat k r) (hU.unit _ a.2))

theorem inc_mul (a b : Gp U hU) : inc (a * b) = lmulM (Matrix.of (inc a)) (inc b) := rfl

instance : IsTopologicalGroup (Gp U hU) where
  continuous_mul := by
    refine Continuous.subtype_mk (mulM_cont.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    exact invM_contOn.comp_continuous continuous_subtype_val (fun x => (hU.unit _ x.2).ne_zero)

def pull (hU : IsClosedSubgroup U) (μ : Measure (Mt k r)) : Measure (Gp U hU) := μ.comap inc

theorem map_pull (μ : Measure (Mt k r)) (h : μ Uᶜ = 0) : (pull hU μ).map inc = μ := by
  rw [pull, inc_memb.map_comap, range_inc]
  exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h)

theorem pull_left (μ : Measure (Mt k r)) (h : ∀ a ∈ U, μ.map (lmulM a) = μ) : (pull hU μ).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_const_mul g).measurable hs, pull, inc_memb.comap_apply, inc_memb.comap_apply]
  have e1 : (μ.map (lmulM (Matrix.of (inc g)))) (inc '' s) = μ (inc '' s) :=
    congrArg (fun m : Measure (Mt k r) => m (inc '' s)) (h (Matrix.of (inc g)) (inc_mem g))
  have e2 := Measure.map_apply (μ := μ) (lmulM_cont (Matrix.of (inc g))).measurable (inc_memb.measurableSet_image.2 hs)
  rw [← e1, e2]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y, hy, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨g⁻¹ * z, ?_, ?_⟩
    · show g * (g⁻¹ * z) ∈ s
      rw [mul_inv_cancel_left]; exact hz
    · rw [inc_mul, hzx]
      exact Matrix.nonsing_inv_mul_cancel_left (Matrix.of (inc g) : Mat k r) (Matrix.of x : Mat k r) (hU.unit _ (inc_mem g))

theorem pull_fin (μ : Measure (Mt k r)) (h : ∀ K : Set (Mt k r), IsCompact K → μ K < ∞) :
    IsFiniteMeasureOnCompacts (pull hU μ) := by
  refine ⟨fun K hK => ?_⟩
  rw [pull, inc_memb.comap_apply]
  exact h _ (hK.image inc_cont)

theorem haarUnique : HaarUnique := by
  intro k r U μ ν hU hμ hν0 hνl hνc
  have : (pull hU μ).IsMulLeftInvariant := pull_left μ hμ.left
  have : (pull hU ν).IsMulLeftInvariant := pull_left ν hνl
  have : IsFiniteMeasureOnCompacts (pull hU μ) := pull_fin μ hμ.finite_compact
  have : IsFiniteMeasureOnCompacts (pull hU ν) := pull_fin ν hνc
  have h0 : pull hU μ ≠ 0 := by
    intro h
    apply hμ.ne_zero
    rw [← map_pull (hU := hU) μ hμ.conc, h, Measure.map_zero]
  obtain ⟨K, hK, hK0⟩ := exists_pos (pull hU μ) h0
  have : (pull hU μ).IsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK hK0
  have : (pull hU μ).IsHaarMeasure := {}
  refine ⟨Measure.haarScalarFactor (pull hU ν) (pull hU μ), ?_⟩
  calc ν = (pull hU ν).map inc := (map_pull ν hν0).symm
    _ = (Measure.haarScalarFactor (pull hU ν) (pull hU μ) • pull hU μ).map inc := by
        rw [← Measure.isMulLeftInvariant_eq_smul (pull hU ν) (pull hU μ)]
    _ = Measure.haarScalarFactor (pull hU ν) (pull hU μ) • μ := by
        rw [Measure.map_smul, map_pull μ hμ.conc]

theorem haarInvFromUnique : HaarInvFromUnique :=
  _root_.UpperTheory.Reformulated.B.BlochKatoDuality.haarInvFromUnique

theorem conjHaar : ConjHaar := by
  intro k r U μ a hU ha h1 h2 hμ
  have hm := (conjM_cont a).measurable
  have haa : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a ha
  have haa' : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hm (show IsOpen (Uᶜ : Set (Mt k r)) from hU.closed.isOpen_compl).measurableSet]
    refine measure_mono_null ?_ hμ.conc
    intro x hx hxU
    exact hx (h1 x hxU)
  · intro u hu
    rw [Measure.map_map (lmulM_cont u).measurable hm]
    have : (lmulM u ∘ conjM a : Mt k r → Mt k r) = conjM a ∘ lmulM (a⁻¹ * u * a) := by
      funext x
      show u * (a * Matrix.of x * a⁻¹) = a * (a⁻¹ * u * a * Matrix.of x) * a⁻¹
      have : a * (a⁻¹ * u * a * Matrix.of x) = (a * a⁻¹) * u * a * Matrix.of x := by simp only [Matrix.mul_assoc]
      rw [this, haa, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    rw [this, ← Measure.map_map hm (lmulM_cont _).measurable, hμ.left _ (h2 u hu)]
  · intro u hu
    rw [Measure.map_map (rmulF_cont u).measurable hm]
    have : (rmulF u ∘ conjM a : Mt k r → Mt k r) = conjM a ∘ rmulF (a⁻¹ * u * a) := by
      funext x
      show (a * Matrix.of x * a⁻¹) * u = a * (Matrix.of x * (a⁻¹ * u * a)) * a⁻¹
      have : a * (Matrix.of x * (a⁻¹ * u * a)) * a⁻¹ = a * Matrix.of x * a⁻¹ * u * (a * a⁻¹) := by
        simp only [Matrix.mul_assoc]
      rw [this, haa, Matrix.mul_one]
    rw [this, ← Measure.map_map hm (rmulF_cont _).measurable, hμ.right _ (h2 u hu)]
  · intro K hK
    rw [Measure.map_apply hm hK.isClosed.measurableSet]
    have hsub : (conjM a : Mt k r → Mt k r) ⁻¹' K ⊆ (conjM a⁻¹ : Mt k r → Mt k r) '' K := by
      intro x hx
      refine ⟨conjM a x, hx, ?_⟩
      show a⁻¹ * (a * Matrix.of x * a⁻¹) * a⁻¹⁻¹ = x
      rw [Matrix.nonsing_inv_nonsing_inv a ha]
      have : a⁻¹ * (a * Matrix.of x * a⁻¹) * a = (a⁻¹ * a) * Matrix.of x * (a⁻¹ * a) := by simp only [Matrix.mul_assoc]
      rw [this, haa', Matrix.one_mul, Matrix.mul_one]; rfl
    exact lt_of_le_of_lt (measure_mono hsub) (hμ.finite_compact _ (hK.image (conjM_cont a⁻¹)))
  · intro h0
    apply hμ.ne_zero
    have := congrArg (fun ν : Measure (Mt k r) => ν Set.univ) h0
    simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
    exact Measure.measure_univ_eq_zero.mp this

theorem conjM_conjM (a b : Mat k r) (x : Mt k r) : conjM a (conjM b x) = conjM (a * b) x := by
  show a * (b * Matrix.of x * b⁻¹) * a⁻¹ = (a * b) * Matrix.of x * (a * b)⁻¹
  rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]

theorem conjM_inv_conjM (a : Mat k r) (ha : IsUnit a.det) (x : Mt k r) : conjM a⁻¹ (conjM a x) = x := by
  rw [conjM_conjM, Matrix.nonsing_inv_mul a ha]
  show (1 : Mat k r) * Matrix.of x * (1 : Mat k r)⁻¹ = x
  rw [inv_one, Matrix.one_mul, Matrix.mul_one]; rfl

def conj2 (p : Mt k r × Mt k r) : Mt k r := mulM (mulM (p.1, p.2), invM p.1)

theorem conjugation_pair_eq (b : Mat k r) (x : Mt k r) : conj2 ((b : Mt k r), x) = conjM b x := rfl

theorem conjugation_continuous_on_invertible : ContinuousOn (conj2 : Mt k r × Mt k r → Mt k r) {p | detF p.1 ≠ 0} := by
  unfold conj2
  refine mulM_cont.comp_continuousOn (ContinuousOn.prodMk ?_ ?_)
  · exact (mulM_cont.comp (continuous_fst.prodMk continuous_snd)).continuousOn
  · exact invM_contOn.comp continuous_fst.continuousOn (fun p hp => hp)

theorem compactConjFromUnique : CompactConjFromUnique := by
  intro HU CH k r U K μ hU hKg hKc hnorm hμ a ha
  have hau : IsUnit a.det := hKg.unit a ha
  have hm := (conjM_cont a).measurable
  have hnorm' : ∀ u ∈ U, a⁻¹ * u * a ∈ U := by
    intro u hu
    have := hnorm a⁻¹ (hKg.inv_mem a ha) u hu
    rwa [Matrix.nonsing_inv_nonsing_inv a hau] at this
  have hH : IsHaarOn U (μ.map (conjM a)) := CH k r U μ a hU hau (hnorm a ha) hnorm' hμ
  obtain ⟨c, hc⟩ := HU k r U μ (μ.map (conjM a)) hU hμ hH.conc hH.left hH.finite_compact
  obtain ⟨C, hC, hC0⟩ := exists_pos μ hμ.ne_zero

  set S : Set (Mt k r) := conj2 '' ((K : Set (Mt k r)) ×ˢ C) with hS
  have hSc : IsCompact S :=
    (IsCompact.prod (show IsCompact (K : Set (Mt k r)) from hKc) hC).image_of_continuousOn
      (conjugation_continuous_on_invertible.mono fun p hp => (hKg.unit p.1 hp.1).ne_zero)
  have hCS : C ⊆ S := by
    intro x hx
    refine ⟨(((1 : Mat k r) : Mt k r), x), ⟨hKg.one_mem, hx⟩, ?_⟩
    rw [conjugation_pair_eq]
    show (1 : Mat k r) * Matrix.of x * (1 : Mat k r)⁻¹ = x
    rw [inv_one, Matrix.one_mul, Matrix.mul_one]; rfl
  have hpre : (conjM a : Mt k r → Mt k r) ⁻¹' S = S := by
    ext x
    constructor
    · rintro ⟨⟨b, y⟩, ⟨hb, hy⟩, hby⟩
      refine ⟨(((a⁻¹ * (Matrix.of b : Mat k r) : Mat k r) : Mt k r), y), ⟨hKg.mul_mem _ (hKg.inv_mem a ha) _ hb, hy⟩, ?_⟩
      rw [conjugation_pair_eq, ← conjM_conjM, ← conjM_inv_conjM a hau x]
      congr 1
    · rintro ⟨⟨b, y⟩, ⟨hb, hy⟩, rfl⟩
      refine ⟨(((a * (Matrix.of b : Mat k r) : Mat k r) : Mt k r), y), ⟨hKg.mul_mem _ ha _ hb, hy⟩, ?_⟩
      rw [conjugation_pair_eq, ← conjM_conjM]; rfl
  have hS0 : μ S ≠ 0 := fun h => hC0 (measure_mono_null hCS h)
  have hSt : μ S ≠ ∞ := (hμ.finite_compact S hSc).ne
  have h4 := congrArg (fun ν : Measure (Mt k r) => ν S) hc
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h4
  rw [Measure.map_apply hm hSc.isClosed.measurableSet, hpre] at h4
  have h5 : ((c : ℝ≥0) : ℝ≥0∞) * μ S = 1 * μ S := by rw [one_mul]; exact h4.symm
  have h6 : ((c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hS0 hSt).mp h5
  have h7 : c = 1 := by exact_mod_cast h6
  rw [hc, h7, one_smul]

end Formalism.FourierDecayAlt.P.B2x1

namespace Formalism.FourierDecayAlt.P

theorem haar_measure_unique_up_to_scalar : Formalism.FourierDecayAlt.B2.HaarUnique := B2x1.haarUnique

theorem haar_inversion_of_uniqueness : Formalism.FourierDecayAlt.B2.HaarInvFromUnique := B2x1.haarInvFromUnique

theorem haar_measure_inversion : Formalism.FourierDecayAlt.B2.HaarInv := B2x1.haarInvFromUnique B2x1.haarUnique

theorem conjugation_preserves_haar : Formalism.FourierDecayAlt.B2.ConjHaar := B2x1.conjHaar

theorem compact_conjugation_of_uniqueness : Formalism.FourierDecayAlt.B2.CompactConjFromUnique := B2x1.compactConjFromUnique

theorem compact_subgroup_conjugation : Formalism.FourierDecayAlt.B2.CompactConj := B2x1.compactConjFromUnique B2x1.haarUnique B2x1.conjHaar

end Formalism.FourierDecayAlt.P
