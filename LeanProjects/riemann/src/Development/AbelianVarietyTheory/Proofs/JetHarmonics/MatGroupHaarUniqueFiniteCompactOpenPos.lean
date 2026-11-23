import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section
namespace GlobalTheory.MatHaar

open PI Topology

variable {m : ℕ}

abbrev Mx (m : ℕ) := Matrix (Fin m) (Fin m) ℂ

def invA (x : MtM m) : MtM m := Matrix.of.symm ((Matrix.of x : Mx m)⁻¹)

def mulA (p : MtM m × MtM m) : MtM m := (Matrix.of p.1 : Mx m) * (Matrix.of p.2 : Mx m)

def adjA (x : MtM m) : MtM m := (Matrix.of x : Mx m).adjugate

def detA (x : MtM m) : ℂ := (Matrix.of x : Mx m).det

theorem detA_cont : Continuous (detA (m := m)) := Continuous.matrix_det (continuous_id (X := Mx m))
theorem adjA_cont : Continuous (adjA (m := m)) := Continuous.matrix_adjugate (continuous_id (X := Mx m))

theorem invA_smul : (invA : MtM m → MtM m) = fun x => (detA x)⁻¹ • adjA x := by
  funext x
  show (Ring.inverse (Matrix.of x : Mx m).det • (Matrix.of x : Mx m).adjugate : Mx m) = _
  rw [Ring.inverse_eq_inv']; rfl

theorem invA_contOn : ContinuousOn (invA : MtM m → MtM m) {x | detA x ≠ 0} := by
  rw [invA_smul]
  exact (detA_cont.continuousOn.inv₀ (fun x hx => hx)).smul adjA_cont.continuousOn

theorem lmulQ_cont (a : Mx m) : Continuous (lmulQ a : MtM m → MtM m) := by
  unfold lmulQ
  exact (continuous_const (y := a)).matrix_mul (continuous_id (X := Mx m))

theorem mulA_cont : Continuous (mulA : MtM m × MtM m → MtM m) := by
  unfold mulA
  exact Continuous.matrix_mul (A := fun p : MtM m × MtM m => (Matrix.of p.1 : Mx m))
    (B := fun p : MtM m × MtM m => (Matrix.of p.2 : Mx m)) continuous_fst continuous_snd

theorem isUnit_det {G : Set (Mx m)} (hG : IsMatGroup G) {a : Mx m} (ha : a ∈ G) : IsUnit a.det :=
  Matrix.isUnit_det_of_right_inverse (hG.2.2.2 a ha).2

def amb (G : Set (Mx m)) : Set (MtM m) := {x | Matrix.of x ∈ G}

theorem amb_closed {G : Set (Mx m)} (hG : IsMatGroup G) : IsClosed (amb G) := hG.1

def Grp (G : Set (Mx m)) (_hG : IsMatGroup G) : Type := {x : MtM m // x ∈ amb G}

variable {G : Set (Mx m)} {hG : IsMatGroup G}

instance : TopologicalSpace (Grp G hG) := inferInstanceAs (TopologicalSpace {x : MtM m // x ∈ amb G})
instance : MeasurableSpace (Grp G hG) := inferInstanceAs (MeasurableSpace {x : MtM m // x ∈ amb G})
instance : BorelSpace (Grp G hG) := inferInstanceAs (BorelSpace {x : MtM m // x ∈ amb G})
instance : SecondCountableTopology (Grp G hG) :=
  inferInstanceAs (SecondCountableTopology {x : MtM m // x ∈ amb G})
instance : T2Space (Grp G hG) := inferInstanceAs (T2Space {x : MtM m // x ∈ amb G})

def inc (x : Grp G hG) : MtM m := x.1

theorem inc_mem (x : Grp G hG) : Matrix.of (inc x) ∈ G := x.2

theorem inc_cont : Continuous (inc : Grp G hG → MtM m) := continuous_subtype_val

theorem inc_closedEmb : IsClosedEmbedding (inc : Grp G hG → MtM m) :=
  (amb_closed hG).isClosedEmbedding_subtypeVal

theorem inc_memb : MeasurableEmbedding (inc : Grp G hG → MtM m) :=
  MeasurableEmbedding.subtype_coe (amb_closed hG).measurableSet

theorem range_inc : Set.range (inc : Grp G hG → MtM m) = amb G := Subtype.range_coe

instance : LocallyCompactSpace (Grp G hG) := inc_closedEmb.locallyCompactSpace

instance : Group (Grp G hG) where
  mul a b := ⟨mulA (a.1, b.1), hG.2.2.1 _ a.2 _ b.2⟩
  one := ⟨(1 : Mx m), hG.2.1⟩
  inv a := ⟨invA a.1, (hG.2.2.2 _ a.2).1⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc (Matrix.of a.1 : Mx m) (Matrix.of b.1) (Matrix.of c.1))
  one_mul a := Subtype.ext (Matrix.one_mul (Matrix.of a.1 : Mx m))
  mul_one a := Subtype.ext (Matrix.mul_one (Matrix.of a.1 : Mx m))
  inv_mul_cancel a := Subtype.ext (Matrix.nonsing_inv_mul (Matrix.of a.1 : Mx m) (isUnit_det hG a.2))

theorem inc_mul (a b : Grp G hG) : inc (a * b) = lmulQ (Matrix.of (inc a)) (inc b) := rfl

instance : IsTopologicalGroup (Grp G hG) where
  continuous_mul := by
    refine Continuous.subtype_mk (mulA_cont.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    exact invA_contOn.comp_continuous continuous_subtype_val (fun x => (isUnit_det hG x.2).ne_zero)

def pull (hG : IsMatGroup G) (μ : Measure (MtM m)) : Measure (Grp G hG) := μ.comap inc

theorem map_pull (μ : Measure (MtM m)) (h : μ {x | Matrix.of x ∉ G} = 0) : (pull hG μ).map inc = μ := by
  rw [pull, inc_memb.map_comap, range_inc]
  exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h)

theorem pull_left (μ : Measure (MtM m)) (h : ∀ a ∈ G, μ.map (lmulQ a) = μ) : (pull hG μ).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_const_mul g).measurable hs, pull, inc_memb.comap_apply, inc_memb.comap_apply]
  have e1 : (μ.map (lmulQ (Matrix.of (inc g)))) (inc '' s) = μ (inc '' s) :=
    congrArg (fun n : Measure (MtM m) => n (inc '' s)) (h (Matrix.of (inc g)) (inc_mem g))
  have e2 := Measure.map_apply (μ := μ) (lmulQ_cont (Matrix.of (inc g))).measurable (inc_memb.measurableSet_image.2 hs)
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
      exact Matrix.nonsing_inv_mul_cancel_left (Matrix.of (inc g) : Mx m) (Matrix.of x : Mx m)
        (isUnit_det hG (inc_mem g))

theorem pull_sigmaFinite (μ : Measure (MtM m)) [SigmaFinite μ] : SigmaFinite (pull hG μ) := by
  refine ⟨⟨⟨fun n => inc ⁻¹' spanningSets μ n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [pull, inc_memb.comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top μ n)
  · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]

theorem factor_pos_lt_top {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite μ] (h0 : μ ≠ 0)
    (c : ℝ≥0∞) (h : μ = c • ν) : 0 < c ∧ c < ⊤ := by
  refine ⟨pos_iff_ne_zero.2 fun hc => h0 (by rw [h, hc, zero_smul]), lt_top_iff_ne_top.2 fun hc => h0 ?_⟩
  rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets μ]
  refine measure_iUnion_null fun n => ?_
  have h1 := measure_spanningSets_lt_top μ n
  have h2 : μ (spanningSets μ n) = ⊤ * ν (spanningSets μ n) := by
    have := congrArg (fun ρ : Measure X => ρ (spanningSets μ n)) h
    simpa [hc] using this
  by_cases h3 : ν (spanningSets μ n) = 0
  · rw [h2, h3, mul_zero]
  · rw [h2, ENNReal.top_mul h3] at h1
    exact absurd h1 (lt_irrefl _)

def haar0 (hG : IsMatGroup G) : Measure (Grp G hG) := Measure.haar

instance : (haar0 hG).IsHaarMeasure := inferInstanceAs (Measure.IsHaarMeasure Measure.haar)

theorem eq_smul_haar (hG : IsMatGroup G) (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ μ = c • (haar0 hG).map inc := by
  obtain ⟨h1, h2, h3, h4⟩ := hμ
  have := pull_sigmaFinite (hG := hG) μ
  have := pull_left (hG := hG) μ h4
  have e := Measure.haarMeasure_unique (pull hG μ) (Classical.arbitrary _)
  have e' : μ = (pull hG μ (Classical.arbitrary (TopologicalSpace.PositiveCompacts (Grp G hG)) :
      TopologicalSpace.PositiveCompacts (Grp G hG))) • (haar0 hG).map inc := by
    rw [← Measure.map_smul]
    refine (map_pull (hG := hG) μ h3).symm.trans ?_
    exact congrArg (Measure.map inc) e
  obtain ⟨a, b⟩ := factor_pos_lt_top μ _ h2 _ e'
  exact ⟨_, a, b, e'⟩

theorem haar_unique_locFinite_openPos :
    ∀ (m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsHaarOnM G μ →
      (∀ μ' : Measure (PI.MtM m), PI.IsHaarOnM G μ' → ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ μ' = c • μ) ∧
      (∀ K : Set (PI.MtM m), IsCompact K → (∀ x ∈ K, Matrix.of x ∈ G) → μ K < ⊤) ∧
      ∀ U : Set (PI.MtM m), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ G) → 0 < μ U := by
  intro m G μ hG hμ
  obtain ⟨c, hc0, hct, hc⟩ := eq_smul_haar hG μ hμ
  refine ⟨fun μ' hμ' => ?_, fun K hK _ => ?_, fun U hU hx => ?_⟩
  · obtain ⟨d, hd0, hdt, hd⟩ := eq_smul_haar hG μ' hμ'
    refine ⟨d / c, ENNReal.div_pos hd0.ne' hct.ne, ENNReal.div_lt_top hdt.ne hc0.ne', ?_⟩
    rw [hd, hc, smul_smul, ENNReal.div_mul_cancel hc0.ne' hct.ne]
  · rw [hc, Measure.smul_apply, smul_eq_mul, inc_memb.map_apply]
    exact ENNReal.mul_lt_top hct (inc_closedEmb.isCompact_preimage hK).measure_lt_top
  · obtain ⟨x, hxU, hxG⟩ := hx
    rw [hc, Measure.smul_apply, smul_eq_mul, inc_memb.map_apply]
    exact ENNReal.mul_pos hc0.ne' ((hU.preimage inc_cont).measure_ne_zero _ ⟨⟨x, hxG⟩, hxU⟩)

end GlobalTheory.MatHaar

end
