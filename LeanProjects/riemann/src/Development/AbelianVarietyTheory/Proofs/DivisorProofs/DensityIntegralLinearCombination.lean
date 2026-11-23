import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DensLinear

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem part_off (ρ : AlgChart p σ D → CxPts p σ → ℝ) {S : Set (CxPts p σ)} (hS : MeasurableSet S)
    (h : ∀ c : AlgChart p σ D, Disjoint c.e.source S) : part ρ S = 0 := by
  have key : part ρ ≤ (part ρ).restrict Sᶜ := iSup_le fun c => by
    have e : ChartGlue.chartMeas c.e (fun y => ENNReal.ofReal (ρ c y)) S = 0 := by
      rw [ChartGlue.chartMeas_apply _ _ hS, (h c).inter_eq, Set.image_empty, Measure.restrict_empty,
        lintegral_zero_measure]
    rw [← Measure.restrict_eq_self_of_ae_mem (s := Sᶜ) (compl_mem_ae_iff.2 e)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart p σ D =>
      ChartGlue.chartMeas c.e fun y => ENNReal.ofReal (ρ c y)) c)
  refine le_antisymm ((key S).trans_eq ?_) zero_le
  rw [Measure.restrict_apply hS, Set.inter_compl_self, measure_empty]

def off (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) : Set (CxPts p σ) := (⋃ c : AlgChart p σ D, c.e.source)ᶜ

theorem part_off' (ρ : AlgChart p σ D → CxPts p σ → ℝ) : part ρ (off p σ D) = 0 :=
  part_off ρ (isOpen_iUnion fun c : AlgChart p σ D => c.e.open_source).measurableSet.compl fun c =>
    Set.disjoint_compl_right_iff_subset.2 (Set.subset_iUnion (fun c : AlgChart p σ D => c.e.source) c)

variable [SecondCountableTopology (CxPts p σ)]

theorem ext_charts {μ ν : Measure (CxPts p σ)} (hμ : μ (off p σ D) = 0) (hν : ν (off p σ D) = 0)
    (h : ∀ (c : AlgChart p σ D) A, MeasurableSet A → A ⊆ c.e.source → μ A = ν A) : μ = ν := by
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable (fun c : AlgChart p σ D => c.e.source)
    fun c => c.e.open_source
  let s : Option (AlgChart p σ D) → Set (CxPts p σ) := fun o => o.elim (off p σ D) fun c => c.e.source
  refine Measure.ext_of_biUnion_eq_univ (S := insert none (some '' T)) (s := s) ((hTc.image _).insert _) ?_ ?_
  · refine Set.eq_univ_of_forall fun y => ?_
    by_cases hy : y ∈ ⋃ c : AlgChart p σ D, c.e.source
    · rw [← hT] at hy
      obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.1 hy
      exact Set.mem_iUnion₂.2 ⟨some c, Set.mem_insert_of_mem _ ⟨c, hc, rfl⟩, hyc⟩
    · exact Set.mem_iUnion₂.2 ⟨none, Set.mem_insert _ _, hy⟩
  · rintro (_ | c) -
    · show μ.restrict (off p σ D) = ν.restrict (off p σ D)
      rw [Measure.restrict_eq_zero.2 hμ, Measure.restrict_eq_zero.2 hν]
    · show μ.restrict c.e.source = ν.restrict c.e.source
      ext B hB
      rw [Measure.restrict_apply hB, Measure.restrict_apply hB]
      exact h c _ (hB.inter c.e.open_source.measurableSet) Set.inter_subset_right

variable {a b a' b' : AlgChart p σ D → CxPts p σ → ℝ} {f : CxPts p σ → ℝ}

omit [SecondCountableTopology (CxPts p σ)] in
theorem aemeas (ha : IsDens a) (c : AlgChart p σ D) {A : Set (CxPts p σ)} (hc : A ⊆ c.e.source) :
    AEMeasurable (fun v => ENNReal.ofReal (a c (c.e.symm v))) (volume.restrict (c.e '' A)) :=
  (((ha.2 c).aemeasurable c.e.open_target.measurableSet).ennreal_ofReal).mono_measure
    (Measure.restrict_mono ((Set.image_mono hc).trans c.e.image_source_eq_target.subset) le_rfl)

theorem part_add_part (ha : IsDens a) (hb : IsDens b) (ha' : IsDens a') (hb' : IsDens b')
    (h : ∀ c y, ENNReal.ofReal (a c y) + ENNReal.ofReal (b c y) =
      ENNReal.ofReal (a' c y) + ENNReal.ofReal (b' c y)) : part a + part b = part a' + part b' := by
  refine ext_charts (D := D) (by simp [part_off']) (by simp [part_off']) fun c A hA hc => ?_
  rw [Measure.add_apply, Measure.add_apply, ha.part_apply c hA hc, hb.part_apply c hA hc, ha'.part_apply c hA hc,
    hb'.part_apply c hA hc, ← lintegral_add_left' (aemeas ha c hc), ← lintegral_add_left' (aemeas ha' c hc)]
  simp only [h]

omit [SecondCountableTopology (CxPts p σ)] in
theorem isDens_smul (ha : IsDens a) (t : ℝ) : IsDens fun c y => t * a c y :=
  ha.mul (f := fun _ => t) continuous_const

omit [SecondCountableTopology (CxPts p σ)] in
theorem isDens_neg (ha : IsDens a) : IsDens fun c y => -a c y :=
  (isDens_smul ha (-1)).congr fun _ _ _ => by simp

omit [SecondCountableTopology (CxPts p σ)] in
theorem isDens_pos (ha : IsDens a) : IsDens fun c y => max (a c y) 0 :=
  ⟨fun c c' y hy hy' => by
    beta_reduce
    rw [ha.1 c c' y hy hy', mul_max_of_nonneg _ _ (sq_nonneg _), mul_zero],
   fun c => (ha.2 c).sup continuousOn_const⟩

theorem part_smul (ha : IsDens a) {t : ℝ} (ht : 0 ≤ t) :
    part (fun c y => t * a c y) = ENNReal.ofReal t • part a := by
  refine ext_charts (D := D) (part_off' _) (by simp [part_off']) fun c A hA hc => ?_
  rw [Measure.smul_apply, (isDens_smul ha t).part_apply c hA hc, ha.part_apply c hA hc, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp only [ENNReal.ofReal_mul ht]

theorem smul_nonneg (ha : IsDens a) (hf : IntegrableDens a f) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableDens (fun c y => t * a c y) f ∧ densInt (fun c y => t * a c y) f = t * densInt a f := by
  have e : part (fun c y => -(t * a c y)) = ENNReal.ofReal t • part fun c y => -a c y := by
    rw [← part_smul (isDens_neg ha) ht]
    simp only [mul_neg]
  unfold IntegrableDens densInt
  rw [e, part_smul ha ht, integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal ht]
  exact ⟨⟨hf.1.smul_measure ENNReal.ofReal_ne_top, hf.2.smul_measure ENNReal.ofReal_ne_top⟩, by
    simp only [smul_eq_mul, mul_sub]⟩

omit [SecondCountableTopology (CxPts p σ)] in
theorem neg (hf : IntegrableDens a f) :
    IntegrableDens (fun c y => -a c y) f ∧ densInt (fun c y => -a c y) f = -densInt a f := by
  unfold IntegrableDens densInt
  simp only [neg_neg, neg_sub]
  exact ⟨⟨hf.2, hf.1⟩, trivial⟩

theorem smul (ha : IsDens a) (hf : IntegrableDens a f) (t : ℝ) :
    IntegrableDens (fun c y => t * a c y) f ∧ densInt (fun c y => t * a c y) f = t * densInt a f := by
  rcases le_total 0 t with ht | ht
  · exact smul_nonneg ha hf ht
  · have := smul_nonneg (isDens_neg ha) (neg hf).1 (neg_nonneg.2 ht)
    rw [(neg hf).2] at this
    simpa only [neg_mul_neg] using this

theorem ofReal_bal (x y : ℝ) : ENNReal.ofReal (x + y) + ENNReal.ofReal (max x 0 + max y 0 - max (x + y) 0) =
    ENNReal.ofReal x + ENNReal.ofReal y := by
  have h : 0 ≤ max x 0 + max y 0 - max (x + y) 0 :=
    sub_nonneg.2 (max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_nonneg (le_max_right _ _) (le_max_right _ _)))
  have m (z : ℝ) : ENNReal.ofReal z = ENNReal.ofReal (max z 0) := by
    rcases le_total z 0 with hz | hz
    · rw [max_eq_right hz, ENNReal.ofReal_of_nonpos hz, ENNReal.ofReal_zero]
    · rw [max_eq_left hz]
  rw [m (x + y), m x, m y, ← ENNReal.ofReal_add (le_max_right _ _) h,
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
  congr 1
  ring

theorem add (ha : IsDens a) (hb : IsDens b) (hf : IntegrableDens a f) (hg : IntegrableDens b f) :
    IntegrableDens (fun c y => a c y + b c y) f ∧
      densInt (fun c y => a c y + b c y) f = densInt a f + densInt b f := by
  have hr : IsDens fun c y => max (a c y) 0 + max (b c y) 0 - max (a c y + b c y) 0 :=
    ((isDens_pos ha).add (isDens_pos hb)).sub (isDens_pos (ha.add hb))
  have e₁ := part_add_part (ha.add hb) hr ha hb fun c y => ofReal_bal _ _
  have e₂ := part_add_part (isDens_neg (ha.add hb)) hr (isDens_neg ha) (isDens_neg hb) fun c y => by
    rw [← ofReal_bal (-a c y) (-b c y), neg_add]
    congr 2
    rw [← neg_add]
    have m (z : ℝ) : max (-z) 0 = max z 0 - z := by
      rcases le_total z 0 with hz | hz
      · rw [max_eq_right hz, max_eq_left (neg_nonneg.2 hz), zero_sub]
      · rw [max_eq_left hz, max_eq_right (neg_nonpos.2 hz), sub_self]
    rw [m, m, m]
    ring
  have i₁ := hf.1.add_measure hg.1
  have i₂ := hf.2.add_measure hg.2
  have j₁ := integral_add_measure hf.1 hg.1
  have j₂ := integral_add_measure hf.2 hg.2
  rw [← e₁] at i₁ j₁
  rw [← e₂] at i₂ j₂
  rw [integrable_add_measure] at i₁ i₂
  rw [integral_add_measure i₁.1 i₁.2] at j₁
  rw [integral_add_measure i₂.1 i₂.2] at j₂
  refine ⟨⟨i₁.1, i₂.1⟩, ?_⟩
  unfold densInt
  linarith

omit [SecondCountableTopology (CxPts p σ)] in
theorem zero : IntegrableDens (fun (_ : AlgChart p σ D) _ => 0) f ∧
    densInt (fun (_ : AlgChart p σ D) _ => 0) f = 0 := by
  unfold IntegrableDens densInt
  rw [MixDens.part_eq_zero fun _ _ _ => le_rfl, MixDens.part_eq_zero fun _ _ _ => neg_zero.le]
  simp

end GlobalTheory.DensLinear

open GlobalTheory.DensLinear in

theorem GlobalTheory.DensLinear.densInt_sum : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) [SecondCountableTopology (CxPts p σ)] (I : Type) [Fintype I] (c : I → ℝ) (ρ : I → AlgChart p σ D → CxPts p σ → ℝ) (f : CxPts p σ → ℝ), (∀ j, IsDens (ρ j)) → (∀ j, IntegrableDens (ρ j) f) → IntegrableDens (fun ch y => ∑ j, c j * ρ j ch y) f ∧ densInt (fun ch y => ∑ j, c j * ρ j ch y) f = ∑ j, c j * densInt (ρ j) f := by
  intro k _ X p σ D _ I _ c ρ f hρ hf
  have key : ∀ s : Finset I, IntegrableDens (fun ch y => ∑ j ∈ s, c j * ρ j ch y) f ∧
      densInt (fun ch y => ∑ j ∈ s, c j * ρ j ch y) f = ∑ j ∈ s, c j * densInt (ρ j) f := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using GlobalTheory.DensLinear.zero
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      have h₁ := GlobalTheory.DensLinear.smul (hρ i) (hf i) (c i)
      have h₂ := GlobalTheory.DensLinear.add (isDens_smul (hρ i) (c i))
        (IsDens.sum s (τ := fun j ch y => c j * ρ j ch y) fun j => isDens_smul (hρ j) (c j)) h₁.1 ih.1
      rw [h₁.2, ih.2] at h₂
      exact h₂
  exact key Finset.univ
