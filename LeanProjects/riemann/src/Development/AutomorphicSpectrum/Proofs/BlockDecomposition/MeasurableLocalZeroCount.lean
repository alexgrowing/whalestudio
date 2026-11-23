import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableZeroCountStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RandomSectionZeroCountStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.FSCrofton.Chart

theorem measurableSet_of_isSigmaCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {A : Set X} (hA : IsSigmaCompact A) :
    MeasurableSet A := by
  obtain ⟨K, hK, rfl⟩ := hA
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

variable {Y : Var ℂ} {L : LB Y.X}

noncomputable def chartVal {n : ℕ} (b : Fin n → L.Sec) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim)
    (i : L.ι) (j : Fin n) (v : ReciprocityTheory.L2DbarEstimates.V Y.dim) : ℂ :=
  secVal Y.str (RingHom.id ℂ) (b j) i (c.e.symm v)

theorem encard_eq_zeroCnt {n : ℕ} (b : Fin n → L.Sec) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim)
    (i : L.ι) (A : Set (CxPts Y.str (RingHom.id ℂ))) (hAc : A ⊆ c.e.source)
    (hAi : A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i)) (C : Fin Y.dim → Fin n → ℂ) :
    (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞) =
      zeroCnt Y.dim (c.e '' A) (chartVal b c i) C := by
  have hinj : Set.InjOn c.e {y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0} :=
    c.e.injOn.mono fun y hy => hAc hy.1
  have himg : c.e '' {y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0} =
      {z ∈ c.e '' A | ∀ k, ∑ j, C k j * chartVal b c i j z = 0} := by
    ext v
    constructor
    · rintro ⟨y, ⟨hyA, hy⟩, rfl⟩
      refine ⟨⟨y, hyA, rfl⟩, fun k => ?_⟩
      simpa only [chartVal, c.e.left_inv (hAc hyA)] using hy k i (hAi hyA)
    · rintro ⟨⟨y, hyA, rfl⟩, hy⟩
      refine ⟨y, ⟨hyA, fun k i' hi' => ?_⟩, rfl⟩
      have h0 : ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0 := by
        simpa only [chartVal, c.e.left_inv (hAc hyA)] using hy k
      have e : ∀ j, secVal Y.str (RingHom.id ℂ) (b j) i' y =
          gv Y.str (RingHom.id ℂ) L i' i y * secVal Y.str (RingHom.id ℂ) (b j) i y :=
        fun j => (secVal_mem (b j)).1 i' i y hi' (hAi hyA)
      simp only [e]
      calc ∑ j, C k j * (gv Y.str (RingHom.id ℂ) L i' i y * secVal Y.str (RingHom.id ℂ) (b j) i y)
          = gv Y.str (RingHom.id ℂ) L i' i y *
              ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [h0, mul_zero]
  rw [zeroCnt, ← himg, hinj.encard_image]

theorem fsBasis_φ_chart (hL : L.IsLB) {n : ℕ} (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤)
    (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι) (v : ReciprocityTheory.L2DbarEstimates.V Y.dim) :
    (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).φ i (c.e.symm v) =
      Real.log (∑ j, ‖chartVal b c i j v‖ ^ 2) := by
  rw [Weight.fsBasis_φ]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rfl

theorem chernPart_eq_lintegral (hL : L.IsLB) {n : ℕ} (b : Fin n → L.Sec)
    (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι)
    (A : Set (CxPts Y.str (RingHom.id ℂ))) (hAm : MeasurableSet A) (hAc : A ⊆ c.e.source)
    (hAi : A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i)) (hBm : MeasurableSet (c.e '' A)) :
    (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernPart Y.dim 1 A =
      ∫⁻ z in c.e '' A, ENNReal.ofReal ((Y.dim.factorial : ℝ) / Real.pi ^ Y.dim *
        (ReciprocityTheory.L2DbarEstimates.cHess Y.dim
          (fun v => ((Real.log (∑ j, ‖chartVal b c i j v‖ ^ 2) : ℝ) : ℂ)) z).det.re) := by
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  have hC := Weight.isCInf_fsBasis (p := Y.str) (σ := RingHom.id ℂ) hL b hb 1 (by simp)
  rw [Weight.chernPart_apply hC 1 c hAm hAc]
  refine setLIntegral_congr_fun hBm fun v hv => ?_
  obtain ⟨y, hy, rfl⟩ := hv
  have hys := c.e.left_inv (hAc hy)
  simp only [hys]
  rw [c.chernDens_eq hC (hAc hy) (hAi hy), AlgChart.hess]
  simp only [fsBasis_φ_chart hL b hb c i, Units.val_one, Int.cast_one, one_mul]

end GlobalTheory.CompanionTheory.FSCrofton.Chart

open GlobalTheory.CompanionTheory.FSCrofton.Chart in

theorem GlobalTheory.CompanionTheory.FSCrofton.crofton_chart : ∀ (Y : Var ℂ) (L : LB Y.X) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι) (j₀ : Fin n) (A : Set (CxPts Y.str (RingHom.id ℂ))), A ⊆ c.e.source → A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i) → (∀ y ∈ A, secVal Y.str (RingHom.id ℂ) (b j₀) i y ≠ 0) → IsSigmaCompact A → Measurable (fun C : Fin Y.dim → Fin n → ℂ => (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞)) ∧ ∫⁻ C : Fin Y.dim → Fin n → ℂ, gW Y.dim (Fin n) C * (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal (Real.pi ^ (Y.dim * n)) * (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernPart Y.dim 1 A := by
  intro Y L hL n b hb c i j₀ A hAc hAi hA0 hAs
  have hAm : MeasurableSet A := measurableSet_of_isSigmaCompact hAs
  have hBs : IsSigmaCompact (c.e '' A) :=
    hAs.image_of_continuousOn (c.e.continuousOn.mono hAc)
  have hBm : MeasurableSet (c.e '' A) := measurableSet_of_isSigmaCompact hBs
  have hcnt := encard_eq_zeroCnt b c i A hAc hAi

  set W : Y.X.Opens := L.U i ⊓ nonzeroLocus (b j₀) with hW
  set U : Set (ReciprocityTheory.L2DbarEstimates.V Y.dim) := c.e.target ∩ c.e.symm ⁻¹' ptsIn Y.str (RingHom.id ℂ) W
    with hU
  have hUo : IsOpen U := ChartGlue.isOpen_over c.e (isOpen_ptsIn W)
  have hUi : ∀ v ∈ U, c.e.symm v ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) := fun v hv =>
    (mem_ptsIn_inf.1 hv.2).1
  have hd : ∀ j, DifferentiableOn ℂ (chartVal b c i j) U := fun j =>
    (c.holo (L.U i) ((b j).f i)).mono fun v hv => ⟨hv.1, hUi v hv⟩
  have h0 : ∀ z ∈ U, chartVal b c i j₀ z ≠ 0 := fun z hz =>
    (secVal_ne_zero_iff (b j₀) (hUi z hz)).2 (mem_ptsIn_inf.1 hz.2).2
  have hBU : c.e '' A ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨c.e.map_source (hAc hy), ?_⟩
    change c.e.symm (c.e y) ∈ ptsIn Y.str (RingHom.id ℂ) W
    rw [c.e.left_inv (hAc hy)]
    exact mem_ptsIn_inf.2 ⟨hAi hy, (secVal_ne_zero_iff (b j₀) (hAi hy)).1 (hA0 y hy)⟩
  refine ⟨?_, ?_⟩
  · simp only [hcnt]
    exact GlobalTheory.T.measurable_zero_count Y.dim (Fin n) U (c.e '' A) (chartVal b c i)
      (fun j => (hd j).continuousOn) hBU hBs
  · simp only [hcnt]
    have key := GlobalTheory.T.random_section_zero_count Y.dim (Fin n) j₀ U (c.e '' A) (chartVal b c i) hUo hd h0 hBU hBs
    rw [key, Fintype.card_fin, chernPart_eq_lintegral hL b hb c i A hAm hAc hAi hBm]
