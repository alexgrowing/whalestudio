import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree.FibMass

theorem sig_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

theorem gram_mem {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (R : Type) [CommRing R]
    [Algebra F R] (hs : ∀ x, σ (σ x) = x) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := by
  intro a c
  have hi : ∀ y : E, sigR R σ (inclR R y) = inclR R (σ y) := fun y => by simp [sigR, inclR]
  change sigR R σ (hR R σ J (X c) (X a)) = hR R σ J (X a) (X c)
  simp only [hR, hform, JR, map_sum, map_mul, Matrix.map_apply, sigR_sigR R σ hs, hi, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.CompanionTheory.AvgFree.FibMass

theorem GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n : ℕ) (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ Tt : Set (Fin n → Fin M → (Fv F v ⊗[F] E)), IsCompact Tt → IsOpen Tt → Tt ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} → (∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (Tt ∩ gramIn (Fv F v) σ J Y) = ∫⁻ y in Y, mv y Tt ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n)) ∧ Continuous (fun y => (mv y Tt).toReal) ∧ (∀ y, mv y Tt ≠ ⊤) ∧ ∃ C : ℝ≥0, ∀ y, mv y Tt ≤ C := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv M J hJ n mv hmv Tt hTc hTo hTf
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  haveI hBH : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  obtain ⟨h1, h2, h3⟩ := hmv
  have hinv : ∀ e, σ (σ e) = e := GlobalTheory.CompanionTheory.AvgFree.FibMass.sig_inv hσ
  have hgc : Continuous (gramR (Fv F v) σ J : (Fin n → Fin M → Fv F v ⊗[F] E) → _) := a10 n M J

  let q : (Fin n → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ n := fun X =>
    ⟨gramR (Fv F v) σ J X, GlobalTheory.CompanionTheory.AvgFree.FibMass.gram_mem (Fv F v) hinv hJ.1 X⟩
  have hqc : Continuous q := hgc.subtype_mk _
  have hTm : MeasurableSet Tt := hTo.measurableSet

  have hae : ∀ y, ∀ᵐ x ∂(mv y), q x = y := fun y => by
    refine measure_mono_null ?_ (h1 y)
    intro x hx hx'
    exact hx (Subtype.ext hx'.1)

  let φ : (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ := Tt.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hTo.frontier_eq, hTc.isClosed.closure_eq]
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro hTc fun x hx => Set.indicator_of_notMem hx _
  have hφt : tsupport φ ⊆ {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
    refine subset_trans (closure_minimal ?_ hTc.isClosed) hTf
    intro x hx
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨hI, hC⟩ := h3 φ hφc hφs hφt
  have hint : ∀ y, ∫ X, φ X ∂(mv y) = (mv y Tt).toReal := fun y => by
    simp [φ, integral_indicator hTm, Measure.real]
  have hfin : ∀ y, mv y Tt ≠ ⊤ := fun y => by
    have h := hI y (Set.mem_univ y)
    rw [integrable_indicator_iff hTm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  have hcont : Continuous fun y => (mv y Tt).toReal := by
    have h := continuousOn_univ.1 hC
    simpa only [hint] using h
  refine ⟨fun Y hY => ?_, hcont, hfin, ?_⟩
  · have hG : gramIn (Fv F v) σ J Y = q ⁻¹' Y := by
      ext X
      constructor
      · rintro ⟨y, hy, e⟩
        have : q X = y := Subtype.ext e
        show q X ∈ Y
        rwa [this]
      · intro hX
        exact ⟨q X, hX, rfl⟩
    rw [hG]
    have hqY : MeasurableSet (q ⁻¹' Y) := hqc.measurable hY
    have hT : MeasurableSet (Tt ∩ q ⁻¹' Y) := hTm.inter hqY
    have e := h2 ((Tt ∩ q ⁻¹' Y).indicator 1) (measurable_one.indicator hT)
    rw [lintegral_indicator_one hT, Measure.restrict_apply hT,
      Set.inter_eq_left.2 (Set.inter_subset_left.trans hTf)] at e
    rw [e, ← lintegral_indicator hY]
    refine lintegral_congr fun y => ?_
    rw [lintegral_indicator_one hT]
    by_cases hy : y ∈ Y
    · rw [Set.indicator_of_mem hy]
      refine measure_congr ?_
      filter_upwards [hae y] with x hx
      refine propext ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      show q x ∈ Y
      rwa [hx]
    · rw [Set.indicator_of_notMem hy]
      refine measure_mono_null (t := {x | ¬ q x = y}) ?_ (hae y)
      intro x hx hxy
      apply hy
      rw [← hxy]
      exact hx.2
  · obtain ⟨C, hC'⟩ := (hTc.image hqc).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨Real.toNNReal C, fun y => ?_⟩
    by_cases hy : y ∈ q '' Tt
    · have h := hC' y hy
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at h
      show mv y Tt ≤ ENNReal.ofReal C
      exact (ENNReal.le_ofReal_iff_toReal_le (hfin y) (ENNReal.toReal_nonneg.trans h)).2 h
    · have h0 : mv y Tt = 0 := by
        refine measure_mono_null ?_ (h1 y)
        intro x hx hx'
        exact hy ⟨x, hx, Subtype.ext hx'.1⟩
      rw [h0]
      exact bot_le
