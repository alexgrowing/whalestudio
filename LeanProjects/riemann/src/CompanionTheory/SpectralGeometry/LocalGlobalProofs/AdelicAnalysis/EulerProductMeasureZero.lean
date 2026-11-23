import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.EulerZero

theorem exists_tail_pos {ι : Type} {a : ι → ℝ} (h : Summable (fun v => |a v - 1|)) (S₀ : Finset ι) :
    ∃ S : Finset ι, S₀ ⊆ S ∧ 0 < ∏' v : {v // v ∉ S}, a v.1 := by
  classical
  have hev : ∀ᶠ v in Filter.cofinite, |a v - 1| < 1 :=
    h.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  have hfin : {v | ¬ |a v - 1| < 1}.Finite := Filter.eventually_cofinite.1 hev
  refine ⟨S₀ ∪ hfin.toFinset, Finset.subset_union_left, ?_⟩
  have hs : Summable (fun v : {v // v ∉ S₀ ∪ hfin.toFinset} => |a v.1 - 1|) :=
    h.comp_injective Subtype.val_injective
  refine (AbsTprod.abs_tprod _ (fun v : {v // v ∉ S₀ ∪ hfin.toFinset} => a v.1) hs).2.2.1 ?_
  rintro ⟨v, hv⟩
  have hv' : |a v - 1| < 1 := by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hc))
  have := (abs_lt.1 hv').1
  show 0 < a v
  linarith

theorem countable_places (F : Type) [Field F] [NumberField F] :
    Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable (𝓞 F) := by
    haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact RingOfIntegers.coe_injective.countable
  haveI : Countable (Ideal (𝓞 F)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_
    intro I
    exact (IsNoetherian.noetherian I : I.FG)
  exact Function.Injective.countable (f := fun la : HeightOneSpectrum (𝓞 F) => la.asIdeal)
    fun a b h => HeightOneSpectrum.ext h

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem exists_measure_intOff {d M n : ℕ} {b : Module.Basis (Fin d) F E}
    {I : Measure (Fin n → Fin M → AF F ⊗[F] E)} {c : ℝ≥0}
    {minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)}
    {m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)}
    (h : IsEulerProd b I c minf m)
    (hmeas : ∀ S, MeasurableSet (intOff (n := n) (M := M) b S)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      I (intOff b S) = (c : ℝ≥0∞) * (minf Set.univ * ∏ v ∈ S, m v Set.univ) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) := by
  obtain ⟨-, -, S₀, hS₀⟩ := h
  refine ⟨S₀, fun S hS => ?_⟩
  have key := hS₀ S hS (fun _ => 1) (fun _ _ => 1) measurable_const (fun _ => measurable_const)
  have hp : pureL b S (fun _ => 1) (fun _ _ => 1) = (intOff (n := n) (M := M) b S).indicator 1 := by
    funext X
    simp [pureL, Set.indicator]
  rw [hp, lintegral_indicator_one (hmeas S)] at key
  simpa using key

end GlobalTheory.CompanionTheory.SW.EulerZero

open GlobalTheory.CompanionTheory.SW.EulerZero in

theorem GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (IsEulerProd b I c minf m → I = 0 → c = 0 ∨ minf = 0 ∨ ∃ v, m v = 0) ∧ (IsEulerProd b I c minf m → (minf = 0 ∨ ∃ v, m v = 0) → I = 0) ∧ ((∀ v, m v (latV b v) < ⊤) → Summable (fun v => |(m v (latV b v)).toReal - 1|) → (minf = 0 ∨ ∃ v, m v = 0) → IsEulerProd b 0 c minf m) := by
  intro F E _ _ _ _ _ σ hσ d b n M I c minf m
  obtain ⟨-, -, -, -, hopen, hcof, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨-, -, -, -, -, -, -, hborel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  haveI := hborel n M
  have hmeas : ∀ S, MeasurableSet (intOff (n := n) (M := M) b S) := fun S => (hopen S).measurableSet
  refine ⟨fun h hI => ?_, fun h hz => ?_, fun hfin hsum hz => ?_⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨hc, hminf, hm⟩ := hcon
    obtain ⟨S₀, hS₀⟩ := exists_measure_intOff h hmeas
    obtain ⟨S, hS, hpos⟩ := exists_tail_pos h.2.1 S₀
    have key := hS₀ S hS
    rw [hI] at key
    have h1 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
    have h2 : minf Set.univ ≠ 0 := by simpa using hminf
    have h3 : ∏ v ∈ S, m v Set.univ ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun v _ => by simpa using hm v
    have h4 : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) ≠ 0 := by
      simpa using hpos
    exact (mul_ne_zero (mul_ne_zero h1 (mul_ne_zero h2 h3)) h4) (by simpa using key.symm)
  · obtain ⟨S₀, hS₀⟩ := exists_measure_intOff h hmeas
    classical
    obtain ⟨S₁, hS₁, hzero⟩ : ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S₁ ∧
        ∀ S, S₁ ⊆ S → minf Set.univ * ∏ v ∈ S, m v Set.univ = 0 := by
      rcases hz with hz | ⟨v, hv⟩
      · exact ⟨S₀, subset_rfl, fun S _ => by simp [hz]⟩
      · refine ⟨insert v S₀, Finset.subset_insert _ _, fun S hS => ?_⟩
        rw [Finset.prod_eq_zero (hS (Finset.mem_insert_self v S₀)) (by simp [hv]), mul_zero]
    haveI := countable_places F
    have hcover : (Set.univ : Set (Fin n → Fin M → AF F ⊗[F] E)) ⊆
        ⋃ T : Finset (HeightOneSpectrum (𝓞 F)), intOff b (S₁ ∪ T) := by
      intro X _
      have hT := Filter.eventually_cofinite.1 (hcof (projFin X))
      refine Set.mem_iUnion.2 ⟨hT.toFinset, fun v hv => ?_⟩
      by_contra hc
      exact hv (Finset.mem_union_right _ (hT.mem_toFinset.2 hc))
    have hnull : I Set.univ = 0 := by
      refine measure_mono_null hcover (measure_iUnion_null fun T => ?_)
      rw [hS₀ _ (hS₁.trans Finset.subset_union_left), hzero _ Finset.subset_union_left]
      simp
    exact Measure.measure_univ_eq_zero.1 hnull
  · refine ⟨hfin, hsum, ?_⟩
    classical
    obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), minf = 0 ∨ ∃ v ∈ S₀, m v = 0 := by
      rcases hz with hz | ⟨v, hv⟩
      · exact ⟨∅, Or.inl hz⟩
      · exact ⟨{v}, Or.inr ⟨v, by simp, hv⟩⟩
    refine ⟨S₀, fun S hS φinf φ _ _ => ?_⟩
    rcases hS₀ with hz | ⟨v, hv, hmv⟩
    · simp [hz]
    · rw [Finset.prod_eq_zero (hS hv) (by simp [hmv])]
      simp
