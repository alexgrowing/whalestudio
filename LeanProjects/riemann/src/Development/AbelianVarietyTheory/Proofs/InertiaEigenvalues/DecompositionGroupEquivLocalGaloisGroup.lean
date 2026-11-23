import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemSpanLIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemIntegralClosureIffMemBall
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.ExistsDen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.SpanLIsMaximal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionGroupEquivPadicGaloisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInertiaIffMemPlaceInertiaStatement

noncomputable section

namespace GlobalTheory.DecLocal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem exists_place_below : ∀ {p : ℕ} [Fact p.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 →
    ∃ w : HeightOneSpectrum (𝓞 F), w ∈ Formalism.BasicNotions.placesOver F p ∧ IsPlaceOver A w := by
  intro p _ F Ω _ _ _ _ A hp
  have hint : ∀ x : 𝓞 F, algebraMap F Ω (x : F) ∈ A := fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A ((NumberField.RingOfIntegers.isIntegral_coe x).algebraMap)
  let f : 𝓞 F →+* A := RingHom.codRestrict ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)) A hint
  let I : Ideal (𝓞 F) := Ideal.comap f (IsLocalRing.maximalIdeal A)
  have hI : ∀ x : 𝓞 F, x ∈ I ↔ A.valuation (algebraMap F Ω (x : F)) < 1 := fun x => by
    change f x ∈ IsLocalRing.maximalIdeal A ↔ _
    exact ValuationSubring.valuation_lt_one_iff A (f x)
  have hpI : ((p : 𝓞 F)) ∈ I := by
    rw [hI]; simpa using hp
  have hp0 : ((p : 𝓞 F)) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  let w : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := I, isPrime := Ideal.comap_isPrime f _,
      ne_bot := fun h => hp0 (by rw [← Ideal.mem_bot, ← h]; exact hpI) }
  exact ⟨w, hpI, fun x => (hI x).symm⟩

theorem exists_root_of_unity : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl p)
    (n : ℕ) (z : PadicAlgCl p), z ^ (p ^ n) = 1 → ∃ y : Ω, y ^ (p ^ n) = 1 ∧ j y = z := by
  intro p _ Ω _ _ j n z hz
  have hf : ((X ^ (p ^ n) - 1 : Polynomial Ω).map j) = X ^ (p ^ n) - 1 := by simp
  have hne : (X ^ (p ^ n) - 1 : Polynomial (PadicAlgCl p)) ≠ 0 := by
    simpa using X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) (1 : PadicAlgCl p)
  have hz' : z ∈ ((X ^ (p ^ n) - 1 : Polynomial Ω).map j).roots := by
    rw [hf, mem_roots hne]; simp [hz]
  rw [Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hz'
  obtain ⟨y, hy, rfl⟩ := hz'
  refine ⟨y, ?_, rfl⟩
  have := isRoot_of_mem_roots hy
  simpa [sub_eq_zero] using this

theorem norm_lt_one_iff {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p)
    (hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (y : Ω) : ‖j y‖ < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', hA, hA]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h0 : 0 < ‖j y‖ := norm_pos_iff.2 ((map_ne_zero j).2 hy)
    rw [map_inv₀, norm_inv]
    simp only [hy, false_or]
    constructor
    · intro h
      exact ⟨h.le, not_le.2 ((one_lt_inv₀ h0).2 h)⟩
    · rintro ⟨h1, h2⟩
      refine lt_of_le_of_ne h1 fun h => h2 ?_
      rw [h, inv_one]

theorem finrank_closure_eq_locDeg : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v →
      Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x))) =
        locDeg v := by
  intro p _ F Ω _ _ _ _ A j hA v hv
  let φ : F →+* PadicAlgCl p := j.comp (algebraMap F Ω)
  obtain ⟨v', -, hφ⟩ := PI.CompDegEF.placeProp p F φ
  have hvp : v ∈ Formalism.BasicNotions.placesOver F p := by
    show ((p : 𝓞 F)) ∈ v.asIdeal
    rw [← hv, ← norm_lt_one_iff A j hA]
    simpa using GlobalTheory.PlaceBridge.norm_l_lt_one (l := p)
  exact PI.CompDegEF.locDegOf_of PI.CompDegEF.ballCard PI.CompDegEF.denseSurj PI.CompDegEF.kerProp
    PI.CompDegEF.normCard p F φ ⟨_, GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range φ⟩
    (fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
    (GlobalTheory.PlaceBridge.adjoin_range_subset_closure φ) v hvp
    (fun x => ⟨(hφ x).1, (norm_lt_one_iff A j hA _).trans (hv x)⟩)

theorem decEquiv : ReciprocityTheory.ChartRestriction.T2.DecEquiv := by
  intro p _ F Ω _ _ _ _ _ A hp
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  obtain ⟨w, hw, hAw⟩ := exists_place_below (F := F) A hp
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding F Ω w A hw hAw
  obtain ⟨i, hi⟩ := GlobalTheory.T.exists_decompositionGroup_equiv_padicGalois p F Ω A j hj
  refine ⟨_, GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω)), i, ?_,
    fun g => GlobalTheory.T.localInertia_iff_mem_placeInertia p F Ω A j hj _ i.toMulEquiv hi g,
    fun v hv => finrank_closure_eq_locDeg p F Ω A j hj v hv⟩
  intro O _ ε hε g n ζ hζ
  obtain ⟨y, hy, rfl⟩ := exists_root_of_unity p Ω j n ζ hζ
  obtain ⟨a, ha, ha'⟩ := hε (i.symm g) n y hy
  refine ⟨a, ?_, ha'⟩
  have e := hi (i.symm g) y
  rw [ContinuousMulEquiv.apply_symm_apply] at e
  rw [e, ha, map_pow]

end GlobalTheory.DecLocal
