import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMultiplicationStableStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationModuleUnitDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeRealEmbeddingEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeImageDiscreteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeImageSpansRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDualIntegralImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTraceFormImaginaryPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmSkewIdealFractionalIdealStatement

set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatTorus

theorem cm_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) : ∃ (e : Fin (Module.finrank ℚ (FR E)) ≃ I) (e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)),
      ∀ j (x : FR E), ((e' j x : ℝ) : ℂ) = φ (e j) (x : E) :=
  GlobalTheory.T.cm_type_real_embedding_equiv E I φ hφ

theorem lat_discrete (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E)
    (hL : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) (Λ : Submodule ℤ (Fin n → ℂ))
    (hΛ : ∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) : DiscreteTopology Λ :=
  GlobalTheory.T.cm_lattice_image_discrete E I φ hφ n e L hL Λ hΛ

theorem lat_span (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E)
    (hL : ∃ N : ℕ, 0 < N ∧ ∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) (Λ : Submodule ℤ (Fin n → ℂ))
    (hΛ : ∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) :
    Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ :=
  GlobalTheory.T.cm_lattice_image_spans_real E I φ hφ n e L hL Λ hΛ

theorem dual_descent (E : Type) [Field E] [NumberField E] (n : ℕ) (Φ : E →ₗ[ℚ] (Fin n → ℂ)) (L : Set E) (ρ : ℝ)
    (hρ : ρ ≠ 0) (hspan : Submodule.span ℝ (Φ '' L) = ⊤)
    (hrat : ∀ x y : E, ∃ q : ℚ, (∑ j, (ρ : ℂ) * Φ x j * starRingEnd ℂ (Φ y j)).im = q) (w : Fin n → ℂ)
    (hw : ∀ x ∈ L, ∃ m : ℤ, (∑ j, (ρ : ℂ) * w j * starRingEnd ℂ (Φ x j)).im = m) : ∃ x : E, w = Φ x :=
  GlobalTheory.T.cm_lattice_dual_integral_image E n Φ L ρ hρ hspan hrat w hw

theorem trace_eq_im (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) (n : ℕ) (e : Fin n ≃ I) (t₁ : E) (ρ : ℝ) (ht₁ : ∀ i, φ i t₁ = -Complex.I * ((ρ / 2 : ℝ) : ℂ))
    (a : FR E) (x y : E) :
    ((Algebra.trace ℚ E ((a : E) * t₁ * x * bar y) : ℚ) : ℝ) =
      (∑ j, (φ (e j) (a : E) * (ρ : ℂ)) * φ (e j) x * starRingEnd ℂ (φ (e j) y)).im :=
  GlobalTheory.T.cm_trace_form_imaginary_part E I φ hφ n e t₁ ρ ht₁ a x y

theorem exists_fracId (E : Type) [Field E] [NumberField E] [IsCMField E] (M : Submodule (OF E) E) (ξ : E) (hξ : ξ ≠ 0)
    (hbar : bar ξ = -ξ) (hM : ∀ m ∈ M, bar m = -m) (hU : IsUnit M) :
    ∃ 𝔠 : FracId (FR E), ∀ a : FR E, a ∈ 𝔠.elt ↔ (a : E) * ξ ∈ M :=
  GlobalTheory.T.cm_skew_ideal_fractional_ideal E M ξ hξ hbar hM hU

theorem trInt_of_integral {E : Type} [Field E] [NumberField E] {x : E} (hx : IsIntegral ℤ x) : TrInt x := by
  have h := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := E) hx
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by rw [← hn]; simp⟩

end GlobalTheory.LatTorus

open GlobalTheory.LatTorus in

theorem GlobalTheory.LatTorus.exists_unif_of_lattice : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∃ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
        ∀ i, U.h i ≠ 0 ∧ IsAlgebraic ℚ ((U.h i : ℂ) * (Real.sqrt d : ℝ)) := by
  intro K _ _ d δ io _ hd hδ E _ _ _ _ I _ φ hφ hio c y hc
  obtain ⟨N, hN, hNO, hNint⟩ := GlobalTheory.T.exists_denominator_of_adelic_lattice E c hc y
  obtain ⟨hU, hML⟩ := GlobalTheory.T.polarization_module_unit_dual E (latMod c y) ⟨N, hN, hNO, hNint⟩
  obtain ⟨e, e', he'⟩ := cm_equiv E I φ hφ
  have hsd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hsq : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have ht : io δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
  obtain ⟨s, hs, hts⟩ : ∃ s : ℤ, s ^ 2 = 1 ∧ io δ = (s : ℂ) * Complex.I * (Real.sqrt d : ℝ) := by
    have h0 : (io δ - Complex.I * (Real.sqrt d : ℝ)) * (io δ + Complex.I * (Real.sqrt d : ℝ)) = 0 := by
      linear_combination ht - Complex.I ^ 2 * hsq - (d : ℂ) * Complex.I_sq
    rcases mul_eq_zero.1 h0 with h | h
    · exact ⟨1, by norm_num, by push_cast; linear_combination h⟩
    · exact ⟨-1, by norm_num, by push_cast; linear_combination h⟩
  set r : ℝ := 2 / Real.sqrt d with hr
  set ξ₁ : E := -((s : E) * algebraMap K E δ) / (d : E) with hξ₁
  have hne : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
  have hs' : (s : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  have hφξ : ∀ i, φ i ξ₁ = -Complex.I * ((r / 2 : ℝ) : ℂ) := by
    intro i
    have h1 : φ i (algebraMap K E δ) = io δ := by rw [← hio i]; rfl
    simp only [hξ₁, map_div₀, map_neg, map_mul, map_intCast, map_natCast, h1, hts, hr]
    push_cast
    rw [← hsq]
    field_simp
    linear_combination (-1 : ℂ) * hs'
  obtain ⟨σ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨i₀, -, -⟩ := hφ σ₀
  have hr0 : 0 < r := div_pos two_pos hsd
  have hξ0 : ξ₁ ≠ 0 := fun h => by
    have h2 := hφξ i₀
    rw [h, map_zero] at h2
    have h3 : ((r / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (half_pos hr0).ne'
    exact h3 (by simpa [Complex.I_ne_zero] using h2.symm)
  have hbar : bar ξ₁ = -ξ₁ := (φ i₀).injective (by
    show φ i₀ (IsCMField.complexConj E ξ₁) = _
    rw [IsCMField.complexEmbedding_complexConj, hφξ, map_neg, hφξ, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    ring)
  obtain ⟨𝔠, h𝔠⟩ := exists_fracId E (polMod (latMod c y)) ξ₁ hξ0 hbar (fun m hm => hm.1) hU
  have hδint : IsIntegral ℤ (algebraMap K E δ) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), by monicity!, ?_⟩
    have : (algebraMap K E δ) ^ 2 = -(d : E) := by rw [← map_pow, hδ]; simp
    simp [Polynomial.eval₂_add, this]
  set c₀ : FR E := ((N ^ 2 * d : ℕ) : FR E) with hc₀
  have hc₀E : (c₀ : E) * ξ₁ = -((N : E) ^ 2 * (s : E) * algebraMap K E δ) := by
    have hd0 : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [hc₀, hξ₁]
    push_cast
    field_simp
  have hc₀mem : c₀ ∈ 𝔠.elt := by
    rw [h𝔠]
    refine ⟨?_, fun x hx z hz => ?_⟩
    · simp only [hc₀]; push_cast
      show IsCMField.complexConj E _ = _
      simp only [map_mul, map_pow, map_natCast]
      change _ * bar ξ₁ = _
      rw [hbar]; ring
    · apply trInt_of_integral
      rw [hc₀E]
      have h1 := hNint x hx
      have h2 := map_isIntegral_int (IsCMField.complexConj E) (hNint z hz)
      have e1 : -((N : E) ^ 2 * (s : E) * algebraMap K E δ) * x * bar z =
          -((s : E) * algebraMap K E δ * ((N : E) * x) * IsCMField.complexConj E ((N : E) * z)) := by
        simp only [bar, map_mul, map_natCast]; ring
      rw [e1]
      exact (((isIntegral_algebraMap (R := ℤ) (x := s)).mul hδint).mul h1 |>.mul h2).neg
  let Φ : E →ₗ[ℚ] (Fin (Module.finrank ℚ (FR E)) → ℂ) := LinearMap.pi fun j => (φ (e j)).toRatAlgHom.toLinearMap
  have hΦ : ∀ x j, Φ x j = φ (e j) x := fun _ _ => rfl
  let Λ : Submodule ℤ (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    ((latMod c y).restrictScalars ℤ).map (Φ.restrictScalars ℤ)
  have hΛ : ∀ w, w ∈ Λ ↔ ∃ x ∈ latMod c y, w = fun j ↦ φ (e j) x := by
    intro w
    simp only [Λ, Submodule.mem_map, Submodule.restrictScalars_mem, LinearMap.coe_restrictScalars]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  have hdisc := lat_discrete E I φ hφ _ e (latMod c y) ⟨N, hN, hNint⟩ Λ hΛ
  have hfull := lat_span E I φ hφ _ e (latMod c y) ⟨N, hN, hNO⟩ Λ hΛ
  have hstab : ∀ (a : 𝓞 (FR E)), ∀ w ∈ Λ, (fun i ↦ (e' i (a : FR E) : ℂ) * w i) ∈ Λ := by
    intro a w hw
    obtain ⟨x, hx, rfl⟩ := (hΛ w).1 hw
    refine (hΛ _).2 ⟨a • x, (latMod c y).smul_mem a hx, ?_⟩
    funext j
    rw [he', Algebra.smul_def, map_mul]
    rfl
  have htr : ∀ (a : FR E) (x z : E), ((Algebra.trace ℚ E ((a : E) * ξ₁ * x * bar z) : ℚ) : ℝ) =
      (∑ j, ((e' j a * r : ℝ) : ℂ) * φ (e j) x * starRingEnd ℂ (φ (e j) z)).im := by
    intro a x z
    rw [trace_eq_im E I φ hφ _ e ξ₁ r hφξ a x z]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.ofReal_mul, he']
  have hint : ∀ a ∈ 𝔠.elt, ∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ,
      (∑ i, ((e' i a * (fun _ => r) i : ℝ) : ℂ) * l i * starRingEnd ℂ (l' i)).im = n := by
    intro a ha l hl l' hl'
    obtain ⟨x, hx, rfl⟩ := (hΛ l).1 hl
    obtain ⟨z, hz, rfl⟩ := (hΛ l').1 hl'
    obtain ⟨n, hn⟩ := ((h𝔠 a).1 ha).2 x hx z hz
    refine ⟨n, ?_⟩
    rw [← htr, hn]
    simp
  have he'c₀ : ∀ j, e' j c₀ = ((N ^ 2 * d : ℕ) : ℝ) := fun j => by rw [hc₀, map_natCast]
  set ρ : ℝ := ((N ^ 2 * d : ℕ) : ℝ) * r with hρ
  have hρ0 : ρ ≠ 0 := by
    have : (0 : ℝ) < ((N ^ 2 * d : ℕ) : ℝ) := by positivity
    exact (mul_pos this hr0).ne'
  have hsum : ∀ (v : Fin (Module.finrank ℚ (FR E)) → ℂ) (x : E),
      (∑ j, ((e' j c₀ * r : ℝ) : ℂ) * v j * starRingEnd ℂ (φ (e j) x)) =
        ∑ j, (ρ : ℂ) * v j * starRingEnd ℂ (Φ x j) := fun v x =>
    Finset.sum_congr rfl fun j _ => by rw [he'c₀, hΦ]
  have hdual : ∀ w : Fin (Module.finrank ℚ (FR E)) → ℂ, (∀ a ∈ 𝔠.elt, ∀ l ∈ Λ, ∃ n : ℤ,
      (∑ i, ((e' i a * (fun _ => r) i : ℝ) : ℂ) * w i * starRingEnd ℂ (l i)).im = n) → w ∈ Λ := by
    intro w hw
    have hspan : Submodule.span ℝ (Φ '' (latMod c y : Set E)) = ⊤ := by
      have hset : Φ '' (latMod c y : Set E) = (Λ : Set (Fin (Module.finrank ℚ (FR E)) → ℂ)) := by
        ext v
        simp only [Set.mem_image, SetLike.mem_coe, hΛ]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
      rw [hset, hfull]
    have hrat : ∀ x z : E, ∃ q : ℚ, (∑ j, (ρ : ℂ) * Φ x j * starRingEnd ℂ (Φ z j)).im = q := by
      intro x z
      refine ⟨Algebra.trace ℚ E ((c₀ : E) * ξ₁ * x * bar z), ?_⟩
      rw [htr]
      exact (congrArg Complex.im (hsum (fun j => Φ x j) z)).symm
    have hw' : ∀ x ∈ (latMod c y : Set E), ∃ m : ℤ, (∑ j, (ρ : ℂ) * w j * starRingEnd ℂ (Φ x j)).im = m := by
      intro x hx
      obtain ⟨m, hm⟩ := hw c₀ hc₀mem (Φ x) ((hΛ _).2 ⟨x, hx, rfl⟩)
      exact ⟨m, by rw [← hsum]; exact hm⟩
    obtain ⟨x, rfl⟩ := dual_descent E _ Φ (latMod c y) ρ hρ0 hspan hrat w hw'
    have hmx : ∀ m ∈ polMod (latMod c y), m * x ∈ dualLat (latMod c y) := by
      intro m hm z hz
      have hreal : m / ξ₁ ∈ maximalRealSubfield E := by
        rw [← IsCMField.complexConj_eq_self_iff]
        rw [map_div₀]
        change bar m / bar ξ₁ = _
        rw [hm.1, hbar, neg_div_neg_eq]
      set a : FR E := ⟨m / ξ₁, hreal⟩
      have ha : (a : E) * ξ₁ = m := div_mul_cancel₀ m hξ0
      have ha' : a ∈ 𝔠.elt := (h𝔠 a).2 (ha ▸ hm)
      obtain ⟨n, hn⟩ := hw a ha' (Φ z) ((hΛ _).2 ⟨z, hz, rfl⟩)
      refine ⟨n, ?_⟩
      have h1 := htr a x z
      rw [ha] at h1
      have h2 : (∑ j, ((e' j a * r : ℝ) : ℂ) * φ (e j) x * starRingEnd ℂ (φ (e j) z)).im = n := hn
      rw [h2] at h1
      exact_mod_cast h1
    have hsub : polMod (latMod c y) * Submodule.span (OF E) {x} ≤ polMod (latMod c y) * latMod c y := by
      rw [hML]
      refine Submodule.mul_le.2 fun m hm v hv => ?_
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hv
      have : m * (b • x) = (b • m) * x := by rw [Algebra.smul_def, Algebra.smul_def]; ring
      rw [this]
      exact hmx _ ((polMod (latMod c y)).smul_mem b hm)
    obtain ⟨u₀, hu₀⟩ := hU
    have hle : Submodule.span (OF E) {x} ≤ latMod c y := by
      have h3 : (↑u₀⁻¹ : Submodule (OF E) E) * (polMod (latMod c y) * Submodule.span (OF E) {x}) ≤
          (↑u₀⁻¹ : Submodule (OF E) E) * (polMod (latMod c y) * latMod c y) :=
        Submodule.mul_le.2 fun a ha b hb => Submodule.mul_mem_mul ha (hsub hb)
      rwa [← hu₀, ← _root_.mul_assoc, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul, _root_.one_mul] at h3
    exact (hΛ _).2 ⟨x, hle (Submodule.mem_span_singleton_self x), rfl⟩
  have hpos : IsTotPos c₀ := fun τ => by rw [hc₀, map_natCast]; positivity
  obtain ⟨X, u, hu, hact, χ, hχ⟩ := GlobalTheory.T.lattice_multiplication_stable (FR E) e' 𝔠 (fun _ => r) Λ (fun _ => hr0) hdisc hfull hstab hint hdual
    ⟨c₀, hc₀mem⟩ hpos
  refine ⟨𝔠, X, ⟨e, ⟨c₀, hc₀mem⟩, hpos, u, ?_, ?_, fun i => 2 * (e' (e.symm i) c₀ * r), ⟨χ, ?_⟩⟩,
    fun i => ⟨?_, ?_⟩⟩
  · intro w
    rw [hu, hΛ]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by funext j; simp [defCoord]⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by funext j; simp [defCoord]⟩
  · intro a w
    rw [← hact a w]
    congr 1
    funext j
    rw [he']
  · convert hχ using 3
    simp
  · simp only [he'c₀]
    have : (0 : ℝ) < ((N ^ 2 * d : ℕ) : ℝ) := by positivity
    positivity
  · have h4 : ((2 * (e' (e.symm i) c₀ * r) : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = ((4 * (N ^ 2 * d) : ℕ) : ℂ) := by
      rw [he'c₀, hr]
      push_cast
      field_simp
      ring
    rw [h4]
    have h5 := isAlgebraic_algebraMap (R := ℚ) (A := ℂ) ((4 * (N ^ 2 * d) : ℕ) : ℚ)
    rwa [map_natCast] at h5
