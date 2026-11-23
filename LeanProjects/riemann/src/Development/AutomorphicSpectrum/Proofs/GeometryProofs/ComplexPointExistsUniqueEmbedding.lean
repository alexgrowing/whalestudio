import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo

namespace OverUnique

open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [NumberField F]

theorem evC_eq_aeval (z : (Σ k, ι k) → ℂ) (g : MRing ι) : evC z g = aeval z g := by
  have h : algebraMap ℤ ℂ = Int.castRingHom ℂ := RingHom.ext_int _ _
  simp only [evC, eval_map, aeval_def, h]

theorem homog_X [DecidableEq K] (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (Pi.single p.1 1) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k0, i0⟩ := p
  by_cases h : k = k0
  · subst h
    simp [Finsupp.single_apply]
  · have h' : ∀ i : ι k, ¬ ((⟨k0, i0⟩ : Σ k, ι k) = ⟨k, i⟩) := fun i e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, h', h]

theorem homog_sub {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (hh : IsMultiHomog h d) :
    IsMultiHomog (g - h) d := by
  rw [sub_eq_add_neg]
  refine isMultiHomog_add hg ?_
  intro m hm
  exact hh m (by simpa using hm)

theorem exists_form (c : ∀ k, ι k) (G : MRing ι) :
    ∃ (D : K → ℕ) (H M : MRing ι), IsMultiHomog H D ∧ IsMultiHomog M D ∧
      ∀ (L : Type) [Field L] (w : (Σ k, ι k) → L), (∀ k, w ⟨k, c k⟩ ≠ 0) →
        aeval w M ≠ 0 ∧ aeval w H = aeval w M * aeval (fun p => w p / w ⟨p.1, c p.1⟩) G := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, C a, 1, ?_, isMultiHomog_one, fun L _ w hw => ?_⟩
    · intro m hm k
      have := support_monomial_subset hm
      simp at this
      simp [this]
    · simp
  | add p q hp hq =>
    obtain ⟨D₁, H₁, M₁, h₁, m₁, e₁⟩ := hp
    obtain ⟨D₂, H₂, M₂, h₂, m₂, e₂⟩ := hq
    refine ⟨D₁ + D₂, H₁ * M₂ + H₂ * M₁, M₁ * M₂,
      isMultiHomog_add (isMultiHomog_mul h₁ m₂) (by rw [add_comm D₁]; exact isMultiHomog_mul h₂ m₁),
      isMultiHomog_mul m₁ m₂, fun L _ w hw => ?_⟩
    obtain ⟨n₁, f₁⟩ := e₁ L w hw
    obtain ⟨n₂, f₂⟩ := e₂ L w hw
    refine ⟨by rw [map_mul]; exact mul_ne_zero n₁ n₂, ?_⟩
    simp only [map_add, map_mul, f₁, f₂]
    ring
  | mul_X p i hp =>
    obtain ⟨D, H, M, h, m, e⟩ := hp
    have hX₁ : IsMultiHomog (X i : MRing ι) (Pi.single i.1 1 : K → ℕ) := homog_X i
    have hX₂ : IsMultiHomog (X ⟨i.1, c i.1⟩ : MRing ι) (Pi.single i.1 1 : K → ℕ) :=
      homog_X (⟨i.1, c i.1⟩ : Σ k, ι k)
    have hH := isMultiHomog_mul h hX₁
    have hM := isMultiHomog_mul m hX₂
    refine ⟨_, _, _, hH, hM, fun L _ w hw => ?_⟩
    obtain ⟨n, f⟩ := e L w hw
    have hc := hw i.1
    refine ⟨by rw [map_mul, aeval_X]; exact mul_ne_zero n hc, ?_⟩
    simp only [map_mul, aeval_X, f]
    field_simp

variable {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem aeval_eq_zero {P : MRing ι} {d : K → ℕ} (hz : z ∈ mcPts (mCoordIdeal y)) (hP : IsMultiHomog P d)
    (h0 : aeval y P = 0) : aeval z P = 0 := by
  rw [← evC_eq_aeval]
  exact hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hP h0)

theorem chart_ne {k : K} {i : ι k} (hz : z ∈ mcPts (mCoordIdeal y)) (h : z ⟨k, i⟩ ≠ 0) : y ⟨k, i⟩ ≠ 0 := by
  classical
  intro h0
  apply h
  have := aeval_eq_zero hz (homog_X (⟨k, i⟩ : Σ k, ι k)) (by rw [aeval_X]; exact h0)
  simpa using this

theorem chart_ker (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) {G : MRing ι} (h0 : aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = 0) :
    aeval (fun p => z p / z ⟨p.1, c p.1⟩) G = 0 := by
  obtain ⟨D, H, M, h, m, e⟩ := exists_form c G
  obtain ⟨-, fy⟩ := e Ω y hy
  obtain ⟨nz, fz⟩ := e ℂ z hc
  rw [h0, mul_zero] at fy
  have := aeval_eq_zero hz h fy
  rw [fz] at this
  exact (mul_eq_zero.mp this).resolve_left nz

theorem exists_intHom (φ : F →+* Ω) (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hG : ∀ a : 𝓞 F, ∃ G : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F)) :
    ∃ τ : 𝓞 F →+* ℂ, ∀ (a : 𝓞 F) (G : MRing ι), aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F) →
      τ a = aeval (fun p => z p / z ⟨p.1, c p.1⟩) G := by
  set v : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩ with hv
  set u : (Σ k, ι k) → ℂ := fun p => z p / z ⟨p.1, c p.1⟩ with hu
  let A : MRing ι →ₐ[ℤ] Ω := aeval v
  let ψ : MRing ι →+* A.range := (A.rangeRestrict : MRing ι →+* A.range)
  let ψ' : MRing ι →+* ℂ := ((aeval u : MRing ι →ₐ[ℤ] ℂ) : MRing ι →+* ℂ)
  have hs : Function.Surjective ψ := A.rangeRestrict_surjective
  have hker : RingHom.ker ψ ≤ RingHom.ker ψ' := by
    intro G hGk
    rw [RingHom.mem_ker] at hGk ⊢
    have h1 : aeval v G = 0 := congrArg Subtype.val hGk
    exact chart_ker hz hc hy h1
  let l : A.range →+* ℂ := RingHom.liftOfSurjective ψ hs ⟨ψ', hker⟩
  have hl : ∀ G, l (ψ G) = ψ' G := fun G =>
    RingHom.liftOfRightInverse_comp_apply ψ _ _ ⟨ψ', hker⟩ G
  let ρ : 𝓞 F →+* A.range := (φ.comp (algebraMap (𝓞 F) F)).codRestrict A.range (fun a => by
    obtain ⟨G, hG'⟩ := hG a
    exact ⟨G, hG'⟩)
  refine ⟨l.comp ρ, fun a G h => ?_⟩
  have : ρ a = ψ G := Subtype.ext h.symm
  rw [RingHom.comp_apply, this, hl]
  rfl

theorem intHom_injective (τ : 𝓞 F →+* ℂ) : Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

end OverUnique

open OverUnique GroundTheory.Heights₂.Heights.LowerBoundFree in

theorem existsUnique_ptOver (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (hO : OverInt y φ) :
    ∀ z ∈ mcPts (mCoordIdeal y), ∃! σ : F →+* ℂ, PtOver y φ σ z := by
  classical
  intro z hz
  choose c hc using hz.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => chart_ne hz (hc k)
  have hG : ∀ a : 𝓞 F, ∃ G : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F) := by
    intro a
    have h := hO.2 c hy a
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval] at h
    exact h
  obtain ⟨τ, hτ⟩ := exists_intHom φ hz hc hy hG
  have hinj := intHom_injective τ
  let σ : F →+* ℂ := IsFractionRing.lift hinj
  have hσ : ∀ a : 𝓞 F, σ (a : F) = τ a := fun a => IsFractionRing.lift_algebraMap hinj a
  refine ⟨σ, ⟨hz, fun a d g h hg hh he => ?_⟩, fun σ' hσ' => ?_⟩
  · obtain ⟨a₁, a₂, ha₂, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    have ha₂' : algebraMap (𝓞 F) F a₂ ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero ha₂
    obtain ⟨G₁, e₁⟩ := hG a₁
    obtain ⟨G₂, e₂⟩ := hG a₂
    obtain ⟨D₁, H₁, M₁, h₁, m₁, f₁⟩ := exists_form c G₁
    obtain ⟨D₂, H₂, M₂, h₂, m₂, f₂⟩ := exists_form c G₂
    obtain ⟨ny₁, y₁⟩ := f₁ Ω y hy
    obtain ⟨ny₂, y₂⟩ := f₂ Ω y hy
    obtain ⟨nz₁, z₁⟩ := f₁ ℂ z hc
    obtain ⟨nz₂, z₂⟩ := f₂ ℂ z hc
    have hP : IsMultiHomog (H₂ * M₁ * g - H₁ * M₂ * h) (D₁ + D₂ + d) := by
      refine homog_sub ?_ (isMultiHomog_mul (isMultiHomog_mul h₁ m₂) hh)
      rw [add_comm D₁]
      exact isMultiHomog_mul (isMultiHomog_mul h₂ m₁) hg
    have h0 : aeval y (H₂ * M₁ * g - H₁ * M₂ * h) = 0 := by
      have hφ : φ (algebraMap (𝓞 F) F a₂) ≠ 0 := by simpa using ha₂'
      simp only [map_sub, map_mul, y₁, y₂, he, e₁, e₂]
      rw [map_div₀]
      field_simp
      ring
    have h1 := aeval_eq_zero hz hP h0
    simp only [map_sub, map_mul, z₁, z₂, ← hτ a₁ G₁ e₁, ← hτ a₂ G₂ e₂, ← evC_eq_aeval z g,
      ← evC_eq_aeval z h, ← hσ] at h1
    have hs₂ : σ (algebraMap (𝓞 F) F a₂) ≠ 0 := by simpa using ha₂'
    rw [map_div₀]
    have hM : aeval z M₁ * aeval z M₂ ≠ 0 := mul_ne_zero nz₁ nz₂
    have h2 : σ (algebraMap (𝓞 F) F a₂) * evC z g = σ (algebraMap (𝓞 F) F a₁) * evC z h := by
      apply mul_left_cancel₀ hM
      linear_combination h1
    field_simp
    linear_combination h2
  · refine RingHom.ext fun a => ?_
    have key : ∀ a : 𝓞 F, σ' (a : F) = σ (a : F) := by
      intro a
      obtain ⟨G, e⟩ := hG a
      obtain ⟨D, H, M, h, m, f⟩ := exists_form c G
      obtain ⟨-, fy⟩ := f Ω y hy
      obtain ⟨nz, fz⟩ := f ℂ z hc
      have hy' : aeval y H = φ (a : F) * aeval y M := by rw [fy, e, mul_comm]
      have h1 := hσ'.2 (a : F) D H M h m hy'
      rw [evC_eq_aeval, evC_eq_aeval, fz] at h1
      rw [hσ, hτ a G e]
      have := mul_left_cancel₀ nz (h1.trans (mul_comm _ _))
      exact this.symm
    obtain ⟨a₁, a₂, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    rw [map_div₀, map_div₀]
    exact congrArg₂ _ (key a₁) (key a₂)

end GlobalTheory.CompanionTheory.Ar.Flat
