import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFieldCmCurvesUnitDiscriminant

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors

namespace GlobalTheory

namespace CMData

variable {K : Type} [Field K] [NumberField K]

theorem exists_periodPair (h2 : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ¬ ComplexEmbedding.IsReal σ) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ x ∈ I.1, z = σ x := by
  obtain ⟨b, hspan⟩ : ∃ b : Module.Basis (Fin 2) ℚ K, ∀ x : K, x ∈ I.1 ↔ x ∈ Submodule.span ℤ (Set.range b) := by
    have hcard := (Module.finrank_eq_card_basis (basisOfFractionalIdeal K I)).symm.trans h2
    refine ⟨(basisOfFractionalIdeal K I).reindex (Fintype.equivFinOfCardEq hcard), fun x => ?_⟩
    rw [Module.Basis.coe_reindex, EquivLike.range_comp, mem_span_basisOfFractionalIdeal]
    exact Iff.rfl
  obtain ⟨a, ha⟩ := CMLattice.exists_im_ne_zero σ hσ
  have hX : (σ (b 0) * starRingEnd ℂ (σ (b 1))).im ≠ 0 := by
    intro h0
    have e := CMLattice.im_mul_conj_eq_det σ b ![1, (a : K)]
    rw [h0, mul_zero] at e
    apply ha
    simpa using e
  have e2 : (σ (b 0) * starRingEnd ℂ (σ (b 1))).im =
      (σ (b 0)).im * (σ (b 1)).re - (σ (b 0)).re * (σ (b 1)).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hind : LinearIndependent ℝ ![σ (b 0), σ (b 1)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      have e1 := congrArg (fun w => (starRingEnd ℂ (σ (b 0)) * w).im) hst
      simp only [Complex.real_smul, mul_add, Complex.add_im, Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, mul_zero,
        Complex.zero_im] at e1
      have hprod : t * ((σ (b 0)).im * (σ (b 1)).re - (σ (b 0)).re * (σ (b 1)).im) = 0 := by
        linear_combination -e1
      rcases mul_eq_zero.mp hprod with h | h
      · exact h
      · exact absurd (e2.trans h) hX
    subst ht
    have h0 : σ (b 0) ≠ 0 := by
      intro h
      apply hX
      rw [h, zero_mul, Complex.zero_im]
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right h0, rfl⟩
  refine ⟨⟨σ (b 0), σ (b 1), hind⟩, fun z => ?_⟩
  show z ∈ Submodule.span ℤ {σ (b 0), σ (b 1)} ↔ _
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m • b 0 + n • b 1, ?_, by simp⟩
    rw [hspan]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · rintro ⟨x, hx, rfl⟩
    rw [hspan, Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, rfl⟩ := hx
    refine ⟨c 0, c 1, ?_⟩
    simp [Fin.sum_univ_two]

theorem exists_mul_of_invariants {L L' : PeriodPair} {c₄ Δ : ℂ}
    (h : c₄ ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = 1728 * L.g₂ ^ 3 * Δ)
    (h₄ : c₄ = 12 * L'.g₂) (hΔ : Δ = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ L'.lattice ↔ ∃ w ∈ L.lattice, z = c * w := by
  subst h₄ hΔ
  exact (lattice_determined_by_invariants L L').2 (by linear_combination (-1 / 1728 : ℂ) * h)

theorem exists_field (h2 : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ¬ ComplexEmbedding.IsReal σ) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ a, σ a ∈ M) ∧
      ∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∃ W : WeierstrassCurve (𝓞 M), IsUnit W.Δ ∧
        ∀ L' : PeriodPair,
          ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) W.c₄ = 12 * L'.g₂ →
          ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) W.Δ = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 →
          ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ L'.lattice ↔ ∃ x ∈ I.1, z = c * σ x := by
  obtain ⟨M, hfin, hσM, hF⟩ := exists_field_cm_curves_unit_discriminant K h2 σ hσ
  refine ⟨M, hfin, hσM, fun I => ?_⟩
  obtain ⟨L, hL⟩ := exists_periodPair h2 σ hσ I
  have hstab : ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice := by
    intro a z hz
    obtain ⟨x, hx, rfl⟩ := (hL z).1 hz
    refine (hL _).2 ⟨(a : K) * x, ?_, by rw [map_mul]⟩
    have hax := Submodule.smul_mem (I.1 : Submodule (𝓞 K) K) a hx
    simpa [Algebra.smul_def] using hax
  obtain ⟨W, hW, hj⟩ := hF L hstab
  refine ⟨W, hW, fun L' h4 hD => ?_⟩
  obtain ⟨c, hc, hc'⟩ := exists_mul_of_invariants hj h4 hD
  refine ⟨c, hc, fun z => ?_⟩
  rw [hc' z]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (hL w).1 hw
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨σ x, (hL _).2 ⟨x, hx, rfl⟩, rfl⟩

theorem mem_inv_iff (𝔟 : (Ideal (𝓞 K))⁰) (x : K) :
    x ∈ ((FractionalIdeal.mk0 K 𝔟)⁻¹).1 ↔ ∀ b ∈ (𝔟 : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K)) := by
  have hne : ((FractionalIdeal.mk0 K 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    Units.ne_zero _
  rw [Units.val_inv_eq_inv_val, FractionalIdeal.mem_inv_iff hne, FractionalIdeal.coe_mk0]
  constructor
  · intro h b hb
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩))
    have hint : IsIntegral ℤ (algebraMap (𝓞 K) K a) := RingOfIntegers.isIntegral_coe a
    rw [ha] at hint
    exact hint
  · intro h y hy
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨_, h b hb⟩, rfl⟩

end CMData

open CMData in

theorem exists_cm_curves_of_weierstrass_curves :
    (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) ∧ ∀ s : R →+* ℂ, s W.c₄ = 12 * (Lf s).g₂ ∧ s W.c₆ = 216 * (Lf s).g₃ ∧ s W.Δ = (Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) → ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (κ : K →+* M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞 K) → Out.PolAV (Sp (𝓞 M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+* ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀ s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) ∧ ∃ β : ClassGroup (𝓞 K) → ℂ, (∀ C, β C ≠ 0) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → ∀ z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice, β C * σ₀ x * z ∈ (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), ∀ z ∈ (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice, (β C)⁻¹ * σ₀ (y : K) * z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice := by
  intro H K _ _ h2 σ₀ hσ₀ 𝔟
  obtain ⟨M, hfin, hσM, hF⟩ := CMData.exists_field h2 σ₀ hσ₀
  have hNF : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨W₀, hW₀, hF₀⟩ := hF 1
  obtain ⟨P, v, L₀, hP, hP₀⟩ := H (𝓞 M) W₀ hW₀
  obtain ⟨c₀, hc₀, hc₀L⟩ := hF₀ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)))
    (hP₀ _).1 (hP₀ _).2.2
  have hL0 : ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔
      ∃ a : 𝓞 K, z = c₀ * σ₀ (a : K) := by
    intro z
    rw [hc₀L z, Units.val_one]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : K), (FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩, rfl⟩
  choose W hW hWL using fun C : ClassGroup (𝓞 K) => hF (FractionalIdeal.mk0 K (𝔟 C))⁻¹
  choose Q t L hQ hQL using fun C => H (𝓞 M) (W C) (hW C)
  choose c hc hcL using fun C => hWL C (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)))
    (hQL C _).1 (hQL C _).2.2
  refine ⟨M, hNF, σ₀.codRestrict M hσM, P, v, L₀, Q, t, L, fun C => (hW C).unit, fun a => rfl, hP, hQ,
    fun C s => ?_, ⟨c₀, hc₀, hL0⟩, fun C => c C / c₀, fun C => div_ne_zero (hc C) hc₀, ?_, ?_⟩
  · rw [IsUnit.unit_spec]
    exact ((hQL C s).2.2).symm
  · intro C x hx z hz
    obtain ⟨a, rfl⟩ := (hL0 z).1 hz
    have hxI := (CMData.mem_inv_iff (𝔟 C) x).2 hx
    rw [hcL C]
    refine ⟨x * (a : K), ?_, ?_⟩
    · have hax := Submodule.smul_mem (((FractionalIdeal.mk0 K (𝔟 C))⁻¹).1 : Submodule (𝓞 K) K) a hxI
      simpa [Algebra.smul_def, mul_comm] using hax
    · rw [map_mul]
      field_simp
  · intro C y hy z hz
    obtain ⟨x', hx', rfl⟩ := (hcL C z).1 hz
    have hint := (CMData.mem_inv_iff (𝔟 C) x').1 hx' y hy
    rw [hL0]
    refine ⟨⟨x' * (y : K), hint⟩, ?_⟩
    show _ = c₀ * σ₀ (x' * (y : K))
    have hcC := hc C
    rw [map_mul]
    field_simp

end GlobalTheory
