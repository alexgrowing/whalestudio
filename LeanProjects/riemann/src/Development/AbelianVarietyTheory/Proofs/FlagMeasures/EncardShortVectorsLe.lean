import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass

theorem trace_cast_eq_sum_re {K : Type} [Field K] [NumberField K] (z : K) :
    ((Algebra.trace ℚ K z : ℚ) : ℝ) = ∑ τ : K →ₐ[ℚ] ℂ, (τ z).re := by
  have key := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := z)
  have hre := congrArg Complex.re key
  rw [Complex.re_sum] at hre
  rw [← hre]
  simp

theorem card_algHom_eq_two_mul_fDeg {K : Type} [Field K] [NumberField K] (hK : IsTotallyComplex K) :
    Module.finrank ℚ K = 2 * fDeg K := by
  have := hK
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

theorem finrank_le_trace_of_integral {K : Type} [Field K] [NumberField K] (z : 𝓞 K)
    (hre : ∀ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).im = 0) (hpos : ∀ τ : K →ₐ[ℚ] ℂ, 0 < (τ (z : K)).re) :
    (Module.finrank ℚ K : ℝ) ≤ ∑ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re := by
  classical
  have hprod : ((∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re : ℝ) : ℂ) = ∏ τ : K →ₐ[ℚ] ℂ, τ (z : K) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact Complex.ext (by simp) (by simp [hre τ])
  have hnorm := Algebra.norm_eq_prod_embeddings (K := ℚ) (E := ℂ) (z : K)
  have h2 : ((((Algebra.norm ℤ z : ℤ) : ℚ) : ℝ) : ℂ) = ((∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re : ℝ) : ℂ) := by
    rw [hprod, ← hnorm, Algebra.coe_norm_int]
    simp
  have hN : (((Algebra.norm ℤ z : ℤ) : ℚ) : ℝ) = ∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re :=
    Complex.ofReal_injective h2
  have hP : (0 : ℝ) < ∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re := Finset.prod_pos fun τ _ => hpos τ
  have hN1 : (1 : ℝ) ≤ ∏ τ : K →ₐ[ℚ] ℂ, (τ (z : K)).re := by
    rw [← hN] at hP ⊢
    have h3 : (0 : ℤ) < Algebra.norm ℤ z := by exact_mod_cast hP
    have h4 : (1 : ℤ) ≤ Algebra.norm ℤ z := h3
    exact_mod_cast h4
  have hL := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.traceLower (K →ₐ[ℚ] ℂ) (fun τ => (τ (z : K)).re)
    (fun τ => (hpos τ).le) hN1
  simpa only [AlgHom.card] using hL

theorem finrank_le_of_span_range {K V E : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup E] [Module ℝ E] (ι : V →+ E)
    (hs : Submodule.span ℝ (Set.range ι) = ⊤) :
    Module.finrank ℝ E ≤ Module.finrank ℚ K * Module.finrank K V := by
  classical
  let bV := Module.finBasis K V
  let bK := Module.finBasis ℚ K
  let g : Fin (Module.finrank ℚ K) × Fin (Module.finrank K V) → E := fun p => ι (bK p.1 • bV p.2)
  have hsub : Set.range ι ⊆ Submodule.span ℝ (Set.range g) := by
    rintro _ ⟨v, rfl⟩
    rw [← bV.sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← bK.sum_repr (bV.repr v j), Finset.sum_smul, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Rat.smul_def, mul_smul, map_ratCast_smul ι K ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hEq : Submodule.span ℝ (Set.range g) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hs]
    exact Submodule.span_le.mpr hsub
  have hc := finrank_range_le_card (R := ℝ) g
  rw [Set.finrank, hEq, finrank_top] at hc
  simpa [Fintype.card_prod] using hc

theorem encard_shortVectors_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → ∀ B : ℝ, 0 ≤ B → (({x : V | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B}.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + 2 * Real.sqrt B) ^ (2 * Module.finrank K V * fDeg K)) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hPD L hL B hB
  classical
  have hK' := hK
  unfold Formalism.HermitianLatticesTheory.IsCMUnram at hK'
  obtain ⟨hTC, hCM, -⟩ := hK'
  have hPD' := hPD
  unfold PD at hPD'
  have hL' := hL
  unfold IsIntLat at hL'
  have hInt := hL'.2
  unfold Formalism.HermitianLatticesTheory.IsIntegralLat at hInt

  have hreal : ∀ (x : V) (τ : K →+* ℂ), (τ (h x x)).im = 0 := by
    intro x τ
    have e1 := hCM τ (h x x)
    have e2 : star (h x x) = h x x := by
      have := hs.eq x x
      simpa [starRingEnd_apply] using this
    rw [e2] at e1
    exact Complex.conj_eq_iff_im.mp e1.symm
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K := by simp
  have hne : Nonempty (K →ₐ[ℚ] ℂ) :=
    Fintype.card_pos_iff.mp (hcard ▸ Module.finrank_pos)

  have htr_pos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
    intro x hx
    have e := trace_cast_eq_sum_re (h x x)
    have hs' : (0 : ℝ) < ∑ τ : K →ₐ[ℚ] ℂ, (τ (h x x)).re :=
      Finset.sum_pos (fun τ _ => hPD' τ.toRingHom x hx) Finset.univ_nonempty
    rw [← e] at hs'
    exact_mod_cast hs'
  obtain ⟨N, ι, hinner, -, -⟩ := Formalism.HermitianLatticesTheory.final_traceReal K V h hs htr_pos
  have hnorm : ∀ x : V, ‖ι x‖ ^ 2 = ∑ τ : K →ₐ[ℚ] ℂ, (τ (h x x)).re := by
    intro x
    rw [← real_inner_self_eq_norm_sq, hinner, trace_cast_eq_sum_re]

  have hlong : ∀ x ∈ L, x ≠ 0 → (Module.finrank ℚ K : ℝ) ≤ ‖ι x‖ ^ 2 := by
    intro x hx hx0
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hInt x hx x hx)
    have hr' : ((r : 𝓞 K) : K) = h x x := hr
    rw [hnorm, ← hr']
    refine finrank_le_trace_of_integral r (fun τ => ?_) (fun τ => ?_)
    · rw [hr']; exact hreal x τ.toRingHom
    · rw [hr']; exact hPD' τ.toRingHom x hx0

  have hshort : ∀ x : V, (∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B) →
      ‖ι x‖ ^ 2 ≤ (Module.finrank ℚ K : ℝ) * B := by
    intro x hx
    rw [hnorm]
    calc ∑ τ : K →ₐ[ℚ] ℂ, (τ (h x x)).re ≤ ∑ _τ : K →ₐ[ℚ] ℂ, B :=
          Finset.sum_le_sum fun τ _ => hx τ.toRingHom
      _ = (Module.finrank ℚ K : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]

  have hinj : Function.Injective ι := by
    intro a b hab
    by_contra hne'
    have hd : a - b ≠ 0 := sub_ne_zero.mpr hne'
    have h0 : ι (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hp := htr_pos (a - b) hd
    have hq : ‖ι (a - b)‖ ^ 2 = ((Algebra.trace ℚ K (h (a - b) (a - b)) : ℚ) : ℝ) := by
      rw [← real_inner_self_eq_norm_sq, hinner]
    rw [h0, norm_zero] at hq
    have : ((Algebra.trace ℚ K (h (a - b) (a - b)) : ℚ) : ℝ) = 0 := by rw [← hq]; ring
    have : Algebra.trace ℚ K (h (a - b) (a - b)) = 0 := by exact_mod_cast this
    exact absurd this hp.ne'

  set E := EuclideanSpace ℝ (Fin N)
  set Es : Submodule ℝ E := Submodule.span ℝ (Set.range ι) with hEs
  let ι' : V →+ Es := AddMonoidHom.mk' (fun x => ⟨ι x, Submodule.subset_span ⟨x, rfl⟩⟩)
    (fun a b => Subtype.ext (map_add ι a b))
  have hι' : ∀ x, ((ι' x : Es) : E) = ι x := fun x => rfl
  have hspan : Submodule.span ℝ (Set.range ι') = ⊤ := by
    have e : Set.range ι' = ((↑) : Es → E) ⁻¹' (Set.range ι) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, Subtype.ext hx⟩
    rw [e]
    exact Submodule.span_span_coe_preimage
  have hdim : Module.finrank ℝ Es ≤ 2 * Module.finrank K V * fDeg K := by
    have h1 := finrank_le_of_span_range (K := K) (V := V) ι' hspan
    rw [card_algHom_eq_two_mul_fDeg hTC] at h1
    calc Module.finrank ℝ Es ≤ 2 * fDeg K * Module.finrank K V := h1
      _ = 2 * Module.finrank K V * fDeg K := by ring

  set D : ℝ := (Module.finrank ℚ K : ℝ) with hD
  have hD0 : 0 < D := by
    rw [hD]; exact_mod_cast Module.finrank_pos
  set Λ : AddSubgroup Es := L.toAddSubgroup.map ι'
  have hl0 : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hmin : ∀ y ∈ Λ, y ≠ 0 → Real.sqrt D ≤ ‖y‖ := by
    intro y hy hy0
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hy
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hy0 (map_zero ι')
    have e : ‖ι' x‖ = ‖ι x‖ := rfl
    rw [e]
    calc Real.sqrt D ≤ Real.sqrt (‖ι x‖ ^ 2) := Real.sqrt_le_sqrt (hlong x hx hx0)
      _ = ‖ι x‖ := Real.sqrt_sq (norm_nonneg _)
  obtain ⟨hfin, hcount⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.packing Es Λ (Real.sqrt D) (Real.sqrt (D * B))
    hl0 (Real.sqrt_nonneg _) hmin
  have hratio : 2 * Real.sqrt (D * B) / Real.sqrt D = 2 * Real.sqrt B := by
    rw [Real.sqrt_mul hD0.le, mul_div_assoc, mul_div_cancel_left₀ _ hl0.ne']
  rw [hratio] at hcount
  have hbase : (1 : ℝ) ≤ 1 + 2 * Real.sqrt B := by
    have := Real.sqrt_nonneg B
    linarith
  have hpow := pow_le_pow_right₀ hbase hdim

  have hmaps : Set.MapsTo ι' {x | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B}
      {y : Es | y ∈ Λ ∧ ‖y‖ ≤ Real.sqrt (D * B)} := by
    rintro x ⟨hx, hxB⟩
    refine ⟨AddSubgroup.mem_map_of_mem ι' hx, ?_⟩
    have e : ‖ι' x‖ = ‖ι x‖ := rfl
    rw [e]
    have := Real.abs_le_sqrt (hshort x hxB)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hinj' : Set.InjOn ι' {x | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B} := by
    intro a _ b _ hab
    apply hinj
    rw [← hι' a, ← hι' b, hab]
  have hle := Set.encard_le_encard_of_injOn hmaps hinj'
  rw [← hfin.cast_ncard_eq] at hle
  calc ((({x | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B}.encard : ℕ∞) : ℝ≥0∞))
      ≤ (((({y : Es | y ∈ Λ ∧ ‖y‖ ≤ Real.sqrt (D * B)}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞) := by
        exact_mod_cast hle
    _ = ENNReal.ofReal (({y : Es | y ∈ Λ ∧ ‖y‖ ≤ Real.sqrt (D * B)}.ncard : ℝ)) := by
        simp
    _ ≤ ENNReal.ofReal ((1 + 2 * Real.sqrt B) ^ (2 * Module.finrank K V * fDeg K)) :=
        ENNReal.ofReal_le_ofReal (hcount.trans hpow)

end GlobalTheory.Mass
