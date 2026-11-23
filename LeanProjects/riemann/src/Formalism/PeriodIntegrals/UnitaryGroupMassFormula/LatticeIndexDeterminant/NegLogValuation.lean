import Mathlib
import Formalism.PeriodIntegrals.LatIdxDet
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange

open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors

noncomputable section

namespace PI.LatIdxDetW

section Gen

variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']

theorem locLen_congr (p : Ideal R) [p.IsPrime] {X X' Y Y' : Submodule R W}
    (hX : localization₂ p X = localization₂ p X') (hY : localization₂ p Y = localization₂ p Y') : locLen p X Y = locLen p X' Y' := by
  unfold locLen
  rw [hX, hY]

private theorem mem_localization_iff_exists_smul_mem (p : Ideal R) [p.IsPrime] (L : Submodule R W) (x : W) :
    x ∈ localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl

private theorem localization_inf' (p : Ideal R) [p.IsPrime] (X Y : Submodule R W) :
    localization₂ p (X ⊓ Y) = localization₂ p X ⊓ localization₂ p Y := by
  ext x
  rw [Submodule.mem_inf, mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨⟨s, hs, (Submodule.mem_inf.1 hx).1⟩, ⟨s, hs, (Submodule.mem_inf.1 hx).2⟩⟩
  · rintro ⟨⟨s, hs, hx⟩, ⟨t, ht, hy⟩⟩
    refine ⟨s * t, p.primeCompl.mul_mem hs ht, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
    · rw [mul_comm, mul_smul]
      exact X.smul_mem t hx
    · rw [mul_smul]
      exact Y.smul_mem s hy

theorem lidx_congr (p : Ideal R) [p.IsPrime] {A A' B B' : Submodule R W}
    (hA : localization₂ p A = localization₂ p A') (hB : localization₂ p B = localization₂ p B') : lidx p A B = lidx p A' B' := by
  unfold lidx
  have hAB : localization₂ p (A ⊓ B) = localization₂ p (A' ⊓ B') := by
    rw [localization_inf', localization_inf', hA, hB]
  rw [locLen_congr p hA hAB, locLen_congr p hB hAB]

theorem lidx_antisymm (p : Ideal R) [p.IsPrime] (A B : Submodule R W) :
    lidx p A B = - lidx p B A := by
  unfold lidx
  rw [inf_comm B A]
  ring

theorem localization_map₂ (p : Ideal R) [p.IsPrime] (φ : W ≃ₗ[R] W') (L : Submodule R W) :
    localization₂ p (L.map (φ : W →ₗ[R] W')) = (localization₂ p L).map (φ : W →ₗ[R] W') := by
  ext x
  simp only [mem_localization_iff_exists_smul_mem, Submodule.mem_map_equiv, LinearEquiv.map_smul]

theorem length_map (φ : W ≃ₗ[R] W') (X Y : Submodule R W) :
    Module.length R (↥(X.map (φ : W →ₗ[R] W')) ⧸
        (Y.map (φ : W →ₗ[R] W')).comap (X.map (φ : W →ₗ[R] W')).subtype) =
      Module.length R (↥X ⧸ Y.comap X.subtype) := by
  have e : (↥X ⧸ Y.comap X.subtype) ≃ₗ[R] (↥(X.map (φ : W →ₗ[R] W')) ⧸
      (Y.map (φ : W →ₗ[R] W')).comap (X.map (φ : W →ₗ[R] W')).subtype) :=
    Submodule.Quotient.equiv _ _ (φ.submoduleMap X) (by
      ext ⟨y, hy⟩
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
      constructor
      · rintro ⟨⟨x, hx⟩, hxY, hxy⟩
        refine ⟨x, hxY, ?_⟩
        simpa using congrArg Subtype.val hxy
      · rintro ⟨x, hxY, hxy⟩
        obtain ⟨x', hx', hx'y⟩ := hy
        have hxx : x = x' := φ.injective (hxy.trans hx'y.symm)
        refine ⟨⟨x, hxx ▸ hx'⟩, hxY, ?_⟩
        apply Subtype.ext
        simpa using hxy)
  exact e.length_eq.symm

theorem locLen_map (p : Ideal R) [p.IsPrime] (φ : W ≃ₗ[R] W') (X Y : Submodule R W) :
    locLen p (X.map (φ : W →ₗ[R] W')) (Y.map (φ : W →ₗ[R] W')) = locLen p X Y := by
  unfold locLen
  rw [localization_map₂, localization_map₂, length_map]

theorem lidx_map (p : Ideal R) [p.IsPrime] (φ : W ≃ₗ[R] W') (A B : Submodule R W) :
    lidx p (A.map (φ : W →ₗ[R] W')) (B.map (φ : W →ₗ[R] W')) = lidx p A B := by
  unfold lidx
  rw [← Submodule.map_inf _ φ.injective, locLen_map, locLen_map]

end Gen

section Lat

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

private theorem neg_log_int_lemma_3 (w : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    - WithZero.log (w.valuation K (algebraMap R K r)) =
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton R⁰ (algebraMap R K r)) := by
  rw [w.valuation_of_algebraMap, w.intValuation_if_neg hr, WithZero.log_exp,
    ← FractionalIdeal.coeIdeal_span_singleton]
  have hJ : Ideal.span {r} ≠ 0 := by simpa using hr
  rw [FractionalIdeal.count_coe K w hJ]
  simp

theorem neg_log_valuation (w : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    - WithZero.log (w.valuation K x) =
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton R⁰ x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hB : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hb0
  have hA : algebraMap R K a ≠ 0 := by
    intro h
    apply hx
    rw [h, zero_div]
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hA (map_zero _)
  have e1 := neg_log_int_lemma_3 (K := K) w ha0
  have e2 := neg_log_int_lemma_3 (K := K) w hb0
  have hc := Formalism.DivisionValues.idxChange_cnt_mul (K := K) w hA (inv_ne_zero hB)
  have hc2 := Formalism.DivisionValues.idxChange_cnt_mul (K := K) w hB (inv_ne_zero hB)
  rw [mul_inv_cancel₀ hB, Formalism.DivisionValues.idxChange_cnt_one] at hc2
  have vA : w.valuation K (algebraMap R K a) ≠ 0 := (w.valuation K).ne_zero_iff.2 hA
  have vB : w.valuation K (algebraMap R K b) ≠ 0 := (w.valuation K).ne_zero_iff.2 hB
  rw [div_eq_mul_inv, hc, map_mul, map_inv₀, WithZero.log_mul vA (inv_ne_zero vB), WithZero.log_inv]
  linarith

variable [FiniteDimensional K V]

theorem lidx_free (w : HeightOneSpectrum R) {d : ℕ} (b : Basis (Fin d) K V) (γ : V ≃ₗ[K] V) :
    lidx w.asIdeal (Submodule.span R (Set.range b))
      ((Submodule.span R (Set.range b)).map ((γ.restrictScalars R : V ≃ₗ[R] V) : V →ₗ[R] V)) =
      FractionalIdeal.count K w
        (FractionalIdeal.spanSingleton R⁰ (LinearMap.det (γ : V →ₗ[K] V))) := by
  classical
  let φ : V ≃ₗ[R] (Fin d → K) := b.equivFun.restrictScalars R
  let M := LinearMap.toMatrix b b (γ : V →ₗ[K] V)
  let e : Fin d → Fin d → K := fun i => φ (b i)
  have he : LinearIndependent K e := b.linearIndependent.map' b.equivFun.toLinearMap b.equivFun.ker
  have hact : Formalism.DivisionValues.idxChangeAct e M = fun i => φ (γ (b i)) := by
    funext i j
    simp [Formalism.DivisionValues.idxChangeAct, e, φ, M, LinearMap.toMatrix_apply, Finset.sum_apply, Finsupp.single_apply]
  have h1 : (Submodule.span R (Set.range b)).map (φ : V →ₗ[R] (Fin d → K)) =
      Submodule.span R (Set.range e) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have h2 : ((Submodule.span R (Set.range b)).map ((γ.restrictScalars R : V ≃ₗ[R] V) : V →ₗ[R] V)).map
      (φ : V →ₗ[R] (Fin d → K)) = Submodule.span R (Set.range (Formalism.DivisionValues.idxChangeAct e M)) := by
    rw [hact, Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
    rfl
  have hdet : M.det ≠ 0 := by
    rw [LinearMap.det_toMatrix]
    exact (LinearEquiv.isUnit_det' γ).ne_zero
  rw [← lidx_map w.asIdeal φ, h1, h2, Formalism.DivisionValues.indexChange_of_det_ne_zero w M hdet e he, LinearMap.det_toMatrix]

end Lat

end PI.LatIdxDetW
