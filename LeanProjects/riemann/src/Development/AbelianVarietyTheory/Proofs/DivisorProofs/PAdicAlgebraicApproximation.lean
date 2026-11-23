import Mathlib
open Polynomial Topology

namespace GlobalTheory.HypersurfaceApprox

theorem continuous_mvAeval {K : Type*} [CommRing K] {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Algebra K R] {d : ℕ} (c : MvPolynomial (Fin d) K) :
    Continuous (fun y : Fin d → R => MvPolynomial.aeval y c) := by
  induction c using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add f g hf hg => simp only [map_add]; exact hf.add hg
  | mul_X f n hf => simp only [map_mul, MvPolynomial.aeval_X]; exact hf.mul (continuous_apply n)

theorem continuous_eval₂_mvAeval {K : Type*} [CommRing K] {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Algebra K R] {d : ℕ}
    (Q : Polynomial (MvPolynomial (Fin d) K)) :
    Continuous (fun yz : (Fin d → R) × R =>
      Polynomial.eval₂ (MvPolynomial.aeval yz.1).toRingHom yz.2 Q) := by
  simp only [Polynomial.eval₂_eq_sum_range]
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((continuous_mvAeval (Q.coeff i)).comp continuous_fst).mul (continuous_snd.pow i)

end GlobalTheory.HypersurfaceApprox

open GlobalTheory.HypersurfaceApprox in

theorem GlobalTheory.exists_approx_point_of_denseRange : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (E : Type) [Field E] [IsAlgClosed E] [Algebra K E] (ι : E →+* ℂ_[p]), DenseRange ι → ∀ [Algebra K ℂ_[p]], ι.comp (algebraMap K E) = algebraMap K ℂ_[p] → ∀ (d m : ℕ) (t : Fin d → ℂ_[p]) (θ : ℂ_[p]) (P : Polynomial (MvPolynomial (Fin d) K)) (Δ : MvPolynomial (Fin d) K) (Q : Fin m → Polynomial (MvPolynomial (Fin d) K)) (η : ℝ), 0 < η → P.Monic → Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ P = 0 → MvPolynomial.aeval t Δ ≠ 0 → ∃ (t' : Fin d → E) (θ' : E), MvPolynomial.aeval t' Δ ≠ 0 ∧ Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' P = 0 ∧ ∀ j, ‖ι (Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j)) / ι (MvPolynomial.aeval t' Δ) - Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) / MvPolynomial.aeval t Δ‖ < η := by
  intro p _ K _ E _ _ _ ι hι _ hc d m t θ P Δ Q η hη hP hθ hΔ
  set n := P.natDegree with hn
  have hcontC := fun c : MvPolynomial (Fin d) K => continuous_mvAeval (R := ℂ_[p]) c
  have hD : ContinuousAt (fun yz : (Fin d → ℂ_[p]) × ℂ_[p] => MvPolynomial.aeval yz.1 Δ) (t, θ) :=
    ((hcontC Δ).comp continuous_fst).continuousAt
  have hR : ∀ᶠ yz in 𝓝 (t, θ), MvPolynomial.aeval yz.1 Δ ≠ 0 ∧ ∀ j,
      ‖Polynomial.eval₂ (MvPolynomial.aeval yz.1).toRingHom yz.2 (Q j) / MvPolynomial.aeval yz.1 Δ
        - Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) / MvPolynomial.aeval t Δ‖ < η := by
    refine (hD.eventually_ne hΔ).and (Filter.eventually_all.2 fun j => ?_)
    have hcj := ((continuous_eval₂_mvAeval (R := ℂ_[p]) (Q j)).continuousAt (x := (t, θ))).div hD hΔ
    filter_upwards [Metric.tendsto_nhds.1 hcj η hη] with yz h
    rwa [dist_eq_norm] at h
  rw [nhds_prod_eq] at hR
  obtain ⟨pa, hpa, pb, hpb, hR⟩ := Filter.eventually_prod_iff.1 hR
  obtain ⟨ε₀, hε₀, hpb⟩ := Metric.eventually_nhds_iff.1 hpb
  have hn0 : n ≠ 0 := by
    intro h0
    have h1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hP h0
    simp [h1] at hθ
  set M := max ‖θ‖ 1 with hMdef
  have hM : 0 < M := lt_max_of_lt_right one_pos
  set ε' : ℝ := (ε₀ / (2 * M)) ^ n / (n + 1) with hε'def
  have hε' : 0 < ε' := by positivity
  have hbound : ((n + 1 : ℝ) * ε') ^ (n : ℝ)⁻¹ * M < ε₀ := by
    have h1 : (n + 1 : ℝ) * ε' = (ε₀ / (2 * M)) ^ n := by
      rw [hε'def]; field_simp
    rw [h1, Real.pow_rpow_inv_natCast (by positivity) hn0]
    have h2 : ε₀ / (2 * M) * M = ε₀ / 2 := by field_simp
    rw [h2]; linarith
  have hcoef : ∀ᶠ y in 𝓝 t, ∀ i ∈ Finset.range (n + 1),
      ‖MvPolynomial.aeval y (P.coeff i) - MvPolynomial.aeval t (P.coeff i)‖ < ε' := by
    rw [Filter.eventually_all_finset]
    intro i _
    filter_upwards [Metric.tendsto_nhds.1 ((hcontC (P.coeff i)).continuousAt (x := t)) ε' hε'] with y h
    rwa [dist_eq_norm] at h
  obtain ⟨r, hr, hU⟩ := Metric.eventually_nhds_iff.1 (hpa.and hcoef)
  have hex : ∀ i, ∃ e : E, dist (ι e) (t i) < r := fun i => by
    obtain ⟨e, he⟩ := hι.exists_dist_lt (t i) hr
    exact ⟨e, by rw [dist_comm]; exact he⟩
  choose t' ht' using hex
  set y : Fin d → ℂ_[p] := ι ∘ t' with hydef
  have hy : dist y t < r := (dist_pi_lt_iff hr).2 ht'
  obtain ⟨hya, hyc⟩ := hU hy
  have hmap : ∀ c : MvPolynomial (Fin d) K, MvPolynomial.aeval y c = ι (MvPolynomial.aeval t' c) := by
    intro c
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, hc]
  have hmapR : ι.comp (MvPolynomial.aeval t').toRingHom = (MvPolynomial.aeval y).toRingHom :=
    RingHom.ext fun c => (hmap c).symm
  set f := P.map (MvPolynomial.aeval t).toRingHom with hfdef
  set g := P.map (MvPolynomial.aeval y).toRingHom with hgdef
  have hfm : f.Monic := hP.map _
  have hgm : g.Monic := hP.map _
  have hfdeg : f.natDegree = n := hP.natDegree_map _
  have hgdeg : g.natDegree = n := hP.natDegree_map _
  have hfa : f.eval θ = 0 := by rw [hfdef, eval_map]; exact hθ
  have hco : ∀ i, ‖g.coeff i - f.coeff i‖ < ε' := by
    intro i
    simp only [hgdef, hfdef, coeff_map]
    by_cases hi : i ≤ n
    · exact hyc i (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]; simpa using hε'
  obtain ⟨b, hb, hθb⟩ := exists_roots_norm_sub_lt_of_norm_coeff_sub_lt hε' hfa hfm hgm
    (hgdeg.trans hfdeg.symm) hco (IsAlgClosed.splits g)
  rw [hfdeg] at hθb
  set g' := P.map (MvPolynomial.aeval t').toRingHom with hg'def
  have hg'g : g'.map ι = g := by rw [hg'def, Polynomial.map_map, hmapR]
  have hg'm : g'.Monic := hP.map _
  rw [← hg'g, (IsAlgClosed.splits g').roots_map_of_injective ι.injective] at hb
  obtain ⟨θ', hθ'r, rfl⟩ := Multiset.mem_map.1 hb
  have hθ'0 : g'.eval θ' = 0 := (mem_roots hg'm.ne_zero).1 hθ'r
  have hpbb : pb (ι θ') := hpb (by rw [dist_comm, dist_eq_norm]; exact hθb.trans hbound)
  obtain ⟨hΔy, hQ⟩ := hR hya hpbb
  refine ⟨t', θ', ?_, ?_, fun j => ?_⟩
  · intro h0; apply hΔy; simp only; rw [hmap, h0, map_zero]
  · rw [← eval_map]; exact hθ'0
  · have h := hQ j
    simp only at h
    rw [hmap Δ, ← hmapR, ← Polynomial.hom_eval₂] at h
    exact h
