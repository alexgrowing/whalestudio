import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicityDifferentEq

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

open IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.HTConst

theorem mem_of_pow_eq_one {K : Type} [Field K] (W : ValuationSubring K) {z : K} {N : ℕ} (hN : 0 < N) (h : z ^ N = 1) :
    z ∈ W := by
  rcases W.mem_or_inv_mem z with h1 | h1
  · exact h1
  · obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    have e : z = (z⁻¹) ^ k := by
      rw [inv_pow]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ']; exact h)
    rw [e]
    exact pow_mem h1 _

theorem exists_intValuation_eq {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) {x : R}
    (hx : x ≠ 0) : ∃ n : ℕ, w.intValuation x = WithZero.exp (-(n : ℤ)) :=
  ⟨_, w.intValuation_if_neg hx⟩

theorem exists_mul_eq_mul {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) {x y : R}
    (hx : x ≠ 0) (h : w.intValuation x = w.intValuation y) :
    ∃ u v, u ∉ w.asIdeal ∧ v ∉ w.asIdeal ∧ u * y = v * x := by
  obtain ⟨n, hn⟩ := exists_intValuation_eq w hx
  have hx1 : x ∈ w.asIdeal ^ n := (w.intValuation_le_pow_iff_mem x n).1 hn.le
  have hy1 : y ∈ w.asIdeal ^ n := (w.intValuation_le_pow_iff_mem y n).1 (h ▸ hn.le)
  have hx2 : x ∉ w.asIdeal ^ (n + 1) := fun hc => by
    have := (w.intValuation_le_pow_iff_mem x (n + 1)).2 hc
    rw [hn, WithZero.exp_le_exp] at this
    push_cast at this
    omega
  obtain ⟨A, hA⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hx1)
  have hAw : ¬ A ≤ w.asIdeal := fun hc => hx2 <| by
    have h1 : x ∈ w.asIdeal ^ n * A := hA ▸ Ideal.mem_span_singleton_self x
    rw [pow_succ]
    exact Ideal.mul_mono_right hc h1
  obtain ⟨u, huA, huw⟩ := SetLike.not_le_iff_exists.1 hAw
  have h2 : u * y ∈ Ideal.span {x} := by
    rw [hA, mul_comm u]
    exact Ideal.mul_mem_mul hy1 huA
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 h2
  refine ⟨u, v, huw, fun hc => ?_, hv.symm ▸ rfl⟩
  have hu1 : w.intValuation u = 1 := HeightOneSpectrum.intValuation_eq_one_iff.2 huw
  have h3 : w.intValuation v * w.intValuation x = w.intValuation x := by
    rw [← map_mul, hv, map_mul, hu1, _root_.one_mul, h]
  have hv1 : w.intValuation v = 1 := mul_right_cancel₀ (w.intValuation_ne_zero x hx) (by rw [h3, _root_.one_mul])
  exact (HeightOneSpectrum.intValuation_eq_one_iff.1 hv1) hc

theorem norm_of_isUnit {C : Type} [NormedField C] [IsUltrametricDist C] {t : ↥(intO C)} (h : IsUnit t) :
    ‖(t : C)‖ = 1 := by
  obtain ⟨s, hs⟩ := h.exists_right_inv
  have h1 : ‖(t : C)‖ ≤ 1 := t.2
  have h2 : ‖(s : C)‖ ≤ 1 := s.2
  have h3 : ‖(t : C)‖ * ‖(s : C)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, hs]
    simp
  nlinarith [norm_nonneg (t : C), norm_nonneg (s : C)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}

theorem exists_primitiveRoot (c : Coeff l) (W : ValuationSubring ℂ) {N : ℕ} (hN : N ∣ l.A) :
    ∃ ζ : ↥(c.V W), IsPrimitiveRoot ζ N := by
  obtain ⟨d, hd⟩ := hN
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by
    rintro rfl
    exact l.A_pos.ne' (by simpa using hd))
  have hprim : IsPrimitiveRoot (zeta l.A ^ d) N :=
    (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow l.A_pos (by rw [hd, mul_comm])
  have hF : zeta l.A ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hW : zeta l.A ^ d ∈ W := mem_of_pow_eq_one W hN0 hprim.pow_eq_one
  refine ⟨⟨⟨_, pow_mem hF d⟩, hW⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := (c.F.val.toRingHom).comp (c.V W).subtype) hprim
    (c.F.val.toRingHom.injective.comp Subtype.val_injective)

theorem embed_mem (W : ValuationSubring ℂ) (τ : E →+* ℂ) (x : 𝓞 E) : τ (x : E) ∈ W := by
  have h1 : IsIntegral ℤ (τ (x : E)) := x.2.map τ.toIntAlgHom
  have h2 : IsIntegral W (τ (x : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← hy]
  exact y.2

theorem natCast_mem_maximalIdeal (c : Coeff l) {W : ValuationSubring ℂ} {p : ℕ} (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) : (p : ↥(c.V W)) ∈ IsLocalRing.maximalIdeal ↥(c.V W) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have h1 : (p : ℂ) * (((y : c.F) : ℂ)) = 1 := by
    have := congrArg (fun t : ↥(c.V W) => (((t : c.F)) : ℂ)) hy
    simpa using this
  have h2 : ((y : c.F) : ℂ) = (p : ℂ)⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [ValuationSubring.mem_nonunits_iff_or] at hW
  rcases hW with h | h
  · exact hp.ne_zero (by exact_mod_cast h)
  · exact h (h2 ▸ y.2)

theorem exists_diffGen [IsGalois ℚ E] (c : Coeff l) {W : ValuationSubring ℂ} {p : ℕ} (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) :
    ∃ a : ↥(c.V W), (p : ↥(c.V W)) ∈ (Ideal.span {a}).radical ∧ ∀ (C : SCF p) (φ : ↥(c.V W) →+* ↥(intO ↥C.S)),
      Real.log ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ = -(vDiff E p * Real.log p) := by
  classical
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  let j : 𝓞 E →+* ↥(c.V W) := (embK c τ).codRestrict (c.V W) fun x => embed_mem W τ x
  have hpm := natCast_mem_maximalIdeal c hp hW
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpc : (p : 𝓞 E) ∈ Ideal.comap j (IsLocalRing.maximalIdeal ↥(c.V W)) := by
    rw [Ideal.mem_comap, map_natCast]; exact hpm
  let w : HeightOneSpectrum (𝓞 E) := ⟨Ideal.comap j (IsLocalRing.maximalIdeal ↥(c.V W)), Ideal.comap_isPrime _ _,
    fun h => hp0 (by rw [h] at hpc; simpa using hpc)⟩
  have hpw : (p : 𝓞 E) ∈ w.asIdeal := hpc
  have hunit : ∀ u, u ∉ w.asIdeal → IsUnit (j u) := fun u hu => by
    by_contra hc
    exact hu ((IsLocalRing.mem_maximalIdeal _).2 hc)
  have hm := multiplicity_different_eq E hp w hpw
  set m := multiplicity w.asIdeal (differentIdeal ℤ (𝓞 E)) with hmdef
  set e := Formalism.BasicNotions.eWL E w with hedef

  have hval : w.intValuation (p : 𝓞 E) = WithZero.exp (-(e : ℤ)) := by
    obtain ⟨n, hn⟩ := exists_intValuation_eq w hp0
    haveI := Fact.mk hp
    haveI := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.liesOver_span E p hp w.isPrime hpw
    have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    have he : e = (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count w.asIdeal := by
      rw [hedef, Formalism.BasicNotions.eWL, Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
        (Ideal.span {(p : ℤ)}) w.asIdeal (by rw [hmap]; exact ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.span_nat_ne_bot p), hmap]
    have h1 : (p : 𝓞 E) ∈ w.asIdeal ^ n := (w.intValuation_le_pow_iff_mem _ n).1 hn.le
    have h2 : (p : 𝓞 E) ∉ w.asIdeal ^ (n + 1) := fun hc => by
      have := (w.intValuation_le_pow_iff_mem _ (n + 1)).2 hc
      rw [hn, WithZero.exp_le_exp] at this
      push_cast at this
      omega
    have h3 := Ideal.count_normalizedFactors_eq (p := w.asIdeal) (x := Ideal.span {(p : 𝓞 E)}) (n := n)
      ((Ideal.span_singleton_le_iff_mem _).2 h1) (fun hc => h2 ((Ideal.span_singleton_le_iff_mem _).1 hc))
    rw [hn, he, h3]
  have he0 : e ≠ 0 := fun h0 => by
    have := (w.intValuation_lt_one_iff_mem _).2 hpw
    rw [hval, h0] at this
    simp at this
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hπ0 : π ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hsame : w.intValuation (π ^ e) = w.intValuation (p : 𝓞 E) := by
    rw [map_pow, hπ, hval, ← WithZero.exp_nsmul]
    simp
  obtain ⟨u, v, hu, hv, huv⟩ := exists_mul_eq_mul w (pow_ne_zero e hπ0) hsame
  have huvj : j u * (p : ↥(c.V W)) = j v * (j π) ^ e := by
    have := congrArg j huv
    simpa using this
  have hdvd : (j π) ^ e ∣ (p : ↥(c.V W)) :=
    ((hunit u hu).dvd_mul_left).1 ⟨j v, by rw [huvj, mul_comm]⟩
  refine ⟨(j π) ^ m, ⟨m, Ideal.mem_span_singleton.2 ?_⟩, fun C φ => ?_⟩
  · refine dvd_trans ?_ (pow_dvd_pow_of_dvd hdvd m)
    rw [← pow_mul]
    exact pow_dvd_pow _ (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero he0))
  · have hn : ‖((φ (j π) : ↥(intO ↥C.S)) : ↥C.S)‖ ^ e = (p : ℝ)⁻¹ := by
      have h1 := congrArg (fun t => ‖((φ t : ↥(intO ↥C.S)) : ↥C.S)‖) huvj
      simp only [map_mul, map_pow, map_natCast, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, norm_mul,
        norm_pow] at h1
      rwa [norm_of_isUnit ((hunit u hu).map φ), norm_of_isUnit ((hunit v hv).map φ), _root_.one_mul, _root_.one_mul, C.norm_p,
        eq_comm] at h1
    have hlog : (e : ℝ) * Real.log ‖((φ (j π) : ↥(intO ↥C.S)) : ↥C.S)‖ = -Real.log p := by
      rw [← Real.log_pow, hn, Real.log_inv]
    rw [map_pow, Subring.coe_pow, norm_pow, Real.log_pow, hm]
    linear_combination (vDiff E p) * hlog

theorem const_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → (∀ N : ℕ, N ∣ l.A → ∃ ζ : ↥(c.V W), IsPrimitiveRoot ζ N) ∧ (IsGalois ℚ E → ∃ a : ↥(c.V W), (p : ↥(c.V W)) ∈ (Ideal.span {a}).radical ∧ ∀ (C : SCF p) (φ : ↥(c.V W) →+* ↥(intO ↥C.S)), Real.log ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ = -(vDiff E p * Real.log p)) :=
  fun _ _ _ _ _ _ c _ _ hp hW => ⟨fun _ hN => exists_primitiveRoot c _ hN, fun _ => exists_diffGen c hp hW⟩

end GlobalTheory.HTConst
