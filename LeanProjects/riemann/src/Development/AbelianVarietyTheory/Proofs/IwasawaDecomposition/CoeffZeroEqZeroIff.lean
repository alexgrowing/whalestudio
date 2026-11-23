import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.PinPlace

theorem mem_mul_iff {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) (y : K) :
    (∃ a : R, y = algebraMap R K (ϖ * a)) ↔ y = 0 ∨ y⁻¹ ∉ (algebraMap R K).range := by
  have hinj := IsFractionRing.injective R K
  constructor
  · rintro ⟨a, rfl⟩
    by_contra hc
    push Not at hc
    obtain ⟨h0, b, hb⟩ := hc
    have h1 : ϖ * a * b = 1 := hinj (by rw [map_mul, hb, mul_inv_cancel₀ h0, map_one])
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one (a * b) (by rw [← mul_assoc, h1]))
  · rintro (rfl | h)
    · exact ⟨0, by simp⟩
    · rcases ValuationRing.isInteger_or_isInteger R y with ⟨b, rfl⟩ | hb
      · have hb : ¬ IsUnit b := by
          rintro ⟨u, rfl⟩
          refine h ⟨(u⁻¹ : Rˣ), ?_⟩
          exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
        have hm : b ∈ IsLocalRing.maximalIdeal R := hb
        rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
        obtain ⟨a, rfl⟩ := hm
        exact ⟨a, rfl⟩
      · exact absurd hb h

variable {D : D7} {p : ℕ} [Fact p.Prime] {la : PlL D p} {jc : DV.KW p →+* ℂ}

theorem mem_range_iff (h : JcPin D p la jc) {y : DV.KW p} {z : D.what₂.LL} (hyz : jc y = D.what₂.embLL z) :
    y ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range ↔
      la.1.valuation D.what₂.LL z ≤ 1 := by
  obtain ⟨W, h1, h2⟩ := h
  rw [← h2, hyz, h1]

theorem mem_pW_iff (h : JcPin D p la jc) {y : DV.KW p} {z : D.what₂.LL} (hyz : jc y = D.what₂.embLL z) :
    (∃ a : WittVector p (AlgebraicClosure (ZMod p)),
        y = algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) (p * a)) ↔
      la.1.valuation D.what₂.LL z < 1 := by
  rw [mem_mul_iff (WittVector.irreducible p) y,
    mem_range_iff h (y := y⁻¹) (z := z⁻¹) (by rw [map_inv₀, map_inv₀, hyz])]
  have h0 : y = 0 ↔ z = 0 := by
    rw [← map_eq_zero_iff jc jc.injective, hyz, map_eq_zero_iff _ D.what₂.embLL.injective]
  rw [h0, map_inv₀, not_le]
  by_cases hz : z = 0
  · simp [hz]
  · have hv : 0 < la.1.valuation D.what₂.LL z := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz)
    rw [one_lt_inv₀ hv]
    simp [hz]

theorem pinned_reads_place : ∀ (D : D7) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)),
    (∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) →
    ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p) (τ : DV.Emb D p) (e : D.host.E →+* D.what₂.LL),
      (jC p la).comp τ = D.what₂.embLL.comp e → ∀ x : 𝓞 D.host.E,
        τ x ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range ∧
        ((∃ a : WittVector p (AlgebraicClosure (ZMod p)),
            τ x = algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) (p * a)) ↔
          la.1.valuation D.what₂.LL (e x) < 1) ∧
        (la.1.valuation D.what₂.LL (e x) < 1 ↔ RingOfIntegers.mapRingHom e x ∈ la.1.asIdeal) := by
  intro D jC h p _ la τ e hτ x
  have hx : jC p la (τ x) = D.what₂.embLL (e x) := RingHom.congr_fun hτ (x : D.host.E)
  have he : e x = algebraMap (𝓞 D.what₂.LL) D.what₂.LL (RingOfIntegers.mapRingHom e x) := rfl
  refine ⟨(mem_range_iff (h p la) hx).2 ?_, mem_pW_iff (h p la) hx, ?_⟩
  · rw [he]; exact la.1.valuation_le_one _
  · rw [he]; exact la.1.valuation_lt_one_iff_mem _

theorem coeff_zero_eq_zero_iff {k : Type} [Field k] [CharP k p] [PerfectRing k p] (b : WittVector p k) :
    b.coeff 0 = 0 ↔ ∃ a : WittVector p k, b = p * a := by
  constructor
  · intro h0
    have hb : ¬ IsUnit b := by
      rintro ⟨u, rfl⟩
      have h1 := congrArg (fun w : WittVector p k => w.coeff 0) u.mul_inv
      simp only [WittVector.mul_coeff_zero, WittVector.one_coeff_zero] at h1
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    have hm : b ∈ IsLocalRing.maximalIdeal (WittVector p k) := hb
    rw [(WittVector.irreducible p).maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨a, rfl⟩ := hm
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [WittVector.mul_coeff_zero]
    have : ((p : WittVector p k)).coeff 0 = 0 := by simp
    rw [this, zero_mul]

theorem pinned_tiedFor : ∀ (D : D7) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)),
    (∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) → Formalism.L2.Geo.ComplexEmbeddingsCompatible jC := by
  intro D jC h p _ la τ e hτ x
  obtain ⟨-, h2, -⟩ := pinned_reads_place D jC h p la τ e hτ x
  rw [← h2]
  constructor
  · rintro ⟨b, hb, h0⟩
    obtain ⟨a, rfl⟩ := (coeff_zero_eq_zero_iff b).1 h0
    exact ⟨a, hb.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨p * a, ha.symm, (coeff_zero_eq_zero_iff _).2 ⟨a, rfl⟩⟩

end GlobalTheory.ShFam.PinPlace
