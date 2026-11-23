import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LocalComponentsSurjective
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropZ
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsRegularSectionGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpecialFibreConstantStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.PropZPf

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem div_sub_mem {L : Lat ξ Ω} {q : Cpt ξ} {w σ tp tq y : Ω} (a : ℤ) (M : ℕ) (hw0 : w ≠ 0)
    (hwq : w ∈ regAt ξ q) (hσ : σ ≠ 0) (hgq : L.IsGenAt q tq) (htp : tp ≠ 0)
    (hhq : w ^ a / (σ / tq) ^ M ∈ regAt ξ q) (hy : y ∈ L q) (hd : tp - tq = w • y) :
    (w ^ a / (σ / tp) ^ M - w ^ a / (σ / tq) ^ M) / w ∈ regAt ξ q := by
  rw [hgq.2, Submodule.mem_span_singleton] at hy
  obtain ⟨r, rfl⟩ := hy
  have hr : ((r • tq : Ω)) = (r : Ω) * tq := rfl
  rw [hr, smul_eq_mul] at hd
  have htq := hgq.1
  have e1 : tp = tq * (1 + w * r) := by linear_combination hd
  have hu : (1 + w * (r : Ω)) ≠ 0 := by
    intro h0; apply htp; rw [e1, h0, mul_zero]
  have e2 : w ^ a / (σ / tp) ^ M = w ^ a / (σ / tq) ^ M * (1 + w * r) ^ M := by
    rw [e1, div_pow, div_pow, mul_pow]
    field_simp
  have g := geom_sum_mul (1 + w * (r : Ω)) M
  have e3 : (w ^ a / (σ / tp) ^ M - w ^ a / (σ / tq) ^ M) / w =
      w ^ a / (σ / tq) ^ M * (r : Ω) * ∑ i ∈ Finset.range M, (1 + w * (r : Ω)) ^ i := by
    rw [e2, div_eq_iff hw0]
    linear_combination (-(w ^ a / (σ / tq) ^ M)) * g
  rw [e3]
  refine mul_mem (mul_mem hhq r.2) (Subring.sum_mem _ fun i _ => pow_mem ?_ i)
  exact add_mem (one_mem _) (mul_mem hwq r.2)

end GlobalTheory.CompanionTheory.Ar.Flat.PropZPf

open GlobalTheory.CompanionTheory.Ar.Flat.PropZPf in

theorem GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds : GlobalTheory.CompanionTheory.Ar.Flat.PropZ := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hconn L σ hvb htriv hgen
  obtain ⟨M, a, hM, hreg, p₀, hp₀, -, hord₀⟩ :=
    GlobalTheory.CompanionTheory.Ar.Flat.exists_regular_section_generator X Ω ξ O s ϖ hϖ hinj hs hg hn hconn.nonempty L σ hvb hgen
  have hw0 : algebraMap O Ω ϖ ≠ 0 := fun e => hϖ.ne_zero (hinj (by rw [map_zero]; exact e))
  have hwreg : ∀ p : Cpt ξ, algebraMap O Ω ϖ ∈ regAt ξ p := fun p =>
    (GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.regular_const X Ω ξ O s hs p ϖ).1
  have hunit : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal :=
    fun p o => (GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.regular_const X Ω ξ O s hs p o).2 hg
  have hgf : ∀ q : Cpt ξ, unitAt ξ q (algebraMap O Ω ϖ) → q ∈ genFibre O ξ := by
    intro q hq o ho
    rw [hunit]
    intro hmem
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho hϖ
    have hP : (s q.1).asIdeal.IsPrime := (s q.1).isPrime
    rw [hu] at hmem
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (by
        have := Ideal.mul_mem_left _ ((u⁻¹ : Oˣ) : O) h1
        rwa [Units.inv_mul] at this))
    · exact (hunit q ϖ).1 hq (hP.mem_of_pow_mem n h1)
  have hσ : σ ≠ 0 := hord₀.ne_zero hM.ne'
  obtain ⟨t, ht⟩ := htriv
  have htq : ∀ q : Cpt ξ, ¬ unitAt ξ q (algebraMap O Ω ϖ) → L.IsGenAt q (t q) := fun q hq => by
    obtain ⟨U, hU, H⟩ := ht q hq
    obtain ⟨h0, h1, -⟩ := H q hU hq
    exact ⟨h0, h1⟩
  have hloc : ∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧
      ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) →
        (fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) p ∈ regAt ξ q ∧
        ((fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) p -
          (fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) q) / algebraMap O Ω ϖ ∈ regAt ξ q := by
    intro p hp
    obtain ⟨U, hU, H⟩ := ht p hp
    refine ⟨U, hU, fun q hqU hq => ?_⟩
    obtain ⟨h0, h1, y, hy, hd⟩ := H q hqU hq
    exact ⟨hreg q (t p) ⟨h0, h1⟩, div_sub_mem a M hw0 (hwreg q) hσ (htq q hq) h0
      (hreg q (t q) (htq q hq)) hy hd⟩
  have hu₀ : unitAt ξ p₀ ((fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) p₀) := by
    have := ZUnit.inv ((orderAt_iff_div (htq p₀ hp₀).1 (htq p₀ hp₀).2).1 hord₀)
    rwa [inv_div] at this
  have key := GlobalTheory.T.connected_special_fibre_constant X Ω ξ O s ϖ hϖ hinj hs hg hconn
    (fun p : Cpt ξ => algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) hloc ⟨p₀, hp₀, hu₀⟩
  refine ⟨M, a, hM, fun p => ?_⟩
  by_cases hp : unitAt ξ p (algebraMap O Ω ϖ)
  · have hgp := hgen p (hgf p hp)
    rw [orderAt_iff_div hgp.1 hgp.2, div_self hσ, one_pow, one_div]
    refine ZUnit.inv ⟨zpow_ne_zero a hw0, ZLat.zpow_mem_regAt hp a, ?_⟩
    rw [← zpow_neg]
    exact ZLat.zpow_mem_regAt hp (-a)
  · rw [orderAt_iff_div (htq p hp).1 (htq p hp).2]
    have h1 : unitAt ξ p (algebraMap O Ω ϖ ^ a / (σ / t p) ^ M) := key p hp
    have := ZUnit.inv h1
    rwa [inv_div] at this
