import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulPowTwoLeTripleProdOfGe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.MomOne PeriodPair

namespace GlobalTheory.CompRat.Inertia

theorem exists_ringEquiv (p : ℕ) [hp : Fact p.Prime] (A : ValuationSubring ℂ) (hA : (p : ℂ) ∈ A.nonunits) :
    ∃ ι : ℂ ≃+* ℂ_[p], ∀ x : ℂ, IsAlgebraic ℚ x → (x ∈ A ↔ ‖ι x‖ ≤ 1) := by
  let Ω := algebraicClosure ℚ ℂ
  have : IsAlgClosure ℚ Ω := algebraicClosure.isAlgClosure ℚ ℂ
  let B : ValuationSubring Ω := A.comap (algebraMap Ω ℂ)
  have hB : B.valuation (p : Ω) < 1 := by
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at *
    refine hA.imp (fun h => absurd (by exact_mod_cast h) hp.out.ne_zero) fun h h' => h ?_
    have : algebraMap Ω ℂ (p : Ω)⁻¹ ∈ A := h'
    simpa using this
  have hpr : Prime (p : 𝓞 ℚ) := by
    have := (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm).2 (Nat.prime_iff_prime_int.1 hp.out)
    simpa using this
  let w : HeightOneSpectrum (𝓞 ℚ) := ⟨Ideal.span {(p : 𝓞 ℚ)}, (Ideal.span_singleton_prime hpr.ne_zero).2 hpr,
    by simpa using hpr.ne_zero⟩
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := p) ℚ Ω w B (Ideal.mem_span_singleton_self _) fun x => by
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    have e : algebraMap ℚ Ω ((Rat.ringOfIntegersEquiv.symm n : 𝓞 ℚ) : ℚ) = (n : Ω) := by simp
    rw [e, GlobalTheory.PlaceBridge.val_int_lt_one_iff B hp.out hB]
    change _ ↔ _ ∈ Ideal.span _
    rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv]
    simp
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p ((algebraMap (PadicAlgCl p) ℂ_[p]).comp j)
  refine ⟨ι, fun x hx => ?_⟩
  have e := hι ⟨x, mem_algebraicClosure_iff.2 hx⟩
  rw [show ι x = _ from e, RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends, ← hj]
  rfl

theorem exists_coord {d : ℕ} (hd : d.Prime) (hd' : d % 16 = 7) {L : PeriodPair} (hL : IsOK d L) {p : ℕ} (hp : p.Prime)
    (A : ValuationSubring ℂ) (hA : (p : ℂ) ∈ A.nonunits) {N : ℕ} (hN : ¬ p ∣ N) :
    ∃ (x : ℂ → ℂ) (α β : ℂ), α ≠ 0 ∧ (∀ z, x z = α * ℘[L] z + β) ∧
      (∀ z, (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice → IsAlgebraic ℚ (x z) ∧ x z ∈ A) ∧
      ∀ z z', (N : ℂ) * z ∈ L.lattice → (N : ℂ) * z' ∈ L.lattice → z ∉ L.lattice → z' ∉ L.lattice →
        x z - x z' ∈ A.nonunits → z - z' ∈ L.lattice ∨ z + z' ∈ L.lattice := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ι, hι⟩ := exists_ringEquiv p A hA
  obtain ⟨M, rfl, rfl, hM, h₁, h₂, h₃, h₄, h₆⟩ := exists_model d p ι L hd hd' hL
  obtain ⟨t1, t2⟩ := TorsionReduction.torsion_integral_and_distinct p M N hM
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hN).symm
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hN (dvd_zero _))
  let K := algebraicClosure ℚ ℂ_[p]
  have tr : ∀ y : ℂ, M.ι y ∈ K → y ∈ algebraicClosure ℚ ℂ := fun y hy =>
    mem_algebraicClosure_iff.2 ((isAlgebraic_algHom_iff (M.ι : ℂ →+* ℂ_[p]).toRatAlgHom M.ι.injective).1
      (mem_algebraicClosure_iff.1 hy))
  let W₀ : WeierstrassCurve K := ⟨⟨_, mem_algebraicClosure_iff.2 h₁⟩, ⟨_, mem_algebraicClosure_iff.2 h₂⟩,
    ⟨_, mem_algebraicClosure_iff.2 h₃⟩, ⟨_, mem_algebraicClosure_iff.2 h₄⟩, ⟨_, mem_algebraicClosure_iff.2 h₆⟩⟩
  have hW : W₀.map (algebraMap K ℂ_[p]) = M.W := rfl
  have hb : M.W.b₂ ∈ K := by rw [← hW, WeierstrassCurve.map_b₂]; exact W₀.b₂.2
  have h4 : M.W.c₄ ∈ K := by rw [← hW, WeierstrassCurve.map_c₄]; exact W₀.c₄.2
  have h6 : M.W.c₆ ∈ K := by rw [← hW, WeierstrassCurve.map_c₆]; exact W₀.c₆.2
  have hh := isHomothetic_scalePeriods M.L M.c hM.1
  generalize scalePeriods M.L M.c hM.1 = L' at hh
  have g2 : L'.g₂ ∈ algebraicClosure ℚ ℂ := tr _ (by
    rw [hh.g₂_eq, inv_mul_eq_div, ← hM.2.2.2.2.2.2.2.1]
    exact K.div_mem h4 (ofNat_mem K 12))
  have g3 : L'.g₃ ∈ algebraicClosure ℚ ℂ := tr _ (by
    rw [hh.g₃_eq, inv_mul_eq_div, ← hM.2.2.2.2.2.2.2.2]
    exact K.div_mem h6 (ofNat_mem K 216))
  have alg : ∀ z, (N : ℂ) * z ∈ M.L.lattice → z ∉ M.L.lattice → M.x z ∈ algebraicClosure ℚ ℂ := fun z hz hz' => by
    have h := (GlobalTheory.CurveAlgebraic.weierstrassP_mem L' (t := M.c * z) g2 g3 hN0 (by rwa [hh])
      (by rwa [mul_left_comm, hh])).1
    rw [hh.weierstrassP_mul, inv_mul_eq_div] at h
    exact sub_mem h (tr _ (by rw [RingEquiv.apply_symm_apply]; exact K.div_mem hb (ofNat_mem K 12)))
  refine ⟨M.x, (M.c ^ 2)⁻¹, -M.ι.symm (M.W.b₂ / 12), inv_ne_zero (pow_ne_zero _ hM.1), fun z => ?_,
    fun z hz hz' => ?_, fun z z' hz hz' h h' hx => ?_⟩
  · rw [Mdl.x]; ring
  · have ha := mem_algebraicClosure_iff.1 (alg z hz hz')
    exact ⟨ha, (hι _ ha).2 (t1 z hz hz')⟩
  · by_contra hc
    rw [not_or] at hc
    have e := t2 z z' hz hz' h h' hc.2 hc.1
    rw [← map_sub] at e
    rcases (ValuationSubring.mem_nonunits_iff_or A).1 hx with h0 | h0
    · simp [h0] at e
    · exact h0 ((hι _ (mem_algebraicClosure_iff.1 (inv_mem (sub_mem (alg z hz h) (alg z' hz' h'))))).2
        (by rw [map_inv₀, norm_inv, e, inv_one]))

end GlobalTheory.CompRat.Inertia
