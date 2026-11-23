import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

set_option autoImplicit false

open Cardinal

namespace GlobalTheory.PadicComplexIso

theorem exists_ringEquiv_over (R K L : Type) [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra R K] [Algebra R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ e : K ≃+* L, ∀ x : R, e (algebraMap R K x) = algebraMap R L x := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have hL : ℵ₀ < #L := hKL ▸ hK
  have hsK : #K = #s := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have htL : #L = #t := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR hL
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.1 (hsK.symm.trans (hKL.trans htL))
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e0 : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R] Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e0.toRingEquiv, fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

theorem mk_le_continuum_of_denseRange {X Y : Type} [MetricSpace Y] (f : X → Y)
    (hf : DenseRange f) (hX : #X ≤ 𝔠) : #Y ≤ 𝔠 := by
  have hex : ∀ (y : Y) (n : ℕ), ∃ x, dist (f x) y < 1 / ((n : ℝ) + 1) := by
    intro y n
    obtain ⟨x, hx⟩ := Metric.denseRange_iff.1 hf y (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    exact ⟨x, by rw [dist_comm]; exact hx⟩
  choose g hg using hex
  have hlim : ∀ y, Filter.Tendsto (fun n => f (g y n)) Filter.atTop (nhds y) := by
    intro y
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hg y n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hinj : Function.Injective g := by
    intro y y' h
    have h2 := hlim y'
    rw [← h] at h2
    exact tendsto_nhds_unique (hlim y) h2
  calc #Y ≤ #(ℕ → X) := Cardinal.mk_le_of_injective hinj
    _ = #X ^ ℵ₀ := by rw [← Cardinal.mk_nat, Cardinal.power_def]
    _ ≤ 𝔠 ^ ℵ₀ := Cardinal.power_le_power_right hX
    _ = 𝔠 := Cardinal.continuum_power_aleph0

theorem mk_padicComplex (q : ℕ) [Fact q.Prime] : #ℂ_[q] = 𝔠 := by
  apply le_antisymm
  · have hQp : #ℚ_[q] ≤ 𝔠 :=
      mk_le_continuum_of_denseRange _ (Padic.denseRange_ratCast q)
        (by rw [Cardinal.mkRat]; exact Cardinal.aleph0_le_continuum)
    have hAl : #(PadicAlgCl q) ≤ 𝔠 :=
      (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[q] (PadicAlgCl q)).trans
        (max_le hQp Cardinal.aleph0_le_continuum)
    exact mk_le_continuum_of_denseRange _ (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl q)) hAl
  · obtain ⟨g, -, -, hg⟩ :=
      (PerfectSpace.univ_perfect (α := ℂ_[q])).exists_nat_bool_injection Set.univ_nonempty
    calc 𝔠 = #(ℕ → Bool) := by
          rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]
      _ ≤ #ℂ_[q] := Cardinal.mk_le_of_injective hg

theorem exists_ringEquiv_extending : ∀ (q : ℕ) [Fact q.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[q]),
    ∃ ι : ℂ ≃+* ℂ_[q], ∀ x : algebraicClosure ℚ ℂ, ι (x : ℂ) = lam x := by
  intro q _ lam
  let _ : Algebra (algebraicClosure ℚ ℂ) ℂ_[q] := lam.toAlgebra
  have _ : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hR : #(algebraicClosure ℚ ℂ) ≤ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ (algebraicClosure ℚ ℂ)).trans
      (by rw [Cardinal.mkRat, max_self])
  have hK : ℵ₀ < #ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  obtain ⟨e, he⟩ := exists_ringEquiv_over (algebraicClosure ℚ ℂ) ℂ ℂ_[q] hR hK
    (by rw [Cardinal.mk_complex, mk_padicComplex])
  exact ⟨e, fun x => he x⟩

end GlobalTheory.PadicComplexIso
