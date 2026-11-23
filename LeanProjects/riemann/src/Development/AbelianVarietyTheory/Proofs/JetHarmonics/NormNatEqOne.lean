import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
open Cardinal
namespace GlobalTheory.MomOne.Inh

theorem mk_le {A X : Type} [MetricSpace X] (f : A → X) (hf : DenseRange f) (hA : #A ≤ 𝔠) :
    #X ≤ 𝔠 := by
  have h : ∀ x : X, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := fun x => by
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa only [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (by rw [hxy]; exact hs y)
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat]
  exact (Cardinal.power_le_power_right hA).trans_eq Cardinal.continuum_power_aleph0

theorem nonempty_iso (p : ℕ) [Fact p.Prime] : Nonempty (ℂ ≃+* ℂ_[p]) := by
  have h1 : #ℚ_[p] ≤ 𝔠 := mk_le _ (Padic.denseRange_ratCast p)
    (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)
  have h2 : #(PadicAlgCl p) ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans (max_le h1 Cardinal.aleph0_le_continuum)
  have h3 : #(ℂ_[p]) ≤ 𝔠 := mk_le (X := PadicComplex p) _
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) h2
  have h4 : 𝔠 ≤ #(ℂ_[p]) := continuum_le_cardinal_of_nontriviallyNormedField _
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum) ?_
  exact Cardinal.eq.1 (by rw [Cardinal.mk_complex]; exact le_antisymm h4 h3)

theorem exists_ok {q : ℕ} [Fact q.Prime] (W : WeierstrassCurve ℂ_[q]) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1) : ∃ M : Mdl q, M.Ok ∧ M.W = W := by
  obtain ⟨ι⟩ := nonempty_iso q
  have hne : W.Δ ≠ 0 := by intro h; simp [h] at hΔ
  have hd : (ι.symm (W.c₄ / 12)) ^ 3 - 27 * (ι.symm (W.c₆ / 216)) ^ 2 ≠ 0 := by
    intro h
    have := congrArg ι h
    simp only [map_sub, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero, map_ofNat] at this
    apply hne
    have hr := W.c_relation
    linear_combination (1/1728) * hr + this
  obtain ⟨L, hL2, hL3⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants hd
  exact ⟨⟨ι, L, 1, W⟩, ⟨one_ne_zero, h1, h2, h3, h4, h6, hΔ, by simp [hL2], by simp [hL3]⟩, rfl⟩

theorem norm_nat_eq_one {q : ℕ} [Fact q.Prime] (n : ℕ) (h : ¬ q ∣ n) : ‖(n : ℂ_[q])‖ = 1 := by
  have : (n : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] (n : ℚ_[q]) := by simp
  rw [this, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h)

theorem exists_mdl_ok (q : ℕ) [hq : Fact q.Prime] : ∃ M : Mdl q, M.Ok := by
  by_cases h : q ∣ 27
  · have h' : ¬ q ∣ 64 := fun h' => hq.out.one_lt.ne' (Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 27 64) h h')
    obtain ⟨M, hM, -⟩ := exists_ok (q := q) ⟨0, 0, 0, -1, 0⟩ (by simp) (by simp) (by simp) (by simp) (by simp) (by
      rw [← norm_nat_eq_one 64 h']; congr 1
      simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]; norm_num)
    exact ⟨M, hM⟩
  · obtain ⟨M, hM, -⟩ := exists_ok (q := q) ⟨0, 0, 1, 0, 0⟩ (by simp) (by simp) (by simp) (by simp) (by simp) (by
      rw [← norm_nat_eq_one 27 h, ← norm_neg]; congr 1
      simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])
    exact ⟨M, hM⟩
end GlobalTheory.MomOne.Inh
