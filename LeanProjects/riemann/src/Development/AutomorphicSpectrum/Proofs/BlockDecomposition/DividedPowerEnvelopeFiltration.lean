import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdealStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.PDCrit

private theorem pq_isStd_eta {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) :
    (pq B).IsStd δ (eta δ) :=
  Classical.choose_spec (FubiniStudyChowHeightFormula₂.Adr.exists_std B J δ (pq B))

theorem repr_sum {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (b : ℕ →₀ B) :
    (pq B).e.repr (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) = b := by
  have hs := pq_isStd_eta δ
  have h1 : (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) =
      Finsupp.linearCombination B (pq B).e b := by
    rw [Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun k _ => ?_
    rw [hs.var k, Algebra.smul_def]
  rw [h1, (pq B).e.repr_linearCombination]

theorem mem_span_iff {B : Type} [CommRing B] (c : B) (z : (pq B).P) :
    z ∈ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, (pq B).e.repr z k ∈ Ideal.span {c} := by
  constructor
  · intro hz k
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)
  · intro h
    choose d hd using fun k => Ideal.mem_span_singleton'.1 (h k)
    rw [Ideal.mem_span_singleton']
    refine ⟨∑ k ∈ ((pq B).e.repr z).support, d k • (pq B).e k, ?_⟩
    conv_rhs => rw [← (pq B).e.linearCombination_repr z]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hd k, mul_comm (d k • (pq B).e k), ← Algebra.smul_def, smul_smul, mul_comm c (d k)]

private theorem sum_finsupp_single_apply_eq_ite {B : Type} [CommRing B] (s : Finset ℕ) (a : ℕ → B) (k : ℕ) :
    (∑ i ∈ s, Finsupp.single i (a i)) k = if k ∈ s then a k else 0 := by
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem mem_fil_sup_iff {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r : ℕ) (c : B)
    (z : (pq B).P) :
    z ∈ fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c} ↔
      ∀ k, (pq B).e.repr z k ∈ fil δ (r - k) ⊔ Ideal.span {c} := by
  have hT := (GlobalTheory.T.divided_power_polynomial_filtration δ (pq B) (eta δ) (pq_isStd_eta δ)).2.2.2
  constructor
  · intro hz k
    obtain ⟨a, ha, s, hs, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add, Finsupp.add_apply]
    exact Submodule.add_mem_sup ((hT r a).1 ha k) ((mem_span_iff c s).1 hs k)
  · intro h
    choose a ha s hs hsum using fun k => Submodule.mem_sup.1 (h k)
    have hF : (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (a i)) +
        (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (s i)) = (pq B).e.repr z := by
      ext k
      rw [Finsupp.add_apply, sum_finsupp_single_apply_eq_ite, sum_finsupp_single_apply_eq_ite]
      split_ifs with hk
      · exact hsum k
      · rw [add_zero]
        exact (Finsupp.notMem_support_iff.1 hk).symm
    have hz : z = (pq B).e.repr.symm (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (a i)) +
        (pq B).e.repr.symm (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (s i)) := by
      rw [← map_add, hF, LinearEquiv.symm_apply_apply]
    rw [hz]
    refine Submodule.add_mem_sup ((hT r _).2 fun k => ?_) ((mem_span_iff c _).2 fun k => ?_)
    · rw [LinearEquiv.apply_symm_apply, sum_finsupp_single_apply_eq_ite]
      split_ifs
      · exact ha k
      · exact Submodule.zero_mem _
    · rw [LinearEquiv.apply_symm_apply, sum_finsupp_single_apply_eq_ite]
      split_ifs
      · exact hs k
      · exact Submodule.zero_mem _

theorem coeff_criteria : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (b : ℕ →₀ B) (r : ℕ) (c : B), ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil (eta δ) r ↔ ∀ k, b k ∈ fil δ (r - k)) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, b k ∈ fil δ (r - k) ⊔ Ideal.span {c}) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, b k ∈ Ideal.span {c}) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) = 0 ↔ ∀ k, b k = 0) := by
  intro B _ J δ b r c
  have hT := (GlobalTheory.T.divided_power_polynomial_filtration δ (pq B) (eta δ) (pq_isStd_eta δ)).2.2.2
  have hr := repr_sum δ b
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hT, hr]
  · rw [mem_fil_sup_iff, hr]
  · rw [mem_span_iff, hr]
  · rw [← LinearEquiv.map_eq_zero_iff (pq B).e.repr, hr]
    simp only [Finsupp.ext_iff, Finsupp.coe_zero, Pi.zero_apply]

end GlobalTheory.CompanionTheory.PDCrit
