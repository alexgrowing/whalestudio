import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdealStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SiteTrCrit

variable {B : Type} [CommRing B] {J : Ideal B}

theorem sum_eq (δ : DividedPowers J) (b : ℕ →₀ B) :
    (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) =
      Finsupp.linearCombination B (pq B).e b := by
  rw [Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [(eta_std δ).var k, Algebra.smul_def]

theorem repr_sum (δ : DividedPowers J) (b : ℕ →₀ B) :
    (pq B).e.repr (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) = b := by
  rw [sum_eq]
  exact (pq B).e.repr_linearCombination b

theorem crit_sup (δ : DividedPowers J) (r : ℕ) (z : (pq B).P) (c : B) :
    z ∈ fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c} ↔
      ∀ k, (pq B).e.repr z k ∈ fil δ (r - k) ⊔ Ideal.span {c} := by
  have crit := (GlobalTheory.CompanionTheory.PDFil.fil_pdPoly δ (pq B) (eta δ) (eta_std δ)).2.2.2 r
  constructor
  · intro hz k
    obtain ⟨f, hf, g, hg, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    have e : w * algebraMap B (pq B).P c = c • w := by rw [Algebra.smul_def, mul_comm]
    rw [e, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mem_sup_left ((crit f).1 hf k))
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)))
  · intro h
    rw [← (pq B).e.linearCombination_repr z, Finsupp.linearCombination_apply]
    refine Ideal.sum_mem _ fun k _ => ?_
    obtain ⟨f, hf, g, hg, e⟩ := Submodule.mem_sup.1 (h k)
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    rw [← e]
    beta_reduce
    rw [add_smul]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ((crit _).2 fun j => ?_)) (Ideal.mem_sup_right ?_)
    · rw [map_smul, (pq B).e.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]
      split_ifs with hj
      · rw [← hj]; exact hf
      · exact Ideal.zero_mem _
    · rw [mul_comm w c, mul_smul, Algebra.smul_def c]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.SiteTrCrit

open GlobalTheory.CompanionTheory.SiteTrCrit in

theorem GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → ∀ (b : ℕ →₀ B) (r : ℕ), r ≤ s → ∀ c : B, (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ↔ ∀ k, b k ∈ fil δ (r - k)) ∧ (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ⊔ Ideal.span {Ideal.Quotient.mk (fil (eta δ) (max s 1)) (algebraMap B (pq B).P c)} ↔ ∀ k, b k ∈ fil δ (r - k) ⊔ Ideal.span {c}) := by
  intro B _ J δ s δ' hδ' b r hr c
  have hK : fil (eta δ) (max s 1) ≤ fil (eta δ) r :=
    GlobalTheory.Cris.ExpBij.dpFil_anti (eta δ) (le_max_of_le_left hr)
  have hfil : fil δ' r = (fil (eta δ) r).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))) :=
    le_antisymm (FubiniStudyChowHeightFormula₂.Adr.Fil.fil_le_map_fil _ _ (eta δ) _ _ δ' _ hδ' rfl r)
      (FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le (eta δ) δ' _ hδ' r)
  have hsup : (fil (eta δ) r).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))) ⊔
      Ideal.span {Ideal.Quotient.mk (fil (eta δ) (max s 1)) (algebraMap B (pq B).P c)} =
      (fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c}).map
        (Ideal.Quotient.mk (fil (eta δ) (max s 1))) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rw [hfil, hsup, Ideal.mem_quotient_iff_mem hK, Ideal.mem_quotient_iff_mem (hK.trans le_sup_left),
    crit_sup, (GlobalTheory.CompanionTheory.PDFil.fil_pdPoly δ (pq B) (eta δ) (eta_std δ)).2.2.2, repr_sum]
  exact ⟨Iff.rfl, Iff.rfl⟩
