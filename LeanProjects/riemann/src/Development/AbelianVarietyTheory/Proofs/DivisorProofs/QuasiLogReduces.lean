import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundariesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryOneTeichmullerLiftIsCocycleModPStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

open CategoryTheory TensorProduct MvPowerSeries in
private lemma mem_quasiLog_iff (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : _root_.GlobalTheory.Katz.IsLaw μ)
    (f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k)) :
    f ∈ _root_.GlobalTheory.Katz.quasiLog p h ↔
      f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d) ∧
        _root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f ∈
          _root_.GlobalTheory.Katz.intBy p k (Fin d ⊕ Fin d) 1 := by
  unfold _root_.GlobalTheory.Katz.quasiLog
  exact Iff.rfl

open CategoryTheory TensorProduct MvPowerSeries in
private lemma exists_lin_eq_algebraMap_of_mem_quasiInt (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    {d : ℕ} {f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k)}
    (hf : f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d)) (i : Fin d) :
    ∃ a, _root_.GlobalTheory.Katz.lin f i = algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) a := by
  obtain ⟨a, ha⟩ := hf (Finsupp.single i 1) i
  exact ⟨a, by simpa [_root_.GlobalTheory.Katz.lin] using ha⟩

open CategoryTheory TensorProduct MvPowerSeries in
private lemma isCoc_of_red_cob1_quasiInt (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (h : _root_.GlobalTheory.Katz.IsLaw μ) (f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k))
    (hf : f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d))
    (c : MvPowerSeries (Fin d ⊕ Fin d) k)
    (hc : _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c) :
    _root_.GlobalTheory.Katz.IsCoc μ c := by
  obtain ⟨-, huniq, -, hadd, -, hdivp, -⟩ := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)
  obtain ⟨-, huniq3, -, -, -, hdivp3, -⟩ :=
    _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d ⊕ Fin d)
  obtain ⟨htwo, hswap⟩ := _root_.GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem p k d μ h f hf
  obtain ⟨hcomm, -⟩ := _root_.GlobalTheory.Katz.red_coboundaries p k d μ
    h.const
  obtain ⟨hred2, hredswap⟩ := hcomm _ c hc
  unfold _root_.GlobalTheory.Katz.IsCoc
  refine ⟨huniq3 _ _ _ hred2 ((hdivp3 _).1 htwo), ?_⟩
  exact sub_eq_zero.1 (huniq _ _ _ (hadd _ _ _ _ hredswap hc).2 ((hdivp _).1 hswap))

open CategoryTheory TensorProduct MvPowerSeries in

theorem _root_.GlobalTheory.quasiLog_reduces : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : _root_.GlobalTheory.Katz.IsLaw μ), (∀ f ∈ _root_.GlobalTheory.Katz.quasiLog p h, ∃ c w, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c ∧ _root_.GlobalTheory.Katz.RedV p (_root_.GlobalTheory.Katz.lin f) w) ∧ ∀ f ∈ _root_.GlobalTheory.Katz.quasiLog p h, ∀ c, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c → _root_.GlobalTheory.Katz.IsCoc μ c := by
  intro p _ k _ _ _ d μ h
  refine ⟨fun f hf => ?_, fun f hf c hc => ?_⟩
  · obtain ⟨hint, hcob⟩ := (mem_quasiLog_iff p k d μ h f).1 hf
    obtain ⟨c, hc⟩ := ((_root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)).1 _).1 hcob
    choose a ha using exists_lin_eq_algebraMap_of_mem_quasiInt p k hint
    exact ⟨c, fun i => WittVector.constantCoeff (a i), hc, fun i => ⟨a i, ha i, rfl⟩⟩
  · exact isCoc_of_red_cob1_quasiInt p k d μ h f
      ((mem_quasiLog_iff p k d μ h f).1 hf).1 c hc

end GlobalTheory
