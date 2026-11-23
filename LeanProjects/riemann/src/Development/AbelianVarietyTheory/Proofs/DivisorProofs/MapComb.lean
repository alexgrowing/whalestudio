import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecond

theorem map_formalGroupLawCoboundaryOne_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hμ),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

end GlobalTheory.SmallSecond

namespace GlobalTheory.SmallSecond

variable {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
  [Algebra O C] {θ : B →+* O} {Θ : Q →+* C}

theorem map_up {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) :
    (fun i => map Θ (up Q μ' i)) = up C (fun i => map θ (μ' i)) := by
  funext i; ext α; simp [up, coeff_map, hΘ]

theorem map_formalGroupLawCoboundaryOne_square {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    (f : MvPowerSeries (Fin d) Q) :
    map Θ (cob1 (up Q μ') f) = cob1 (up C (fun i => map θ (μ' i))) (map Θ f) := by
  rw [map_formalGroupLawCoboundaryOne_eq Θ _ (fun i => by simp [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
    coeff_zero_eq_constantCoeff_apply, hμ]), map_up hΘ]

theorem map_comb {σ ι : Type} [Fintype ι] (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    map Θ (comb b e) = comb (fun i => θ (b i)) (fun i => map Θ (e i)) := by
  unfold comb
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext α
  rw [coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_map, map_mul, hΘ]

theorem ql_map {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : QL μ' ⊤ f) :
    QL (fun i => map θ (μ' i)) ⊤ (map Θ f) := by
  obtain ⟨h0, h1, h2⟩ := hf
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  · obtain ⟨b, -, hb⟩ := h1 i
    exact ⟨θ b, trivial, by simp only [lin, coeff_map] at hb ⊢; rw [hb, hΘ]⟩
  · rw [← map_formalGroupLawCoboundaryOne_square hΘ μ' hμ]
    intro α
    obtain ⟨b, -, hb⟩ := h2 α
    exact ⟨θ b, trivial, by rw [coeff_map, hb, hΘ]⟩

theorem formalGroupLawCoboundaryOne_map_eq_zero {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : In (RingHom.ker θ) (cob1 (up Q μ') f)) :
    cob1 (up C (fun i => map θ (μ' i))) (map Θ f) = 0 := by
  rw [← map_formalGroupLawCoboundaryOne_square hΘ μ' hμ]
  ext α
  obtain ⟨b, hb0, hb⟩ := hf α
  rw [coeff_map, hb, hΘ, RingHom.mem_ker.1 hb0, map_zero, map_zero]

end GlobalTheory.SmallSecond
