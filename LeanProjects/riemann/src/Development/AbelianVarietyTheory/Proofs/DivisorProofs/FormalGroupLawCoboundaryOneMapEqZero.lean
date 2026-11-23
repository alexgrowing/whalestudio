import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffFrob

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
open GlobalTheory.QLog.Window

namespace GlobalTheory.QLog.WindowMat

theorem integers_isIntegrallyClosedIn {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsIntegrallyClosedIn O C :=
  isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 h)⟩

theorem hasPeriod_zero {p : ℕ} {O B Q : Type} [CommRing O] [CommRing B] [CommRing Q] [Algebra B Q]
    {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d) {θ : B →+* O} (h : IsFrame p Q θ)
    (t : G.Tate) : c.HasPeriod θ t (0 : MvPowerSeries (Fin d) Q) 0 := by
  refine (c.hasPeriod_iff h t (0 : MvPowerSeries (Fin d) Q) 0).2 fun n z _ => ⟨0, fun m => ⟨0, fun N _ => ⟨0, ?_⟩⟩, 0, ?_⟩
  · have h0 : trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N) (0 : MvPowerSeries (Fin d) Q) = 0 :=
      map_zero _
    rw [h0, map_zero, sub_zero, mul_zero, map_zero]
  · simp

section Transfer

variable {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
  [Algebra O C] (θ : B →+* O) (Θ : Q →+* C)
  (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
include hΘ

theorem in_map_top {σ : Type} {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (⊤ : Ideal O) (map Θ f) := fun α => by
  obtain ⟨b, -, eb⟩ := hf α
  exact ⟨θ b, Submodule.mem_top, by rw [coeff_map, eb, hΘ]⟩

theorem map_eq_zero_of_in_ker {σ : Type} {f : MvPowerSeries σ Q} (hf : In (RingHom.ker θ) f) :
    map Θ f = 0 := by
  ext α
  obtain ⟨b, hb, eb⟩ := hf α
  rw [coeff_map, eb, hΘ, RingHom.mem_ker.1 hb, map_zero, map_zero]

theorem map_comb {σ ι : Type} [Finite σ] [Fintype ι] (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    map Θ (comb b e) = comb (fun i => θ (b i)) fun i => map Θ (e i) := by
  unfold comb
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul', hΘ]

theorem lin_map {d : ℕ} (f : MvPowerSeries (Fin d) Q) (i : Fin d) : lin (map Θ f) i = Θ (lin f i) := by
  simp only [lin, coeff_map]

theorem up_map {d : ℕ} {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, map θ (μ' i) = μ i) (i : Fin d) :
    up C μ i = map Θ (up Q μ' i) := by
  ext α
  simp only [up, coeff_map, ← hμ, hΘ]

theorem ql_map {d : ℕ} {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, map θ (μ' i) = μ i)
    (h0 : ∀ i, constantCoeff (μ' i) = 0) {f : MvPowerSeries (Fin d) Q} (hf : QL μ' ⊤ f) :
    QL μ ⊤ (map Θ f) := by
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [constantCoeff_map, hf.1, map_zero]
  · obtain ⟨b, -, eb⟩ := hf.2.1 i
    exact ⟨θ b, Submodule.mem_top, by rw [lin_map θ Θ hΘ, eb, hΘ]⟩
  · have : up C μ = fun i => map Θ (up Q μ' i) := funext (up_map θ Θ hΘ hμ)
    rw [this, ← map_formalGroupLawCoboundaryOne_eq Θ _ (constantCoeff_up h0)]
    exact in_map_top θ Θ hΘ hf.2.2

theorem formalGroupLawCoboundaryOne_map_eq_zero {d : ℕ} {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, map θ (μ' i) = μ i)
    (h0 : ∀ i, constantCoeff (μ' i) = 0) {f : MvPowerSeries (Fin d) Q}
    (hf : In (RingHom.ker θ) (cob1 (up Q μ') f)) : cob1 (up C μ) (map Θ f) = 0 := by
  have : up C μ = fun i => map Θ (up Q μ' i) := funext (up_map θ Θ hΘ hμ)
  rw [this, ← map_formalGroupLawCoboundaryOne_eq Θ _ (constantCoeff_up h0)]
  exact map_eq_zero_of_in_ker θ Θ hΘ hf

end Transfer

theorem comb_sum {B Q σ ι κ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype ι] [Fintype κ]
    (R : κ → ι → B) (a : ι → B) (e : κ → MvPowerSeries σ Q) :
    comb (fun l => ∑ i, R l i * a i) e = ∑ i, algebraMap B Q (a i) • comb (fun l => R l i) e := by
  unfold comb
  simp only [map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem din_of_in {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] {f : MvPowerSeries σ Q}
    (hf : In (⊤ : Ideal B) f) : DIn (⊤ : Ideal B) f := fun α i => by
  obtain ⟨b, -, eb⟩ := hf α
  exact ⟨(α i : B) * b, Submodule.mem_top, by rw [eb, map_mul, map_natCast]⟩

end GlobalTheory.QLog.WindowMat
