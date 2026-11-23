import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsPadicIntMatrixChangeStatement

noncomputable section

namespace GlobalTheory.MomN

open GlobalTheory.MomOne PowerSeries
open scoped ComplexConjugate

theorem exists_padicInt_inv {q : ℕ} [Fact q.Prime] {s : ℕ} (h : Nat.Coprime s q) :
    ∃ u : ℤ_[q], (s : ℤ_[q]) * u = 1 := by
  have h1 : IsUnit (s : ℤ_[q]) := by
    rw [PadicInt.isUnit_iff]
    have hq : ¬ (q : ℤ) ∣ (s : ℤ) := by
      intro hd
      have hd' : q ∣ s := Int.natCast_dvd_natCast.mp hd
      have : q ∣ 1 := by
        have := Nat.dvd_gcd hd' (dvd_refl q)
        rwa [h] at this
      exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp this)
    have h2 := (PadicInt.norm_int_lt_one_iff_dvd (p := q) (s : ℤ)).not.mpr hq
    have h3 : ‖((s : ℤ) : ℤ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
    have h4 : ‖((s : ℤ) : ℤ_[q])‖ = 1 := le_antisymm h3 (not_lt.mp h2)
    simpa using h4
  obtain ⟨u, hu⟩ := h1
  exact ⟨((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]), by rw [← hu]; simp⟩

theorem latInt_of_span : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (d : ℕ) (ω : ℂ_[q]) (Λ : AddSubgroup V) (κ : Type) [Fintype κ] (b : κ → V) (G : V → ℂ), d.Prime → d % 16 = 7 → Split d q → (∀ x ∈ Λ, ∃ s : ℕ, Nat.Coprime s q ∧ ∃ c : κ → ℂ, (∀ i, InOK d (c i)) ∧ (s : ℂ) • x = ∑ i, c i • b i) → MomInt ι (fun i => ι.symm ω • b i) G → LatInt ι ω Λ G := by
  intro q _ ι V _ _ d ω Λ κ _ b G hd h16 hS hspan hM κ' _ v hv
  have hOK := GlobalTheory.MomOne.okArith d q ι hd h16 hS
  choose s hs c hc hx using fun i => hspan (v i) (hv i)
  have ha : ∀ i j, ∃ a : ℤ_[q], ι (c i j) = zc a := fun i j => (hOK.2.1 _ (hc i j)).1
  choose a ha using ha
  choose u hu using fun i => exists_padicInt_inv (q := q) (hs i)
  have hs0 : ∀ i, (s i : ℂ) ≠ 0 := by
    intro i h0
    have h1 : s i = 0 := by exact_mod_cast h0
    have := hu i
    rw [h1] at this
    simp at this
  have hzu : ∀ i, (s i : ℂ_[q]) * zc (u i) = 1 := by
    intro i
    have := congrArg (zc (q := q)) (hu i)
    simpa [zc] using this
  refine GlobalTheory.T.jetsAreBoundedMeasureMoments_padicInt_matrix_change q ι V κ κ' (fun i => ι.symm ω • b i) (fun i => ι.symm ω • v i)
    (fun i j => c i j / s i) (fun i j => a i j * u i) G ?_ ?_ hM
  · intro i j
    have hsq : (s i : ℂ_[q]) ≠ 0 := fun h0 => by
      have := hzu i
      rw [h0] at this
      simp at this
    have e1 : zc (a i j * u i) = zc (a i j) * zc (u i) := by simp [zc]
    rw [map_div₀, ha, map_natCast, e1, div_eq_iff hsq, mul_assoc, mul_comm (zc (u i)), hzu, mul_one]
  · intro i
    have e : v i = (s i : ℂ)⁻¹ • ∑ j, c i j • b j := by
      rw [← hx i, smul_smul, inv_mul_cancel₀ (hs0 i), one_smul]
    conv_lhs => rw [e]
    rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [smul_smul]
    congr 1
    field_simp [hs0 i]

end GlobalTheory.MomN
