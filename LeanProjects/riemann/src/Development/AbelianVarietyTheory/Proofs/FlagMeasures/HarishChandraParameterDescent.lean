import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraCentralActionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtendSpecialUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfinitesimalCharacterExtensionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtensionPreservesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtensionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightsOfExtensionStatement

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SUtoU

variable {n : ℕ}

theorem rhoNh_sub_const (ε : Fin n → Bool) (lam : Fin n → ℝ) (c : ℝ) :
    rhoNh ε (fun a => lam a - c) = rhoNh ε lam := by
  funext a
  simp only [rhoNh, sub_lt_sub_iff_right]

theorem rhoCh_sub_const (ε : Fin n → Bool) (lam : Fin n → ℝ) (c : ℝ) :
    rhoCh ε (fun a => lam a - c) = rhoCh ε lam := by
  funext a
  simp only [rhoCh, sub_lt_sub_iff_right]

theorem lowCh_sub_const (ε : Fin n → Bool) (lam : Fin n → ℝ) (c : ℝ) :
    lowCh ε (fun a => lam a - c) = fun a => lowCh ε lam a - c := by
  funext a
  simp only [lowCh, rhoNh_sub_const, rhoCh_sub_const, Pi.add_apply, Pi.sub_apply]
  ring

theorem exists_sum_eq_int (hn : 1 ≤ n) (lam : Fin n → ℝ) (hU : IsParU lam) :
    ∃ m : ℤ, ∑ a, lam a = (m : ℝ) := by
  choose k hk using hU.2
  obtain ⟨t, ht⟩ := Nat.even_mul_pred_self n
  refine ⟨(t : ℤ) + ∑ a, k a, ?_⟩
  have hlam : ∀ a, lam a = ((n : ℝ) - 1) / 2 + (k a : ℝ) := fun a => by linarith [hk a]
  have hcast : (n : ℝ) * ((n : ℝ) - 1) = 2 * (t : ℝ) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) ht
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hn, Nat.cast_one] at this
    linarith
  simp only [hlam, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  linarith

theorem extension_main : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsParU lam → ∃ m : ℤ, ∑ a, lam a = (m : ℝ) ∧ IsParS (fun a => lam a - (m : ℝ) / n) ∧ (IsHCS ε (fun a => lam a - (m : ℝ) / n) π' → ∃ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), Ext ε m π' π ∧ IsHCU ε lam π) := by
  intro n hn ε H _ _ π' lam hU
  obtain ⟨m, hm⟩ := exists_sum_eq_int hn lam hU
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨m, hm, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Finset.sum_sub_distrib, hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  · intro a b h
    exact hU.1 (by simpa using h)
  · intro a b
    obtain ⟨ka, hka⟩ := hU.2 a
    obtain ⟨kb, hkb⟩ := hU.2 b
    exact ⟨ka - kb, by push_cast; linarith⟩
  · intro hS
    obtain ⟨⟨hcomp, hnt, hrep, hirr, hsq⟩, hinf, ⟨S0, hS0, huniq⟩, habove⟩ := hS
    have hcent := GlobalTheory.T.harish_chandra_central_action n hn ε H π' lam m hU hm ⟨⟨hcomp, hnt, hrep, hirr, hsq⟩, hinf, ⟨S0, hS0, huniq⟩, habove⟩
    obtain ⟨π, hext, hrepU⟩ := GlobalTheory.T.extend_special_unitary_rep n hn ε H m π' hrep hcent
    refine ⟨π, hext, ?_⟩
    obtain ⟨-, hirrIff, -, -⟩ := GlobalTheory.T.extension_preserves_properties n hn ε H m π' π hext
    have hsqIff := GlobalTheory.T.square_integrable_iff_extension n hn ε H m π' π hext hrepU
    have hinfU := GlobalTheory.T.infinitesimal_character_extension n hn ε H m π' π hext _ hinf
    obtain ⟨-, hKT⟩ := GlobalTheory.T.weights_of_extension n hn ε H m π' π hext
    have hlow := lowCh_sub_const ε lam ((m : ℝ) / n)
    have hsumLow : ∑ a, lowCh ε lam a = (m : ℝ) := by
      have h0 := hS0.1
      rw [hlow, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at h0
      field_simp at h0
      linarith
    have hKTlow : ∀ S : Submodule ℂ H, IsKTypeU ε lam π (lowCh ε lam) S ↔
        IsKTypeS ε (fun a => lam a - (m : ℝ) / n) π' (lowCh ε (fun a => lam a - (m : ℝ) / n)) S := by
      intro S
      rw [hKT lam (lowCh ε lam) ((m : ℝ) / n) S, hlow]
      exact ⟨fun h => h.2, fun h => ⟨hsumLow, h⟩⟩
    refine ⟨⟨hcomp, hnt, hrepU, hirrIff.2 hirr, hsqIff.2 hsq⟩, ?_, ⟨S0, (hKTlow S0).2 hS0, fun S hS => huniq S ((hKTlow S).1 hS)⟩, ?_⟩
    · convert hinfU using 2 with a
      push_cast
      field_simp
      ring
    · intro μ S hμS
      obtain ⟨-, hμS'⟩ := (hKT lam μ ((m : ℝ) / n) S).1 hμS
      obtain ⟨c, hc, heq⟩ := habove _ S hμS'
      refine ⟨c, fun a b hab => by simpa using hc a b hab, ?_⟩
      funext a
      have := congrFun heq a
      rw [hlow] at this
      simp only [Pi.add_apply] at this ⊢
      linarith

end GlobalTheory.SUtoU

end
