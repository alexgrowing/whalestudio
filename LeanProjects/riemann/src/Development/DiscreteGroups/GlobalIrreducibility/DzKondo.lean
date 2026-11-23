import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzKLink
import Development.DiscreteGroups.GlobalIrreducibility.DzKName
import Development.DiscreteGroups.GlobalIrreducibility.OrbitOfAgree
import Development.DiscreteGroups.GlobalIrreducibility.DzKSchur
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut

open Polynomial GlobalTheory.CuspGL GlobalTheory.GLq GlobalTheory.Published

noncomputable section

namespace DiscreteGroups.sglob.DzType

open Kon

set_option linter.style.haveILetI false

theorem lKondo : LKondo := by
  intro g _ n hn2 hbig K _ _ hK ψ₀ hψ₀
  classical
  have hgp : g.Prime := Fact.out
  have hn0 : 0 < n := by omega
  have hKpos : 0 < Nat.card K := by rw [hK]; exact pow_pos hgp.pos _
  have : Finite K := Nat.finite_of_card_ne_zero hKpos.ne'
  let _ : Fintype K := Fintype.ofFinite K
  have : FiniteDimensional (ZMod g) K := Module.Finite.of_finite
  have hcard : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have hfr : Module.finrank (ZMod g) K = n := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod g) (V := K)
    rw [ZMod.card, hcard] at h1
    exact (Nat.pow_right_injective hgp.two_le h1).symm
  obtain ⟨θ₀, hθ₀, ι, kOf, hlink, τE, hτe, hτ1, hτ2, hex⟩ := named_family g n hn0 K hfr
  have hN : 0 < g ^ n - 1 := by have := Nat.one_lt_pow hn0.ne' hgp.one_lt; omega
  have hD0 : (∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    have hi1 := (Finset.mem_Ico.1 hi).1
    have h1 : ((g ^ i : ℕ) : ℂ) ≠ 1 := by
      rw [Ne, Nat.cast_eq_one]; exact (Nat.one_lt_pow (by omega) hgp.one_lt).ne'
    rw [sub_ne_zero]; exact_mod_cast h1
  have hGL : glCard (ZMod g) n ≠ 0 := by unfold glCard; exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hNc : ((g ^ n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hε : ((-1 : ℂ) ^ (n - 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  refine ⟨(-1) ^ (n - 1) * glCard (ZMod g) n / (((g ^ n - 1 : ℕ) : ℂ) * ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1)),
    div_ne_zero (mul_ne_zero hε hGL) (mul_ne_zero hNc hD0), ?_⟩
  intro θ hθ τ hτ hf
  have hname : ∀ x, τ.character x = τE θ x := by
    obtain ⟨θ', hθ', heq⟩ := hex τ.character hτ
    obtain ⟨i, hi, hii⟩ := orbit_of_agree hn2 hbig hK θ θ' hθ (fun z hz => by
      obtain ⟨y, hy, hzy⟩ := hz
      have e1 := hf y hy z hzy
      have e2 := (hτ1 θ' hθ').2.2 y hy z hzy
      rw [heq] at e1
      show fo g n θ z = fo g n θ' z
      exact mul_left_cancel₀ hε (e1.symm.trans e2))
    have h3 : τE θ = τE θ' := (hτ2 θ θ' hθ hθ').2 ⟨i, hi, hii⟩
    intro x; rw [heq, ← h3]
  have hsimple := simple_of_isIrr τ hτ.2.1
  let fψ : Gn g n → ℂ := fun y => ((ψ₀ (Matrix.trace (y : Mt g n)) : Circle) : ℂ)
  have hfcl : ∀ x y : Gn g n, fψ (y * x * y⁻¹) = fψ x := by
    intro x y
    simp only [fψ, Units.val_mul]
    rw [Matrix.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨c, hc1, hc2⟩ := central_scalar τ fψ hfcl
  have hdim : (Module.finrank ℂ τ : ℂ) = ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1) := by
    rw [← FDRep.char_one, hname, (hτ1 θ hθ).2.1]
  have hip := ipGL_psi_trace (F := ZMod g) (Fin n → ZMod g) (by rw [Module.finrank_fin_fun]; exact hn0) θ₀ hθ₀
    (kOf θ) (fun a => ((ψ₀ a : Circle) : ℂ))
  rw [Module.finrank_fin_fun] at hip
  rw [(GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties (ZMod g) n (fun _ => 0)).2.2.1, finsum_eq_sum_of_fintype] at hip
  have e : ∀ y : Gn g n, fψ y * τ.character y⁻¹ =
      star (psi (rootSum θ₀ (kOf θ)) (Fin n → ZMod g) (Matrix.toLin' (y : Mt g n)) *
        star ((ψ₀ (-(LinearMap.charpoly (Matrix.toLin' (y : Mt g n))).nextCoeff) : Circle) : ℂ)) * (-1) ^ (n - 1) := by
    intro y
    rw [GlobalTheory.BadShare.ZCalc.character_inv, hname, hτe, ← trace_eq_nextCoeff hn0]
    simp only [fψ, starRingEnd_apply, star_mul', star_pow, star_neg, star_one, star_star]
    ring
  have hsum : ∑ y : Gn g n, fψ y * τ.character y⁻¹ =
      (-1) ^ (n - 1) * glCard (ZMod g) n * aC n θ₀ (hT n fun a => ((ψ₀ a : Circle) : ℂ)) (kOf θ) := by
    rw [Finset.sum_congr rfl (fun y _ => e y), ← Finset.sum_mul, ← star_sum]
    rw [show (∑ y : Gn g n, psi (rootSum θ₀ (kOf θ)) (Fin n → ZMod g) (Matrix.toLin' (y : Mt g n)) *
        star ((ψ₀ (-(LinearMap.charpoly (Matrix.toLin' (y : Mt g n))).nextCoeff) : Circle) : ℂ)) =
        glCard (ZMod g) n * star (aC n θ₀ (hT n fun a => ((ψ₀ a : Circle) : ℂ)) (kOf θ)) from hip]
    rw [star_mul', star_star, glCard, star_natCast]
    ring
  have hgs := aC_eq_gs hn0 hK θ₀ ι θ (kOf θ) (hlink θ) ψ₀
  rw [hdim, hsum, hgs] at hc2
  have hcval : c = (-1) ^ (n - 1) * glCard (ZMod g) n /
      (((g ^ n - 1 : ℕ) : ℂ) * ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1)) * gs ψ₀ θ⁻¹ := by
    unfold gs
    have h4 : c = (c * ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1)) / ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1) := by
      field_simp
    rw [h4, hc2]
    field_simp
  intro v
  rw [finsum_eq_sum_of_fintype]
  exact (hc1 v).trans (by rw [hcval])

end DiscreteGroups.sglob.DzType
