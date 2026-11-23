import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCoeEqOfPowEqOne
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU

theorem wHom_ext (p : ℕ) [Fact p.Prime] (f g : Formalism.L2.G.Pend.WW p →+* ℂ_[p])
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1)
    (ht : ∀ y, f (WittVector.teichmuller p y) = g (WittVector.teichmuller p y)) (x : Formalism.L2.G.Pend.WW p) :
    f x = g x := by
  refine Formalism.L2.G.Pend.eq_of_close p fun N => ?_
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x N
  set S := ∑ i ∈ Finset.Iic N, (WittVector.teichmuller p
        (((_root_.frobeniusEquiv (Formalism.L2.G.Pend.kb p) p).symm ^ i) (x.coeff i)) * (p : Formalism.L2.G.Pend.WW p) ^ i) with hS
  have hfS : f S = g S := by
    rw [hS, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, ht]
  have hx : x = S + (p : Formalism.L2.G.Pend.WW p) ^ (N + 1) * c := by rw [← hc]; ring
  have hpC : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := Formalism.L2.G.Pend.norm_p_C p
  have e : f x - g x = (p : ℂ_[p]) ^ (N + 1) * (f c - g c) := by
    rw [hx, map_add, map_add, hfS, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]; ring
  rw [e, norm_mul, norm_pow, hpC]
  have h1 : ‖f c - g c‖ ≤ 1 := Formalism.L2.G.Pend.nsub p (hf c) (hg c)
  calc ((p : ℝ)⁻¹) ^ (N + 1) * ‖f c - g c‖ ≤ ((p : ℝ)⁻¹) ^ (N + 1) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((p : ℝ)⁻¹) ^ N * (p : ℝ)⁻¹ := by rw [mul_one, pow_succ]
    _ ≤ ((p : ℝ)⁻¹) ^ N * 1 := mul_le_mul_of_nonneg_left (Formalism.L2.G.Pend.r_lt_one p).le (by positivity)
    _ = ((p : ℝ)⁻¹) ^ N := mul_one _

theorem wToC_frob (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (hζ : ∀ (ζ : ℂ_[p]) (n : ℕ), 0 < n → Nat.Coprime n p → ζ ^ n = 1 → σ ζ = ζ ^ p) (x : FormalGroupSystem.WW p) :
    σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x) := by
  have := wHom_ext p (σ.comp (Formalism.L2.G.Pend.wToC p)) ((Formalism.L2.G.Pend.wToC p).comp (sigW p))
    (fun y => by rw [RingHom.comp_apply, hσ]; exact Formalism.L2.G.Pend.norm_wToC_le p y)
    (fun y => Formalism.L2.G.Pend.norm_wToC_le p _) (fun y => ?_) x
  · exact this
  · rw [RingHom.comp_apply, RingHom.comp_apply]
    have hs : sigW p (WittVector.teichmuller p y) = WittVector.teichmuller p (y ^ p) := by
      show WittVector.frobenius (WittVector.teichmuller p y) = _
      rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]
    rw [hs, map_pow (WittVector.teichmuller p), map_pow (Formalism.L2.G.Pend.wToC p)]
    by_cases hy : y = 0
    · subst hy
      rw [WittVector.teichmuller_zero, map_zero, map_zero, zero_pow (Fact.out : p.Prime).ne_zero]
    · obtain ⟨m, hm, hc, h1⟩ := Formalism.L2.G.Pend.exists_coprime_pow_eq_one p hy
      exact hζ _ m hm hc (by rw [← map_pow, ← map_pow, h1, map_one, map_one])

theorem exists_isFrob_wToC : ∀ (p : ℕ) [Fact p.Prime], ∃ σ : ℂ_[p] →+* ℂ_[p], GlobalTheory.ThBe0.IsFrob σ ∧
    ∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x) := by
  intro p _
  obtain ⟨g, hg⟩ := GlobalTheory.ThBe0.exists_gal_pow p
  have hζ : ∀ (ζ : ℂ_[p]) (n : ℕ), 0 < n → Nat.Coprime n p → ζ ^ n = 1 → Formalism.Per.σC g ζ = ζ ^ p := by
    intro ζ n hn hnl h
    obtain ⟨a, rfl, ha⟩ := GlobalTheory.ThBe0.exists_coe_eq_of_pow_eq_one p ζ n hn h
    rw [GlobalTheory.RingBasics.σC_coe, hg a n hnl ha]
    exact map_pow (algebraMap (PadicAlgCl p) ℂ_[p]) a p
  exact ⟨Formalism.Per.σC g, GlobalTheory.ThBe0.isFrob_of_rootOfUnity _ (GlobalTheory.RingBasics.norm_σC g) hζ,
    wToC_frob p _ (GlobalTheory.RingBasics.norm_σC g) hζ⟩

end GlobalTheory.TwU
