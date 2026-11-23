import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

theorem level_good_and_sign : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ p : ℕ, p.Prime → Q.l.GoodAt p) ∧ Q.l.A = 1 ∧ ∀ τ : D.host.E →+* ℂ, τ (Q.H.rt : D.host.E) = Q.H.rt0 → (τ (-D.host.xi0)).im < 0 := by
  rintro D Q ⟨⟨-, hrt, hrt0, -⟩, ⟨hM, hA⟩, -, -⟩
  refine ⟨fun p hp => ?_, hA, fun τ hτ => ?_⟩
  · have hodd := Q.l.odd
    rw [hM] at hodd
    have h3 : ∀ a : ℕ, a.Prime → Odd a → 3 ≤ a := fun a ha ho => by
      have h2 := ha.two_le
      obtain ⟨k, hk⟩ := ho
      omega
    have ha := h3 _ (D.host.g_prime 0) (Nat.Odd.of_mul_left hodd)
    have hb := h3 _ (D.host.g_prime 1) (Nat.Odd.of_mul_right hodd)
    have hab : (D.host.g 0).Coprime (D.host.g 1) :=
      (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt
    have hM0 : Q.l.M ≠ 0 := by have := Q.l.three_le; omega
    have key : ∀ c, 3 ≤ c → c ∣ Q.l.M → ¬ p ∣ c → 3 ≤ Q.l.M / p ^ Q.l.M.factorization p :=
      fun c hc hd hn => hc.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd hn))
    by_cases h : p ∣ D.host.g 0
    · refine key _ hb (hM ▸ dvd_mul_left _ _) fun h' => hp.one_lt.ne' ?_
      exact Nat.eq_one_of_dvd_coprimes hab h h'
    · exact key _ ha (hM ▸ dvd_mul_right _ _) h
  · rw [hrt, hrt0] at hτ
    have h1 := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
    have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
      rw [hφ]
      have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
      simpa using hd
    rw [if_pos hpos, Int.cast_one, _root_.one_mul] at h1
    rw [map_neg, Complex.neg_im]
    linarith

end GlobalTheory.RecDict
