import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open GlobalTheory.HeckeApprox (inAf_sub inAf_nsmul inAf_mem inAfH)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

theorem betaH_holds : BetaH := by
  intro p _ D G L h κ n hn hnp hnκ hI hκ
  set u := L.actG h with hu
  set ui := L.actG h⁻¹ with hui
  have hinv : ∀ v, ui (u v) = v := by
    intro v
    rw [hu, hui, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ v, u (ui v) = v := by
    intro v
    rw [hu, hui, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hIu : ∀ v ∈ LaHat D, u v ∈ LaHat D := hI
  set h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := κ • ui with hh₀
  have h₀app : ∀ v, h₀ v = κ • ui v := fun v => rfl
  have h₀mem : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D := by
    intro v hv
    obtain ⟨v', hv', e⟩ := hκ v hv
    rw [h₀app, ← map_nsmul, ← e, hinv]
    exact hv'
  have h₀u : ∀ v, u (h₀ v) = κ • v := by
    intro v
    rw [h₀app, map_nsmul, hinv']
  have h₀c : ∀ (c : D.O) v, h₀ (actAf D c v) = actAf D c (h₀ v) := by
    intro c v
    rw [h₀app, h₀app, hui, actG_actAf, map_nsmul]
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.lattice_endomorphism_integral_approximation p D h₀ h₀mem
  obtain ⟨k, m, hkm⟩ : ∃ k : ℕ, ∃ m : ℤ, (κ : ℤ) * k = 1 + n * m := by
    have hc : Nat.Coprime κ n := hnκ.symm
    have e := Nat.gcd_eq_gcd_ab κ n
    rw [hc.gcd_eq_one] at e
    have hn' : (0:ℤ) < n := by exact_mod_cast hn
    refine ⟨(Nat.gcdA κ n % n).toNat, -(Nat.gcdB κ n) - κ * (Nat.gcdA κ n / n), ?_⟩
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne'), Int.emod_def]
    push_cast at e
    linear_combination -e
  have hsm : ∀ {M : Type} [AddCommGroup M] (y : M), (κ * k) • y = y + n • (m • y) := by
    intro M _ y
    have : (((κ * k : ℕ) : ℤ)) • y = ((1:ℤ) + n * m) • y := by push_cast; rw [hkm]
    rw [natCast_zsmul] at this
    rw [this, add_smul, one_smul, mul_smul, natCast_zsmul]
  have key : ∀ x, ∃ v ∈ LaHat D, u (inAf D (k • φ n x)) = inAf D x + n • v := by
    intro x
    obtain ⟨w, hw, e⟩ := hφ n hn hnp x
    refine ⟨m • inAf D x - k • u w, ?_, ?_⟩
    · exact sub_mem (zsmul_mem (inAf_mem D x) _) (nsmul_mem (hIu w hw) _)
    · have e2 : inAf D (φ n x) = h₀ (inAf D x) - n • w := by rw [e]; abel
      rw [inAf_nsmul, e2, map_nsmul, map_sub, h₀u, map_nsmul, smul_sub, smul_smul, mul_comm k κ, hsm,
        smul_sub n, smul_comm n k (u w)]
      abel
  have hg : ∀ x, (k • φ n) x = k • φ n x := fun x => rfl
  refine ⟨k • φ n, ?_, ?_, ?_, ?_⟩
  · intro c x
    rw [hg, hg]
    obtain ⟨w1, hw1, e1⟩ := hφ n hn hnp (c • x)
    obtain ⟨w2, hw2, e2⟩ := hφ n hn hnp x
    have a1 : inAf D (φ n (c • x)) = h₀ (inAf D (c • x)) - n • w1 := by rw [e1]; abel
    have a2 : inAf D (φ n x) = h₀ (inAf D x) - n • w2 := by rw [e2]; abel
    have hE : inAf D (k • φ n (c • x) - c • (k • φ n x)) = n • (k • (actAf D c w2 - w1)) := by
      rw [inAf_sub, inAf_nsmul, ← actAf_inAf, inAf_nsmul, map_nsmul, a1, a2, ← actAf_inAf, h₀c, map_sub,
        map_nsmul, smul_sub, smul_sub, smul_sub, smul_sub, smul_comm k n w1, smul_comm k n (actAf D c w2)]
      abel
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _
      (nsmul_mem (sub_mem (actAf_mem_laHat D c hw2) hw1) k) hE
    exact ⟨z, by rw [← hz]; abel⟩
  · intro x z hxz
    rw [hg] at hxz
    obtain ⟨v, hv, e⟩ := key x
    rw [hxz, inAf_nsmul, map_nsmul] at e
    have hx : inAf D x = n • (u (inAf D z) - v) := by rw [smul_sub, e]; abel
    exact LatDiv.eq_nsmul_of_inAf_eq_nsmul p D x n hn hnp _ (sub_mem (hIu _ (inAf_mem D z)) hv) hx
  · intro x
    obtain ⟨y, w, hw, e⟩ := exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp (u (inAf D x)) (hIu _ (inAf_mem D x))
    obtain ⟨v, hv, ev⟩ := key y
    have hd : inAf D (k • φ n y) - inAf D x = ui (n • (v - w)) := by
      rw [← hinv (inAf D (k • φ n y) - inAf D x), map_sub, ev, e]
      congr 1
      rw [smul_sub]
      abel
    have h1 : inAf D (κ • (k • φ n y - x)) = n • h₀ (v - w) := by
      rw [inAf_nsmul, inAf_sub, hd, map_nsmul, h₀app, smul_comm κ n]
    obtain ⟨z1, hz1⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _ (h₀mem _ (sub_mem hv hw)) h1
    refine ⟨y, k • z1 - m • (k • φ n y - x), ?_⟩
    have ht := hsm (k • φ n y - x)
    rw [mul_comm κ k, ← smul_smul, hz1] at ht
    rw [hg, smul_sub, smul_comm n k z1, ht]
    abel
  · intro x
    rw [hg]
    exact key x

end UpperTheory.Gal.FiniteEtaleModels
