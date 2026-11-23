import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FrobFieldExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseIsogeny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKerIdealDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsogenyKernelFiniteAlgebraFinrankEqDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPartMulOfCoprimeAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelPartOrderPrimeToPStatement
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

open GlobalTheory.AV.KerPart in

theorem isIsog_hasLogDeg_map : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), IsIsogeny f → IsIsog (t.map t' f.hom) ∧ HasLogDeg (t.map t' f.hom) (padicValNat p (deg f)) := by
  intro p _ k _ A B G H t t' f hf
  have hp : p.Prime := Fact.out
  obtain ⟨N, g, hN, -, hfg, hgf⟩ := GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny k A B f hf
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.ne_one
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => hm (h0 ▸ dvd_zero p)
  have kill : ∀ {T : Over (Sp k)} (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ (p ^ a * m) = 1 :=
    fun x hx => pow_eq_one_of_comp hfg x hx
  refine ⟨?_, ?_⟩
  · have hu : IsUnit (m : ℤ_[p]) := by
      by_contra h
      have h1 : (m : ℤ_[p]) ∈ nonunits ℤ_[p] := h
      rw [PadicInt.mem_nonunits, PadicInt.norm_lt_one_iff_dvd] at h1
      obtain ⟨c, hc⟩ := h1
      have h2 := congrArg PadicInt.toZMod hc
      rw [map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul, ZMod.natCast_eq_zero_iff] at h2
      exact hm h2
    obtain ⟨u, hu⟩ := hu
    have hs : (↑u⁻¹ : ℤ_[p]) * ((p ^ a * m : ℕ) : ℤ_[p]) = (p : ℤ_[p]) ^ a := by
      push_cast
      rw [← hu, mul_left_comm, Units.inv_mul, mul_one]
    have eA : ((p ^ a * m) • 𝟙 A : A ⟶ A).hom = 𝟙 A.X ^ (p ^ a * m) := by simp
    have eB : ((p ^ a * m) • 𝟙 B : B ⟶ B).hom = 𝟙 B.X ^ (p ^ a * m) := by simp
    haveI : IsMonHom (𝟙 A.X ^ (p ^ a * m)) := eA ▸ inferInstance
    haveI : IsMonHom (𝟙 B.X ^ (p ^ a * m)) := eB ▸ inferInstance
    have h1 : t.map t' f.hom ≫ t'.map t g.hom = ((p ^ a * m : ℕ) : ℤ_[p]) • 𝟙 G := by
      rw [← TorsionTower.map_comp, ← t.map_pow_id]
      exact t.map_congr t (by rw [← comp_hom, hfg, eA])
    have h2 : t'.map t g.hom ≫ t.map t' f.hom = ((p ^ a * m : ℕ) : ℤ_[p]) • 𝟙 H := by
      rw [← TorsionTower.map_comp, ← t'.map_pow_id]
      exact t'.map_congr t' (by rw [← comp_hom, hgf, eB])
    refine ⟨a, (↑u⁻¹ : ℤ_[p]) • t'.map t g.hom, ?_, ?_⟩
    · rw [Linear.comp_smul, h1, smul_smul, hs]
    · rw [Linear.smul_comp, h2, smul_smul, hs]
  · obtain ⟨H₀, _, _, i₀, hK₀, hdeg⟩ := GlobalTheory.T.exists_isogeny_kernel_finite_algebra_finrank_eq_degree k A B f hf
    obtain ⟨Hm, _, _, im, hKm, hpm⟩ := GlobalTheory.T.exists_kernelPart_order_prime_to_p p k A B f m hm0 hm
    have hcop : (p ^ a).Coprime m := (Nat.Coprime.pow_left a ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)).symm))
    obtain ⟨H₁, _, _, i₁, hK₁, hrank⟩ := GlobalTheory.T.kernelPart_mul_of_coprime_abelianVariety k A B f (p ^ a) m hcop _ _ _ _ (kerPow_kerPt t t' f a) hKm
    have h01 : Module.finrank k H₁ = deg f := (finrank_eq_of_kerPow hK₁ hK₀ fun R _ _ x hx =>
      iff_of_true (kill x hx) (pow_zero x)).trans hdeg
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (finrank_quot_kerIdeal_dvd (t.map t' f.hom) a)
    have hv : padicValNat p (deg f) = j := by
      rw [← h01, hrank, hj, padicValNat.mul (pow_ne_zero _ hp.ne_zero) (fun h0 => hpm (by rw [h0]; exact dvd_zero p)),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hpm, add_zero]
    refine ⟨a, fun n hn => ?_⟩
    rw [hv, ← hj]
    refine finrank_eq_of_kerPow (kerPow_kerPt t t' f n) (kerPow_kerPt t t' f a) fun R _ _ x hx => ?_
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h2 := pow_gcd_eq_one.2 ⟨h, kill x hx⟩
      have h3 : (p ^ n).gcd (p ^ a * m) = p ^ a := by
        obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hn
        rw [pow_add, Nat.gcd_mul_left, (Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)), mul_one]
      rwa [h3] at h2
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, pow_mul, h, one_pow]

end GlobalTheory.Dieu
