import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalCharacterIdealPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrderPullbackAlongHom
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.BoundedDen

theorem den_factorization_le (p : ℕ) [Fact p.Prime] (q : ℚ) (M : ℕ) (hM : 0 < M) (k : ℤ) (e : ℕ)
    (h : q * ((M : ℚ) * (p : ℚ) ^ e) = k) (ℓ : ℕ) (hℓ : ℓ ≠ p) :
    q.den.factorization ℓ ≤ M.factorization ℓ := by
  have hp : p.Prime := Fact.out
  have hN : ((M * p ^ e : ℕ) : ℚ) ≠ 0 := by
    have : 0 < M * p ^ e := Nat.mul_pos hM (pow_pos hp.pos e)
    exact_mod_cast this.ne'
  have hq : q = Rat.divInt k ((M * p ^ e : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast at hN ⊢
    rw [eq_div_iff hN]; exact h
  have hd : q.den ∣ M * p ^ e := by
    have := Rat.den_dvd k ((M * p ^ e : ℕ) : ℤ)
    rw [← hq] at this
    exact_mod_cast this
  have hle := (Nat.factorization_le_iff_dvd q.den_nz (Nat.mul_pos hM (pow_pos hp.pos e)).ne').2 hd ℓ
  rw [Nat.factorization_mul hM.ne' (pow_pos hp.pos e).ne', Nat.factorization_pow, hp.factorization] at hle
  simpa [Finsupp.single_apply, Ne.symm hℓ] using hle

end GlobalTheory.LKCx.BoundedDen

namespace GlobalTheory.LKCx.BoundedDen

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (h₁ : G.GAf), ∃ D : ℕ, 0 < D ∧ ∀ y : grp G β, f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → ∀ ℓ : ℕ, ℓ ≠ p → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization ℓ ≤ D.factorization ℓ) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization ℓ ≤ D.factorization ℓ := by
  intro p _ G β x t hx L f hf h₁
  obtain ⟨Ω, Ω', hΩ, hΩ', hmem⟩ := exists_compact_toAfF p G L f hf β x t hx h₁
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  let b := Module.finBasis ℚ G.C
  let b' := b.baseChange (AfP p)
  have hcpt : ∀ i, IsCompact ((b'.coord i) '' Ω) := fun i =>
    hΩ.image (IsModuleTopology.continuous_of_linearMap (b'.coord i))
  choose m hm0 hm using fun i => GlobalTheory.DenAway.den_bounded_of_isCompact p _ (hcpt i)
  obtain ⟨M', hM'0, hM'⟩ := GlobalTheory.DenAway.den_bounded_of_isCompact p Ω' hΩ'
  refine ⟨(∏ i, m i) * M', Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0, fun y hy ℓ hℓ => ⟨fun i => ?_, ?_⟩⟩
  · have hval : b'.coord i (inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) =
        algebraMap ℚ (AfP p) (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i) := by
      simp only [inC, b', RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Module.Basis.coord_apply,
        Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    obtain ⟨k, e, hk⟩ := hm i (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i) (by rw [← hval]; exact ⟨_, (hmem y hy).1, rfl⟩)
    have h1 := den_factorization_le p _ (m i) (hm0 i) k e hk ℓ hℓ
    have hd : m i ∣ (∏ j, m j) * M' := (Finset.dvd_prod_of_mem m (Finset.mem_univ i)).mul_right _
    exact h1.trans ((Nat.factorization_le_iff_dvd (hm0 i).ne'
      (Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0).ne').2 hd ℓ)
  · have e0 : ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ) = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ := Units.val_inv_eq_inv_val _
    obtain ⟨k, e, hk⟩ := hM' _ (hmem y hy).2
    rw [e0]
    have h1 := den_factorization_le p _ M' hM'0 k e hk ℓ hℓ
    exact h1.trans ((Nat.factorization_le_iff_dvd hM'0.ne'
      (Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0).ne').2 (dvd_mul_left _ _) ℓ)

end GlobalTheory.LKCx.BoundedDen
