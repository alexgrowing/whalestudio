import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem isSquare_or_isSquare_neg_of_mod_four {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3)
    {a : ZMod p} (ha : a ≠ 0) : IsSquare a ∨ IsSquare (-a) := by
  by_cases hs : IsSquare a
  · exact Or.inl hs
  · right
    have h1 : quadraticChar (ZMod p) a = -1 := (quadraticChar_neg_one_iff_not_isSquare).2 hs
    have hm1 : ¬ IsSquare (-1 : ZMod p) := by
      rw [ZMod.exists_sq_eq_neg_one_iff]; omega
    have h2 : quadraticChar (ZMod p) (-1) = -1 := (quadraticChar_neg_one_iff_not_isSquare).2 hm1
    have h4 : quadraticChar (ZMod p) (-a) = 1 := by
      rw [neg_eq_neg_one_mul, map_mul, h1, h2]; norm_num
    exact (quadraticChar_one_iff_isSquare (neg_ne_zero.2 ha)).1 h4

theorem sq_perm_mul :
    ∀ (p c : ℕ), p.Prime → p % 4 = 3 → ¬ p ∣ c → ∃ (e : Sq p ≃ Sq p) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
      ∀ k : Sq p, (p : ℤ) ∣ (((k.1 : ℕ) : ℤ) * c - ε * (((e k).1 : ℕ) : ℤ)) := by
  intro p c hp h3 hc
  haveI : Fact p.Prime := ⟨hp⟩
  have hc0 : ((c : ℕ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  obtain ⟨ε, hε, hsq⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsSquare ((ε : ZMod p) * (c : ZMod p)) := by
    rcases isSquare_or_isSquare_neg_of_mod_four h3 hc0 with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h⟩
  set s : ZMod p := (ε : ZMod p) * (c : ZMod p) with hs
  have hε2 : (ε : ZMod p) * (ε : ZMod p) = 1 := by
    rcases hε with h | h <;> subst h <;> simp
  have hs0 : s ≠ 0 := by
    intro h0
    have : (ε : ZMod p) * s = 0 := by rw [h0, mul_zero]
    rw [hs, ← mul_assoc, hε2, one_mul] at this
    exact hc0 this
  let f : Sq p → Sq p := fun k =>
    ⟨⟨(s * ((k.1 : ℕ) : ZMod p)).val, ZMod.val_lt _⟩, by
      simp only [ZMod.natCast_val, ZMod.cast_id', id]
      exact ⟨mul_ne_zero hs0 k.2.1, hsq.mul k.2.2⟩⟩
  have hf : ∀ k, (((f k).1 : ℕ) : ZMod p) = s * ((k.1 : ℕ) : ZMod p) := by
    intro k; simp [f]
  have hinj : Function.Injective f := by
    intro k₁ k₂ h
    have h' : s * ((k₁.1 : ℕ) : ZMod p) = s * ((k₂.1 : ℕ) : ZMod p) := by
      rw [← hf, ← hf, h]
    have h'' := mul_left_cancel₀ hs0 h'
    apply Subtype.ext; apply Fin.ext
    have := congrArg ZMod.val h''
    rwa [ZMod.val_cast_of_lt k₁.1.2, ZMod.val_cast_of_lt k₂.1.2] at this
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.1 hinj
  refine ⟨Equiv.ofBijective f hbij, ε, hε, fun k => ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [Equiv.ofBijective_apply, hf, hs]
  linear_combination (-(((k.1 : ℕ) : ZMod p) * (c : ZMod p))) * hε2

end GlobalTheory.CMModel
