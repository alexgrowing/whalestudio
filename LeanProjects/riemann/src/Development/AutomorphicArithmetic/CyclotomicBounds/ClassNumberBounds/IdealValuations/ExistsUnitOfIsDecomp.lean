import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.ExistsUnitDivConj
import Mathlib

open NumberField NumberField.IsCMField NumberField.Units IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.IdealValuations

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

private theorem pow_bijective_zmod {l M h : ℕ} (hh : h.Coprime l) :
    Function.Bijective (fun x : Multiplicative (ZMod (l ^ M)) => x ^ h) := by
  have hc : (Nat.card (Multiplicative (ZMod (l ^ M)))).Coprime h := by
    have : Nat.card (Multiplicative (ZMod (l ^ M))) = l ^ M := by
      rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod (l ^ M))), Nat.card_zmod]
    rw [this]
    exact Nat.Coprime.pow_left _ hh.symm
  exact (powCoprime hc).bijective

theorem IsDel.values {l M : ℕ} (hl : l.Prime) {ι : Type*} [Fintype ι]
    {B : MinusBasis K l ι} {v : HeightOneSpectrum (𝓞 K)}
    {om : (𝓞 K ⧸ v.asIdeal)ˣ →* Multiplicative (ZMod (l ^ M))}
    {del : primeTo v →* Multiplicative (ZMod (l ^ M))} (hdel : IsDel B v om del) :
    (∀ (α : Kˣ) (hα : toPrincipalIdeal (𝓞 K) K α ∈ primeTo v) (u : (locAt v.asIdeal)ˣ),
      ((u : locAt v.asIdeal) : K) = (α : K) / complexConj K (α : K) →
        del ⟨_, hα⟩ = om (residueUnit v.asIdeal u)) ∧
    (∀ A : primeTo v, (A : IdealGroup K) ∈ fromBase K → del A = 1) ∧
    (∀ (i : ι) (hi : B.aa i ∈ primeTo v), del ⟨_, hi⟩ = 1) := by
  classical
  have hbij := pow_bijective_zmod (M := M) B.h_coprime
  have hone : ∀ A : primeTo v, IsDecomp B.h B.aa (A : IdealGroup K) 1 → del A = 1 := by
    intro A hA
    apply hbij.1
    change del A ^ B.h = 1 ^ B.h
    rw [hdel A 1 hA 1 (by simp), map_one, map_one, one_pow]
  refine ⟨?_, ?_, ?_⟩
  · intro α hα u hu
    apply hbij.1
    change del ⟨_, hα⟩ ^ B.h = om (residueUnit v.asIdeal u) ^ B.h
    rw [← map_pow om, ← map_pow (residueUnit v.asIdeal)]
    refine hdel ⟨_, hα⟩ (α ^ B.h) ⟨0, 1, one_mem _, by simp⟩ _ ?_
    rw [Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hu, Units.val_pow_eq_pow_val, map_pow,
      div_pow]
  · intro A hA
    exact hone A ⟨0, (A : IdealGroup K) ^ B.h, pow_mem hA _, by simp⟩
  · intro i hi
    refine hone _ ⟨Pi.single i (B.h : ℤ), 1, one_mem _, ?_⟩
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp

end KStar.IdealValuations
