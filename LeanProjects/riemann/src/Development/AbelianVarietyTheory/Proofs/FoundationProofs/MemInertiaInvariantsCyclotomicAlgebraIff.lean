import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInPrimitiveRootOfInertiaFixedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedCycModOfFixedCycZ
import Development.AbelianVarietyTheory.Definitions.Foundations.KumValUnique
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

theorem mem_cycAlg_iff : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : A, x ∈ cycAlg l A ↔ ∀ s ∈ ineCyc l A, s (x : Ω) = x := by
  intro l _ Ω _ _ _ A hA x
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hl : l.Prime := Fact.out
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  constructor
  · intro hx s hs
    obtain ⟨hsI, hsZ⟩ := mem_ineCyc.1 hs
    induction hx using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨n, hn⟩ := hz
      refine GlobalTheory.Col.fix_of_cycMod (l := l) (le_refl n) ?_ ?_
      · simp [cycMod, hsZ]
      · exact_mod_cast congrArg (fun a : A => (a : Ω)) hn
    | algebraMap r => exact r.2 s hsI
    | add a b _ _ ha hb =>
      show s ((a : Ω) + (b : Ω)) = (a : Ω) + (b : Ω)
      rw [map_add, ha, hb]
    | mul a b _ _ ha hb =>
      show s ((a : Ω) * (b : Ω)) = (a : Ω) * (b : Ω)
      rw [map_mul, ha, hb]
  · intro hx
    have hv : A.valuation (l : Ω) < 1 := by
      obtain ⟨v, hv, hl⟩ := hA
      have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hl
      simpa using h1
    obtain ⟨m, hm⟩ := GlobalTheory.fixed_cycMod_of_fixed_cycZ l Ω A hv ∅ (x : Ω)
      (fun s hs _ hz => hx s (mem_ineCyc.2 ⟨hs, hz⟩))
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hpos : 0 < l ^ m := pow_pos hl.pos m
    haveI : NeZero (l ^ m) := ⟨hpos.ne'⟩
    have hfix : ∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s (x : Ω) = x := by
      intro s hs hsζ
      refine hm s ⟨hs, by simp, ?_⟩
      have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ hζ.pow_eq_one
      have h2 : ζ ^ (PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])).val = ζ ^ 1 := by
        rw [pow_one]
        exact h1.symm.trans hsζ
      have h3 := (pow_eq_pow_iff_modEq (G := Ωˣ) (x := (hζ.isUnit hpos.ne').unit)
        (n := (PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])).val) (m := 1)).1 (by
          apply Units.ext
          simpa using h2)
      have h4 : orderOf (hζ.isUnit hpos.ne').unit = l ^ m := by
        rw [← orderOf_units, IsUnit.unit_spec]
        exact hζ.eq_orderOf.symm
      rw [h4, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, Nat.cast_one] at h3
      exact Units.ext h3
    obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.exists_polynomial_in_primitiveRoot_of_inertia_fixed l Ω A hA m ζ hζ (x : Ω) x.2 hfix
    have hζA : ζ ∈ A := mem_of_pow_mem A hpos.ne' (by rw [hζ.pow_eq_one]; exact A.one_mem)
    have hζc : (⟨ζ, hζA⟩ : A) ∈ cycAlg l A :=
      mem_cycAlg_of_pow (n := m) (Subtype.ext (by simpa using hζ.pow_eq_one))
    have e : x = ∑ d ∈ Finset.range (Q.natDegree + 1), (⟨Q.coeff d, (hQ d).1⟩ : A) * (⟨ζ, hζA⟩ : A) ^ d := by
      apply Subtype.ext
      rw [← hQe, Polynomial.eval_eq_sum_range]
      refine Eq.trans ?_ (map_sum A.subtype _ _).symm
      refine Finset.sum_congr rfl fun d _ => ?_
      simp
    rw [e]
    refine Subalgebra.sum_mem _ fun d _ => Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hζc d)
    exact (cycAlg l A).algebraMap_mem (⟨⟨Q.coeff d, (hQ d).1⟩, (hQ d).2⟩ : fixA A)

end GlobalTheory.RecOne
