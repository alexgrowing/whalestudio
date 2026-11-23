import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationOfDerivationOnLargeSubalgebra
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

noncomputable section

namespace GlobalTheory.RecOne

def decRingHom {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (s : G ℚ Ω)
    (hs : s ∈ Dec (F := ℚ) A) : A →+* A where
  toFun x := ⟨s x, (apply_mem_iff_of_mem_Dec hs (x : Ω)).2 x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

def TwDiff {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (_τ : A →+* A) : Type :=
  KaehlerDifferential (fixA A) A

instance {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : A →+* A) :
    AddCommGroup (TwDiff A τ) :=
  inferInstanceAs (AddCommGroup (KaehlerDifferential (fixA A) A))

instance {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : A →+* A) :
    Module A (TwDiff A τ) :=
  Module.compHom (KaehlerDifferential (fixA A) A) τ

theorem transp_rel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (s : G ℚ Ω),
    s ∈ Ine (F := ℚ) A → ∀ a b a' b' c d c' d' : A, (c : Ω) = s a → (d : Ω) = s b →
    (c' : Ω) = s a' → (d' : Ω) = s b' → a • dA A b = a' • dA A b' → c • dA A d = c' • dA A d' := by
  intro Ω _ _ A s hs a b a' b' c d c' d' hc hd hc' hd' h
  set τ := decRingHom A s (Ine_le_Dec A hs) with hτ
  have hτc : τ a = c := Subtype.ext hc.symm
  have hτd : τ b = d := Subtype.ext hd.symm
  have hτc' : τ a' = c' := Subtype.ext hc'.symm
  have hτd' : τ b' = d' := Subtype.ext hd'.symm
  obtain ⟨T, hT⟩ := kaehler_rel_local (fixA A) A 2 ![a, -a'] ![b, b']
    (by simp [Fin.sum_univ_two, h])
  let D : A → TwDiff A τ := fun x => (dA A (τ x) : KaehlerDifferential (fixA A) A)
  have hD : IsDerOn (⊤ : Subalgebra (fixA A) A) D :=
    { add := fun x _ y _ => by
        show dA A (τ (x + y)) = dA A (τ x) + dA A (τ y)
        rw [map_add, map_add]
      mul := fun x _ y _ => by
        show dA A (τ (x * y)) = τ x • dA A (τ y) + τ y • dA A (τ x)
        rw [map_mul, Derivation.leibniz]
      alg := fun r => by
        show dA A (τ (algebraMap (fixA A) A r)) = 0
        have e : τ (algebraMap (fixA A) A r) = algebraMap (fixA A) A r :=
          Subtype.ext (r.2 s hs)
        rw [e, Derivation.map_algebraMap] }
  have key := hT ⊤ (by simp) (by simp) (TwDiff A τ) D hD
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at key
  change τ a • dA A (τ b) + τ (-a') • dA A (τ b') = (0 : KaehlerDifferential (fixA A) A) at key
  rw [map_neg, hτc, hτd, hτc', hτd', neg_smul, ← sub_eq_add_neg, sub_eq_zero] at key
  exact key

end GlobalTheory.RecOne
