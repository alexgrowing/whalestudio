import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockEmbeddingFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFamilyOfRealised
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldAbelianByPrimePower
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfVirtualAndCharacter
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersOfAbelianByPrimePower
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.AsAlgebraHomSurjectiveOfFinrankIntertwiningMapEq
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingCharacterEqFinrankInte
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClos
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterExtendScalarsRep
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrredu

noncomputable section

namespace GlobalTheory.GoodFamily

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.BI GlobalTheory.GoodCharsCompare Formalism.MainNotions.PrimeDegreeVariant
open scoped MonoidAlgebra

section Characters

theorem irreducible_of_surjective {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [Nontrivial V]
    (ρ : Representation k G V) (h : Function.Surjective ρ.asAlgebraHom) : ρ.IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  refine ⟨fun S => ?_⟩
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
  · refine Or.inr (Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun w _ => ?_))
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hv0
    obtain ⟨a, ha⟩ := h (LinearMap.smulRight φ w)
    have hw : ρ.asAlgebraHom a v = w := by rw [ha]; simp [hφ]
    rw [← hw]
    clear hw ha
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, LinearMap.add_apply]; exact S.toSubmodule.add_mem hx hy
    | single t c =>
      rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
      exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule t hv)

theorem irreducible_extend (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] {G : Type} [Group G]
    [Finite G] {n : ℕ} (ρ : Representation K G (Fin n → K))
    (h : Module.finrank K (Representation.IntertwiningMap ρ ρ) = 1) : (extendScalarsRep K L ρ).IsIrreducible := by
  have h1 := pair_character_eq_finrank K L G _ _ ρ ρ
  have h2 := pair_character_eq_finrank L L G _ _ (extendScalarsRep K L ρ) (extendScalarsRep K L ρ)
  simp only [character_extendScalarsRep, Algebra.algebraMap_self, RingHom.id_apply] at h2
  rw [h1, h] at h2
  obtain ⟨h3, h4⟩ := GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one L G _ (extendScalarsRep K L ρ)
    (by exact_mod_cast h2.symm)
  exact irreducible_of_surjective _ h4

theorem norm_one_prod {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)] {χ : ∀ i, G i → ℂ}
    (h : ∀ i, IsChar ℂ ℂ (χ i) ∧ pair (χ i) (χ i) = 1) :
    IsChar ℂ ℂ (fun t : ∀ i, G i => ∏ i, χ i (t i)) ∧
      pair (fun t : ∀ i, G i => ∏ i, χ i (t i)) (fun t => ∏ i, χ i (t i)) = 1 := by
  classical
  constructor
  · have : ∀ s : Finset ι, IsChar ℂ ℂ (fun t : ∀ i, G i => ∏ i ∈ s, χ i (t i)) := by
      intro s
      induction s using Finset.induction with
      | empty => simpa using isChar_one ℂ ℂ (∀ i, G i)
      | insert a s ha ih =>
        obtain ⟨n, ρ, hρ⟩ := (h a).1
        have h1 : IsChar ℂ ℂ (fun t : ∀ i, G i => χ a (t a)) := ⟨n, ρ.comp (Pi.evalMonoidHom G a), fun t => hρ (t a)⟩
        have := isChar_mul_complex h1 ih
        convert this using 1
        funext t
        rw [Finset.prod_insert ha]; rfl
    exact this _
  · letI : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
    have h2 : ∏ i, pair (χ i) (χ i) = 1 := Finset.prod_eq_one fun i _ => (h i).2
    rw [← h2]
    simp only [pair, finsum_eq_sum_of_fintype, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    rw [Nat.card_pi, Nat.cast_prod, Fintype.prod_sum]
    simp only [Finset.prod_mul_distrib, Pi.inv_apply]

end Characters

section Local

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues

variable {g : ℕ} [Fact g.Prime] {r : ℕ}

end Local

section Global

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues

end Global

end GlobalTheory.GoodFamily
