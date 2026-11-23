import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing

namespace GlobalTheory

theorem localSubalgebra_eval_sub_mem_maximalIdeal {X O : Type} [CommRing O] [IsLocalRing O]
    (T : Subalgebra O (X → O)) [IsLocalRing T] {f : X → O} (hf : f ∈ T) (x y : X) :
    f x - f y ∈ IsLocalRing.maximalIdeal O := by
  classical
  haveI : (IsLocalRing.maximalIdeal O).IsMaximal := IsLocalRing.maximalIdeal.isMaximal O
  letI : Field (O ⧸ IsLocalRing.maximalIdeal O) := Ideal.Quotient.field _
  let ψ : X → (T →+* O ⧸ IsLocalRing.maximalIdeal O) := fun z =>
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp
      ((Pi.evalRingHom (fun _ : X => O) z).comp (T.val : T →+* (X → O)))
  have hψ : ∀ z (g : T), ψ z g = Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) ((g : X → O) z) :=
    fun _ _ => rfl
  have hsurj : ∀ z, Function.Surjective (ψ z) := by
    intro z q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨algebraMap O T a, by rw [hψ]; rfl⟩
  have hker : ∀ z, RingHom.ker (ψ z) = IsLocalRing.maximalIdeal T := fun z =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (hsurj z))
  have hg : (⟨f, hf⟩ - algebraMap O T (f y) : T) ∈ RingHom.ker (ψ y) := by
    rw [RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem]
    simp
  rw [hker y, ← hker x, RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem] at hg
  simpa using hg

theorem hensel_roots_of_local_family : ∀ {X O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [HenselianRing O (IsLocalRing.maximalIdeal O)] {t : ℕ} (T : Subalgebra O (X → O)), IsLocalRing T → ∀ (P : X → Polynomial O), (∀ j, (fun x => (P x).coeff j) ∈ T) → (∀ x, (P x).Monic ∧ (P x).natDegree = t) → ∀ (π : X) (d : Fin t → O), (∀ a b, a ≠ b → IsUnit (d a - d b)) → P π = ∏ c, (Polynomial.X - Polynomial.C (d c)) → ∀ x, ∃ β : Fin t → O, Function.Injective β ∧ P x = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  classical
  intro X O _ _ _ _ t T hT P hcoeff hdeg π d hd hπ x
  have hmap : (P x).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) =
      (P π).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) := by
    ext j
    simp only [Polynomial.coeff_map]
    rw [Ideal.Quotient.eq]
    exact localSubalgebra_eval_sub_mem_maximalIdeal T (hcoeff j) x π
  have hroot : ∀ c, ∃ b, (P x).IsRoot b ∧ b - d c ∈ IsLocalRing.maximalIdeal O := by
    intro c
    apply HenselianRing.is_henselian (P x) (hdeg x).1 (d c)
    · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
        hmap, hπ, Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_prod,
        Finset.prod_eq_zero (Finset.mem_univ c) (by simp), map_zero]
    · rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← Polynomial.derivative_map, hmap,
        Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
      apply IsUnit.map
      rw [hπ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
        Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero,
        Polynomial.eval_prod]
      have : ∀ a ∈ Finset.univ.erase c, IsUnit (d c - d a) := fun a ha =>
        hd c a (Finset.ne_of_mem_erase ha).symm
      exact IsUnit.prod_iff.2 this
  choose β hβ hβm using hroot
  have hinj : Function.Injective β := by
    intro a b hab
    by_contra hne
    have hmem : d b - d a ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ (hβm a) (hβm b)
      rw [hab] at this
      convert this using 1; ring
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (hd b a (Ne.symm hne))
  refine ⟨β, hinj, ?_⟩
  have hx0 : P x ≠ 0 := (hdeg x).1.ne_zero
  have hle : (Finset.univ.val.map β) ≤ (P x).roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map hinj Finset.univ.nodup)]
    intro r hr
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp hr
    exact (Polynomial.mem_roots hx0).mpr (hβ c)
  have hcard : (P x).roots.card ≤ (Finset.univ.val.map β).card := by
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, ← (hdeg x).2]
    exact Polynomial.card_roots' _
  have heq : Finset.univ.val.map β = (P x).roots := Multiset.eq_of_le_of_card_le hle hcard
  have hrc : (P x).roots.card = (P x).natDegree := by
    rw [← heq, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, (hdeg x).2]
  rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hdeg x).1 hrc, ← heq,
    Multiset.map_map]
  rfl

end GlobalTheory
