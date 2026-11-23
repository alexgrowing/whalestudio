import Mathlib
import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog

open NumberField IntermediateField
open scoped GroundTheory.LocalField.Abstract ComplexConjugate

namespace GroundTheory.Global

namespace Cyclotomic

open GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

section UnitsDegree

theorem continuous_unitsPadicEquiv_apply (q : Nat.Primes) :
    Continuous fun u : ℤ̂ˣ => unitsPadicEquiv u q := by
  simp_rw [unitsPadicEquiv_apply]
  rw [Units.continuous_iff]
  exact ⟨(continuous_toPadicInt q).comp Units.continuous_val,
    (continuous_toPadicInt q).comp Units.continuous_coe_inv⟩

noncomputable def unitsDegree : ℤ̂ˣ →* Multiplicative ℤ̂ where
  toFun u := Multiplicative.ofAdd
    (ofPadics fun q => Multiplicative.toAdd (padicUnitsLog q (unitsPadicEquiv u q)))
  map_one' := by
    rw [show (fun q : Nat.Primes => Multiplicative.toAdd (padicUnitsLog q (unitsPadicEquiv 1 q))) =
      0 from funext fun q => by simp, map_zero, ofAdd_zero]
  map_mul' u v := by
    rw [← ofAdd_add, ← map_add]
    congr 2
    funext q
    simp

theorem toPadicInt_unitsDegree (u : ℤ̂ˣ) (q : Nat.Primes) :
    toPadicInt q (Multiplicative.toAdd (unitsDegree u)) =
      Multiplicative.toAdd (padicUnitsLog q (unitsPadicEquiv u q)) :=
  congrFun (toPadics_ofPadics _) q

theorem continuous_unitsDegree : Continuous unitsDegree :=
  continuous_ofAdd.comp (continuous_ofPadics.comp (continuous_pi fun q =>
    continuous_toAdd.comp ((continuous_padicUnitsLog q).comp
      (continuous_unitsPadicEquiv_apply q))))

theorem unitsDegree_surjective : Function.Surjective unitsDegree := by
  intro y
  choose g hg using fun q : Nat.Primes =>
    padicUnitsLog_surjective q (Multiplicative.ofAdd (toPadicInt q (Multiplicative.toAdd y)))
  refine ⟨unitsPadicEquiv.symm g, Multiplicative.toAdd.injective (ext_toPadicInt fun q => ?_)⟩
  rw [toPadicInt_unitsDegree, MulEquiv.apply_symm_apply, hg, toAdd_ofAdd]

theorem unitsDegree_eq_one_iff (u : ℤ̂ˣ) :
    unitsDegree u = 1 ↔ ∀ q : Nat.Primes, unitsPadicEquiv u q ∈ CommGroup.torsion ℤ_[q]ˣ := by
  simp_rw [← ker_padicUnitsLog, MonoidHom.mem_ker]
  constructor
  · intro h q
    have := toPadicInt_unitsDegree u q
    rw [h, toAdd_one, map_zero] at this
    exact congrArg Multiplicative.ofAdd this.symm
  · intro h
    refine Multiplicative.toAdd.injective (ext_toPadicInt fun q => ?_)
    rw [toPadicInt_unitsDegree, h q, toAdd_one, toAdd_one, map_zero]

theorem unitsDegree_eq_one_of_pow_eq_one {u : ℤ̂ˣ} {k : ℕ} (hk : 0 < k) (h : u ^ k = 1) :
    unitsDegree u = 1 := by
  rw [unitsDegree_eq_one_iff]
  intro q
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨k, hk, ?_⟩
  rw [← Pi.pow_apply, ← map_pow, h, map_one, Pi.one_apply]

theorem unitsDegree_neg_one : unitsDegree (-1) = 1 :=
  unitsDegree_eq_one_of_pow_eq_one two_pos (by rw [neg_one_sq])

end UnitsDegree

section Degree

noncomputable def degree : Gal(ℚ̄/ℚ) →* Multiplicative ℤ̂ :=
  unitsDegree.comp character

theorem degree_apply (σ : Gal(ℚ̄/ℚ)) : degree σ = unitsDegree (character σ) :=
  rfl

theorem continuous_degree : Continuous degree :=
  continuous_unitsDegree.comp continuous_character

theorem degree_surjective : Function.Surjective degree :=
  unitsDegree_surjective.comp character_surjective

theorem ker_character_le_ker_degree : character.ker ≤ degree.ker := fun σ h => by
  rw [MonoidHom.mem_ker, degree_apply, MonoidHom.mem_ker.1 h, map_one]

noncomputable def degreeComponent (q : Nat.Primes) : Gal(ℚ̄/ℚ) →* Multiplicative ℤ_[q] :=
  (padicUnitsLog q).comp ((Units.map (toPadicInt q).toMonoidHom).comp character)

theorem degreeComponent_apply (q : Nat.Primes) (σ : Gal(ℚ̄/ℚ)) :
    degreeComponent q σ = padicUnitsLog q (Units.map (toPadicInt q).toMonoidHom (character σ)) :=
  rfl

theorem toPadicInt_degree (q : Nat.Primes) (σ : Gal(ℚ̄/ℚ)) :
    toPadicInt q (Multiplicative.toAdd (degree σ)) = Multiplicative.toAdd (degreeComponent q σ) := by
  rw [degree_apply, toPadicInt_unitsDegree, unitsPadicEquiv_apply]
  rfl

theorem continuous_degreeComponent (q : Nat.Primes) : Continuous (degreeComponent q) := by
  have h : Continuous fun σ : Gal(ℚ̄/ℚ) => Multiplicative.toAdd (degreeComponent q σ) :=
    ((continuous_toPadicInt q).comp (continuous_toAdd.comp continuous_degree)).congr
      (toPadicInt_degree q)
  exact continuous_ofAdd.comp h

end Degree

section ComplexConjugation

def IsComplexConjugation (σ : Gal(ℚ̄/ℚ)) : Prop :=
  ∃ ι : ℚ̄ →+* ℂ, ∀ x, ι (σ x) = conj (ι x)

theorem exists_algEquiv_conj (ι : ℚ̄ →+* ℂ) :
    ∃ σ : Gal(ℚ̄/ℚ), ∀ x, ι (σ x) = conj (ι x) := by
  let _ : Algebra ℚ̄ ℂ := ι.toAlgebra
  have : IsScalarTower ℚ ℚ̄ ℂ := IsScalarTower.of_algebraMap_eq fun x =>
    (eq_ratCast _ x).trans (eq_ratCast (ι.comp (algebraMap ℚ ℚ̄)) x).symm
  let c : ℂ →ₐ[ℚ] ℂ := (starRingEnd ℂ).toRatAlgHom
  exact ⟨c.restrictNormal' ℚ̄, fun x => c.restrictNormal_commutes ℚ̄ x⟩

theorem exists_isComplexConjugation : ∃ σ : Gal(ℚ̄/ℚ), IsComplexConjugation σ := by
  let ι : ℚ̄ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  obtain ⟨σ, hσ⟩ := exists_algEquiv_conj ι.toRingHom
  exact ⟨σ, ι.toRingHom, hσ⟩

theorem character_of_isComplexConjugation {σ : Gal(ℚ̄/ℚ)} (h : IsComplexConjugation σ) :
    character σ = -1 := by
  obtain ⟨ι, hι⟩ := h
  refine Units.ext ?_
  rw [Units.val_neg, Units.val_one]
  refine (eq_character σ (-1) fun n t ht => ?_).symm
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow n.ne_zero] at ht
    exact zero_ne_one ht
  have hσ : σ t = t⁻¹ := by
    apply ι.injective
    rw [hι, map_inv₀]
    have hn : ‖ι t‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, ht, map_one]) n.ne_zero
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
    simp
  have hcast : (-1 : ZMod n) = (((n : ℕ) - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (n.pos : 1 ≤ (n : ℕ)), ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [hσ, map_neg, map_one, hcast, pow_val_natCast ht]
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← pow_succ, Nat.sub_add_cancel (n.pos : 1 ≤ (n : ℕ)), ht]

theorem degree_of_isComplexConjugation {σ : Gal(ℚ̄/ℚ)} (h : IsComplexConjugation σ) :
    degree σ = 1 := by
  rw [degree_apply, character_of_isComplexConjugation h, unitsDegree_neg_one]

end ComplexConjugation

section FixedField

noncomputable def zhatField : IntermediateField ℚ ℚ̄ :=
  fixedField degree.ker

theorem isClosed_ker_degree : IsClosed (degree.ker : Set Gal(ℚ̄/ℚ)) :=
  isClosed_singleton.preimage continuous_degree

theorem fixingSubgroup_zhatField : zhatField.fixingSubgroup = degree.ker :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨degree.ker, isClosed_ker_degree⟩

theorem zhatField_le_maxCyclotomic : zhatField ≤ maxCyclotomic := by
  rw [← fixedField_ker_character]
  intro x hx
  rw [zhatField, mem_fixedField_iff] at hx
  rw [mem_fixedField_iff]
  exact fun f hf => hx f (ker_character_le_ker_degree hf)

theorem isReal_zhatField (φ : zhatField →+* ℂ) : ComplexEmbedding.IsReal φ := by
  let _ : Algebra zhatField ℂ := φ.toAlgebra
  have : Algebra.IsAlgebraic zhatField ℚ̄ := Algebra.IsAlgebraic.tower_top (K := ℚ) zhatField
  let ι : ℚ̄ →ₐ[zhatField] ℂ := IsAlgClosed.lift
  obtain ⟨σ, hσ⟩ := exists_algEquiv_conj ι.toRingHom
  have hdeg : σ ∈ degree.ker := degree_of_isComplexConjugation ⟨_, hσ⟩
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hx : σ (x : ℚ̄) = x := (mem_fixedField_iff _ _).1 x.2 σ hdeg
  have h1 : ι (x : ℚ̄) = φ x := ι.commutes x
  have h2 := hσ (x : ℚ̄)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hx, h1] at h2
  exact h2.symm

instance isTotallyReal_zhatField : IsTotallyReal zhatField :=
  ⟨fun _ => InfinitePlace.isReal_iff.2 (isReal_zhatField _)⟩

end FixedField

end Cyclotomic

end GroundTheory.Global
