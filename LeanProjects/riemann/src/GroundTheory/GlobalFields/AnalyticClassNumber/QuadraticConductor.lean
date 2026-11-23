import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.QuadraticLegendre
import GroundTheory.GlobalFields.AnalyticClassNumber.QuadraticDirichletConductor
import GroundTheory.GlobalFields.AnalyticClassNumber.QuadraticHurwitzZero
import GroundTheory.GlobalFields.Artin.ConductorInduction
import GroundTheory.GlobalFields.Artin.ConductorOneDim
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain Module GroundTheory.LocalField NumberField.InfinitePlace NumberField.Units
open scoped Real

namespace GroundTheory.Global

section Congr

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem artinExponent_congr_character {ρ : Representation ℂ Gal(L/K) V}
    {ρ' : Representation ℂ Gal(L/K) W} (h : ρ.character = ρ'.character)
    (v : HeightOneSpectrum (𝓞 K)) : artinExponent v ρ = artinExponent v ρ' := by
  apply Nat.cast_injective (R := ℂ)
  rw [natCast_artinExponent v ρ (placeAbove v), natCast_artinExponent v ρ' (placeAbove v), h]

theorem artinConductorIdeal_congr_character {ρ : Representation ℂ Gal(L/K) V}
    {ρ' : Representation ℂ Gal(L/K) W} (h : ρ.character = ρ'.character) :
    artinConductorIdeal ρ = artinConductorIdeal ρ' :=
  finprod_congr fun v ↦ by rw [artinExponent_congr_character h v]

end Congr

namespace Quadratic

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem character_ind_trivial :
    ((Representation.trivial ℂ Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))) ℂ).ind
      (AlgEquiv.restrictScalarsHom ℚ)).character =
      ((Representation.trivial ℂ Gal(K/ℚ) ℂ).prod (charRep (galChar K))).character := by
  classical
  have := Fintype.ofFinite Gal(K/ℚ)
  have := Fintype.ofFinite Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ)))
  have hH : Nat.card Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))) = 1 := by
    rw [IsGalois.card_aut_eq_finrank, IntermediateField.finrank_fixedField_eq_card,
      Subgroup.card_bot]
  have hsub : ∀ h : Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))), h = 1 :=
    fun h ↦ (Nat.card_eq_one_iff_unique.1 hH).1.elim h 1
  funext g
  rw [character_ind, indFun_apply, character_prod, character_charRep, hH]
  simp only [Nat.cast_one, inv_one, one_mul]
  have htriv : ∀ h, (Representation.trivial ℂ
      Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))) ℂ).character h = 1 := fun h ↦ by
    simp [Representation.character]
  have htriv' : (Representation.trivial ℂ Gal(K/ℚ) ℂ).character g = 1 := by
    simp [Representation.character]
  rw [htriv']
  have hinner : ∀ t : Gal(K/ℚ), (∑ h : Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))),
      if (AlgEquiv.restrictScalarsHom ℚ) h = t⁻¹ * g * t then
        (Representation.trivial ℂ _ ℂ).character h else 0) = if g = 1 then 1 else 0 := fun t ↦ by
    rw [Fintype.sum_eq_single 1 (fun h hh ↦ absurd (hsub h) hh), map_one, htriv]
    by_cases hg : g = 1
    · simp [hg]
    · rw [if_neg hg, if_neg]
      intro h1
      apply hg
      have : t * (t⁻¹ * g * t) * t⁻¹ = g := by group
      rw [← this, ← h1]
      group
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card, card_gal]
  by_cases hg : g = 1
  · subst hg
    rw [if_pos rfl, galChar_one_apply]
    norm_num
  · rw [if_neg hg, galChar_apply_of_ne_one K hg]
    norm_num

theorem artinConductorIdeal_galChar :
    artinConductorIdeal (charRep (galChar K)) =
      relDiscr ℚ (IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))) := by
  have h1 := artinConductorIdeal_ind (K := ℚ) (L := K) ⊥
    (Representation.trivial ℂ Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))) ℂ)
  rw [artinConductorIdeal_eq_top_of_forall_eq_one
      (Representation.trivial ℂ Gal(K/IntermediateField.fixedField (⊥ : Subgroup Gal(K/ℚ))) ℂ)
      (fun _ ↦ rfl), Module.finrank_self, pow_one,
    ← Ideal.one_eq_top, map_one, mul_one] at h1
  have h2 := artinConductorIdeal_congr_character (character_ind_trivial K)
  rw [artinConductorIdeal_prod, artinConductorIdeal_eq_top_of_forall_eq_one
      (Representation.trivial ℂ Gal(K/ℚ) ℂ) (fun _ ↦ rfl), ← Ideal.one_eq_top, one_mul] at h2
  exact h2.symm.trans h1

theorem absNorm_artinConductorIdeal_galChar :
    Ideal.absNorm (artinConductorIdeal (charRep (galChar K))) = (discr K).natAbs := by
  rw [artinConductorIdeal_galChar, absNorm_relDiscr_rat, discr_eq_discr_of_algEquiv _
    ((IntermediateField.equivOfEq (IntermediateField.fixedField_bot (F := ℚ) (E := K))).trans
      IntermediateField.topEquiv)]

theorem level_eq : level K = (discr K).natAbs := by
  have h1 := DirichletHecke.absNorm_conductor_heckeCharacter (kronecker K) (isPrimitive_kronecker K)
  rw [← heckeCharacterOfChar_galChar, ← artinConductorIdeal_charRep_eq_conductor,
    absNorm_artinConductorIdeal_galChar] at h1
  exact h1.symm

section Transport

variable {N M : ℕ} (h : N = M) (χ : DirichletCharacter ℂ N)

theorem changeLevel_of_eq_apply (n : ℕ) : DirichletCharacter.changeLevel (dvd_of_eq h) χ n = χ n := by
  subst h
  rw [DirichletCharacter.changeLevel_self]

theorem isPrimitive_changeLevel_of_eq (hχ : χ.IsPrimitive) :
    (DirichletCharacter.changeLevel (dvd_of_eq h) χ).IsPrimitive := by
  subst h
  rwa [DirichletCharacter.changeLevel_self]

theorem LFunction_changeLevel_of_eq [NeZero N] [NeZero M] (s : ℂ) :
    DirichletCharacter.LFunction (DirichletCharacter.changeLevel (dvd_of_eq h) χ) s =
      DirichletCharacter.LFunction χ s := by
  subst h
  rw [DirichletCharacter.changeLevel_self]

theorem heckeCharacter_changeLevel_of_eq [NeZero N] [NeZero M] :
    DirichletHecke.heckeCharacter (DirichletCharacter.changeLevel (dvd_of_eq h) χ) =
      DirichletHecke.heckeCharacter χ := by
  subst h
  rw [DirichletCharacter.changeLevel_self]

theorem changeLevel_of_eq_ne_one (hχ : χ ≠ 1) :
    DirichletCharacter.changeLevel (dvd_of_eq h) χ ≠ 1 := by
  subst h
  rwa [DirichletCharacter.changeLevel_self]

end Transport

instance : NeZero (discr K).natAbs :=
  ⟨Int.natAbs_ne_zero.2 (discr_ne_zero K)⟩

def kroneckerChar : DirichletCharacter ℂ (discr K).natAbs :=
  DirichletCharacter.changeLevel (dvd_of_eq (level_eq K)) (kronecker K)

theorem isPrimitive_kroneckerChar : (kroneckerChar K).IsPrimitive :=
  isPrimitive_changeLevel_of_eq (level_eq K) _ (isPrimitive_kronecker K)

theorem conductor_kroneckerChar : (kroneckerChar K).conductor = (discr K).natAbs :=
  isPrimitive_kroneckerChar K

theorem heckeCharacter_kroneckerChar :
    DirichletHecke.heckeCharacter (kroneckerChar K) = heckeCharacterOfChar (galChar K) := by
  rw [kroneckerChar, heckeCharacter_changeLevel_of_eq (level_eq K), heckeCharacterOfChar_galChar]

theorem kroneckerChar_apply (n : ℕ) : kroneckerChar K n = kronecker K n :=
  changeLevel_of_eq_apply (level_eq K) _ n

theorem LFunction_kroneckerChar (s : ℂ) :
    DirichletCharacter.LFunction (kroneckerChar K) s = DirichletCharacter.LFunction (kronecker K) s :=
  LFunction_changeLevel_of_eq (level_eq K) _ s

theorem kroneckerChar_ne_one : kroneckerChar K ≠ 1 :=
  changeLevel_of_eq_ne_one (level_eq K) _ (kronecker_ne_one K)

theorem kroneckerChar_apply_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    kroneckerChar K p = (legendreSym p (discr K) : ℂ) := by
  rw [kroneckerChar_apply, kronecker_apply_prime K p hp]

theorem classNumber_eq_of_discr_neg' (hd : discr K < 0) :
    (classNumber K : ℂ) = torsionOrder K * Real.sqrt |(discr K : ℝ)| *
      DirichletCharacter.LFunction (kroneckerChar K) 1 / (2 * π) := by
  rw [LFunction_kroneckerChar, classNumber_eq_of_discr_neg K hd]

theorem classNumber_mul_regulator_eq_of_discr_pos' (hd : 0 < discr K) :
    ((classNumber K * regulator K : ℝ) : ℂ) = Real.sqrt (discr K : ℝ) *
      DirichletCharacter.LFunction (kroneckerChar K) 1 / 2 := by
  rw [LFunction_kroneckerChar, classNumber_mul_regulator_eq_of_discr_pos K hd]

theorem LFunction_kroneckerChar_zero (hd : discr K < 0) :
    DirichletCharacter.LFunction (kroneckerChar K) 0 = 2 * classNumber K / torsionOrder K := by
  obtain ⟨h1, h2⟩ := places_of_discr_neg K hd
  have hR : regulator K = 1 := regulator_eq_one_of_card_eq_one (by omega)
  have hz := continuedDedekindZeta_zero K
  rw [if_pos (by omega), hR, continuedDedekindZeta_eq_mul K zero_ne_one, riemannZeta_zero] at hz
  rw [LFunction_kroneckerChar]
  push_cast at hz
  linear_combination (-2 : ℂ) * hz

theorem classNumber_eq_sum_of_discr_neg (hd : discr K < 0) :
    (classNumber K : ℂ) = -(torsionOrder K / (2 * (discr K).natAbs)) *
      ∑ a : ZMod (discr K).natAbs, kroneckerChar K a * (a.val : ℂ) := by
  have h0 := LFunction_kroneckerChar_zero K hd
  rw [LFunction_zero_eq_of_ne_one (kroneckerChar_ne_one K)] at h0
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_ne_zero K)
  have hN : ((discr K).natAbs : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Int.natAbs_ne_zero.2 (discr_ne_zero K))
  calc (classNumber K : ℂ) = (torsionOrder K / 2) * (2 * classNumber K / torsionOrder K) := by
        field_simp
    _ = (torsionOrder K / 2) * (-(1 / ((discr K).natAbs : ℂ)) *
          ∑ a : ZMod (discr K).natAbs, kroneckerChar K a * (a.val : ℂ)) := by rw [h0]
    _ = _ := by ring

end Quadratic

end GroundTheory.Global
