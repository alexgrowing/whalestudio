import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericMultiplicityOne
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalInducedCharacter

noncomputable section

namespace GlobalTheory.CuspidalIdempotentCharacters

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

theorem isIndCuspChar_iff {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) {K : Type} [Field K]
    (s : K →+* ℂ) (χ : G0 Pg r → K) :
    GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.IsIndCuspChar Pg r s χ ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar Pg r s χ := by
  constructor
  · rintro ⟨b, V, i1, i2, i3, σ, hc, hχ⟩
    exact ⟨_, fun PP => ⟨b PP, V PP, i1 PP, i2 PP, i3 PP, σ PP, hc PP, fun _ => rfl⟩, hχ⟩
  · rintro ⟨θ, hθ, hχ⟩
    choose b V i1 i2 i3 σ hc ht using hθ
    exact ⟨b, V, i1, i2, i3, σ, hc, fun g => (hχ g).trans (Finset.prod_congr rfl fun PP _ => ht PP (g PP))⟩

theorem sum_eq_lvlSum {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K]
    (P : LevelP Pg r K) (χ : G0 Pg r → K) (i : Fintype P.H) :
    ∑ h : P.H, χ (h : G0 Pg r) * (((P.chi h)⁻¹ : Kˣ) : K) = GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.lvlSum P χ := by
  obtain rfl : i = GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.fintypeH P := Subsingleton.elim _ _
  rfl

theorem genericMultOne_iff : GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector
  refine forall_congr' fun E => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun Pg =>
    forall_congr' fun r => forall_congr' fun K => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun s => forall_congr' fun ψ => forall_congr' fun _ => forall_congr' fun χ =>
    imp_congr (isIndCuspChar_iff Pg r s χ) ?_
  rw [← sum_eq_lvlSum (P0 Pg r ψ) χ]

section Idem

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem eps_eq_lvlIdem (H : Subgroup G) (ψ : H →* Kˣ) :
    Formalism.MainNotions.PrimeDegreeVariant.eps (⟨H, ψ⟩ : Formalism.MainNotions.PrimeDegreeVariant.Pair K G) = lvlIdem H ψ := by
  classical
  unfold Formalism.MainNotions.PrimeDegreeVariant.eps lvlIdem
  rw [Finset.smul_sum]
  symm
  refine Fintype.sum_of_injective (fun h : H => (h : G)) Subtype.val_injective _ _ ?_ ?_
  · intro x hx
    have : x ∉ H := fun h => hx ⟨⟨x, h⟩, rfl⟩
    simp [this]
  · intro h
    simp [map_inv]

variable {W : Type} [AddCommGroup W] [Module K W]

theorem asAlgebraHom_lvlIdem (τ : Representation K G W) (H : Subgroup G) (ψ : H →* Kˣ) [Fintype H] :
    τ.asAlgebraHom (lvlIdem H ψ) = (Nat.card H : K)⁻¹ • ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) := by
  unfold lvlIdem
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr (by congr!) fun h _ => ?_
  rw [Representation.asAlgebraHom_single, smul_smul, map_inv]

theorem isIdempotentElem_lvlIdem [CharZero K] (τ : Representation K G W) (H : Subgroup G) (ψ : H →* Kˣ) :
    IsIdempotentElem (τ.asAlgebraHom (lvlIdem H ψ)) := by
  classical
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  set T : Module.End K W := ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) with hT
  have h1 : ∀ a : H, ((((ψ a)⁻¹ : Kˣ) : K) • τ (a : G)) * T = T := by
    intro a
    rw [hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun h => ?_
    simp [smul_smul, mul_comm]
  have h2 : T * T = (Nat.card H : K) • T := by
    conv_lhs => rw [hT, Finset.sum_mul, ← hT]
    rw [Finset.sum_congr rfl fun a _ => h1 a]
    simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  rw [IsIdempotentElem, asAlgebraHom_lvlIdem, ← hT, smul_mul_smul_comm, h2, smul_smul, mul_assoc,
    inv_mul_cancel₀ hc, mul_one]

theorem finrank_eq_one_iff [CharZero K] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G)
    (ψ : H →* Kˣ) [Fintype H] :
    Module.finrank K (LinearMap.range (τ.asAlgebraHom (lvlIdem H ψ))) = 1 ↔
      ∑ h : H, LinearMap.trace K W (τ (h : G)) * (((ψ h)⁻¹ : Kˣ) : K) = (Nat.card H : K) := by
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  have h := (LinearMap.IsIdempotentElem.isProj_range _ (isIdempotentElem_lvlIdem τ H ψ)).trace
  have e : LinearMap.trace K W (τ.asAlgebraHom (lvlIdem H ψ)) =
      (Nat.card H : K)⁻¹ * ∑ h : H, LinearMap.trace K W (τ (h : G)) * (((ψ h)⁻¹ : Kˣ) : K) := by
    rw [asAlgebraHom_lvlIdem, map_smul, map_sum, smul_eq_mul]
    simp [mul_comm]
  rw [← Nat.cast_eq_one (R := K), ← h, e, inv_mul_eq_one₀ hc, eq_comm]

end Idem

end GlobalTheory.CuspidalIdempotentCharacters
