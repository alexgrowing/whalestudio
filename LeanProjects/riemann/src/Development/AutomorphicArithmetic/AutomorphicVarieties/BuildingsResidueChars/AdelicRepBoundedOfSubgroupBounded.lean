import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open CategoryTheory UpperTheory.V.Af.CohB in
theorem UpperTheory.adelic_rep_bounded_of_subgroup_bounded :
    UpperTheory.V.Af.BA.BddSub := by
  classical
  unfold UpperTheory.V.Af.BA.BddSub
  intro G _ S hS hB
  haveI := hS
  unfold UpperTheory.V.Af.CohB.Bdd at hB ⊢
  obtain ⟨c, hc⟩ := hB
  haveI : Finite (Quotient (QuotientGroup.rightRel S)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm
  have hrank : ∀ B : Rep.{0,0,0} ℂ S, Module.rank ℂ ↑(Rep.coind S.subtype B) ≤
      (Nat.card (Quotient (QuotientGroup.rightRel S)) : Cardinal) * Module.rank ℂ ↑B := by
    intro B
    let L : ↥(Representation.coindV S.subtype B.ρ) →ₗ[ℂ]
        (Quotient (QuotientGroup.rightRel S) → ↑B) :=
      { toFun := fun f q => f.1 q.out
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hL : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro f hf
      apply Subtype.ext
      funext g
      show f.1 g = 0
      let o : G := (Quotient.mk (QuotientGroup.rightRel S) g).out
      have h1 : Quotient.mk (QuotientGroup.rightRel S) o = Quotient.mk (QuotientGroup.rightRel S) g :=
        Quotient.out_eq _
      have h2 : g * o⁻¹ ∈ S := QuotientGroup.rightRel_apply.mp (Quotient.exact h1)
      let s : S := ⟨g * o⁻¹, h2⟩
      have hfo : f.1 o = 0 := congrFun hf (Quotient.mk (QuotientGroup.rightRel S) g)
      have hso : S.subtype s * o = g := by
        show g * o⁻¹ * o = g
        rw [inv_mul_cancel_right]
      calc f.1 g = f.1 (S.subtype s * o) := by rw [hso]
        _ = B.ρ s (f.1 o) := f.2 s o
        _ = 0 := by rw [hfo, map_zero]
    calc Module.rank ℂ ↑(Rep.coind S.subtype B)
        = Module.rank ℂ ↥(Representation.coindV S.subtype B.ρ) := rfl
      _ ≤ Module.rank ℂ (Quotient (QuotientGroup.rightRel S) → ↑B) :=
        LinearMap.rank_le_of_injective L hL
      _ = Cardinal.mk (Quotient (QuotientGroup.rightRel S)) * Module.rank ℂ ↑B := by
        rw [rank_pi, Cardinal.sum_const']
      _ = (Nat.card (Quotient (QuotientGroup.rightRel S)) : Cardinal) * Module.rank ℂ ↑B := by
        rw [Nat.cast_card]
  refine ⟨c * Nat.card (Quotient (QuotientGroup.rightRel S)), fun B => ?_⟩
  have htot : UpperTheory.V.Af.CohB.totCoh B = UpperTheory.V.Af.CohB.totCoh (Rep.coind S.subtype B) := by
    unfold UpperTheory.V.Af.CohB.totCoh
    congr 1
    funext q
    exact ((groupCohomology.coindIso B q).toLinearEquiv).rank_eq.symm
  rw [htot, Nat.cast_mul, mul_assoc]
  refine (hc _).trans ?_
  gcongr
  exact hrank B
