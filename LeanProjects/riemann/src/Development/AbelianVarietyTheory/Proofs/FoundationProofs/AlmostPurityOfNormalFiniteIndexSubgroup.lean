import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityMovesIntegersOfNeOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleOfMovesIntegersStatement
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem mem_Fix_iff {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) (x : L) : x ∈ Fix L N ↔ ∀ h : G, h ∈ N → h • x = x :=
  ⟨fun hx h hh => hx ⟨h, hh⟩, fun hx m => hx m.1 m.2⟩

noncomputable instance quotFixAction {L : Type} [Field L] {G : Type} [Group G]
    [MulSemiringAction G L] (U : Subgroup G) [U.Normal] :
    MulSemiringAction (G ⧸ U) (Fix L U) :=
  inferInstanceAs (MulSemiringAction (G ⧸ U) (FixedPoints.subring L U))

theorem quot_smul_coe {L : Type} [Field L] {G : Type} [Group G]
    [MulSemiringAction G L] (U : Subgroup G) [U.Normal] (g : G) (x : Fix L U) :
    (((g : G ⧸ U) • x : Fix L U) : L) = g • (x : L) := rfl

end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem almostSep_of_normal_finiteIndex : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ),
    p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L],
    (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) →
    ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ U : Subgroup G, U.Normal → U.FiniteIndex →
    (∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x) → AlmostSep v U := by
  intro L _ v p hp hp0 hp1 G _ _ hv ζ hζ hζG hroot U hU hUfin hfaith
  refine GlobalTheory.T.fixedFieldAlmostEtale_of_moves_integers L v G hv U hU hUfin ?_
  intro σ hσ
  let L' := ↥(Fix L U)
  let v' : Valuation L' ℝ≥0 := v.comap (Fix L U).subtype
  have hv'x : ∀ x : L', v' x = v (x : L) := fun x => rfl
  haveI : Finite (G ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  haveI : FaithfulSMul (G ⧸ U) L' := by
    refine ⟨fun {q₁ q₂} h => ?_⟩
    induction q₁ using QuotientGroup.induction_on with | H g₁ => ?_
    induction q₂ using QuotientGroup.induction_on with | H g₂ => ?_
    rw [QuotientGroup.eq]
    by_contra hne
    obtain ⟨x, hx, hmov⟩ := hfaith _ hne
    apply hmov
    have h1 := congrArg Subtype.val (h ⟨x, hx⟩)
    rw [quot_smul_coe, quot_smul_coe] at h1
    rw [mul_smul, ← h1, ← mul_smul, inv_mul_cancel, one_smul]
  have hpcast : ((p : L') : L) = (p : L) := map_natCast (Fix L U).subtype p
  have hζU : ζ ∈ Fix L U := (mem_Fix_iff U ζ).2 fun h _ => hζG h
  let ζ' : L' := ⟨ζ, hζU⟩
  have hζ' : IsPrimitiveRoot ζ' p :=
    (IsPrimitiveRoot.map_iff_of_injective (f := (Fix L U).subtype) Subtype.val_injective).1 hζ
  have hmain := GlobalTheory.T.almostPurity_moves_integers_of_ne_one L' v' p hp (by rw [hv'x, hpcast]; exact hp0)
    (by rw [hv'x, hpcast]; exact hp1) (G ⧸ U)
    (by
      intro q x
      induction q using QuotientGroup.induction_on with | H g => ?_
      rw [hv'x, hv'x, quot_smul_coe, hv])
    ζ' hζ'
    (by
      intro q
      induction q using QuotientGroup.induction_on with | H g => ?_
      exact Subtype.ext (by rw [quot_smul_coe]; exact hζG g))
    (by
      obtain ⟨θ, hθ, hθu⟩ := hroot
      refine ⟨θ, hθ, fun u hu => ?_⟩
      have hu' : (u : L) ∈ Fix L (⊤ : Subgroup G) := by
        refine (mem_Fix_iff _ _).2 fun g _ => ?_
        have := congrArg Subtype.val (((mem_Fix_iff _ u).1 hu) (g : G ⧸ U) trivial)
        rwa [quot_smul_coe] at this
      obtain ⟨w, hw, hwu⟩ := hθu _ hu'
      have hwU : w ∈ Fix L U := (mem_Fix_iff U w).2 fun h _ => (mem_Fix_iff _ w).1 hw h trivial
      refine ⟨⟨w, hwU⟩, ?_, ?_⟩
      · refine (mem_Fix_iff _ _).2 fun q _ => ?_
        induction q using QuotientGroup.induction_on with | H g => ?_
        exact Subtype.ext (by rw [quot_smul_coe]; exact (mem_Fix_iff _ w).1 hw g trivial)
      · rw [hv'x, hv'x]
        exact hwu)
    (σ : G ⧸ U) (by rwa [Ne, QuotientGroup.eq_one_iff])
  intro r hr
  obtain ⟨x, -, hx1, hxr⟩ := hmain r hr
  refine ⟨(x : L), x.2, hx1, ?_⟩
  rw [hv'x, AddSubgroupClass.coe_sub, quot_smul_coe] at hxr
  exact hxr

end GlobalTheory.AlmostEt
