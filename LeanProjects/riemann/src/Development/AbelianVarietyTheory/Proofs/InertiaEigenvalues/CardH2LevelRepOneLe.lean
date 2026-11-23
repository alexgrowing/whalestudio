import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCardTorsionLevelFractionRingQuotStatement
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

theorem finite_card_dual {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [Finite V] :
    Finite (Module.Dual F V) ∧ Nat.card (Module.Dual F V) = Nat.card V := by
  haveI : Module.Finite F V := Module.Finite.of_finite
  haveI : Finite (Module.Dual F V) := DFunLike.finite (Module.Dual F V)
  refine ⟨inferInstance, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := F), Module.natCard_eq_pow_finrank (K := F) (V := V),
    Subspace.dual_finrank_eq]

theorem card_H2_level_rep_le :
    Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M)
    (h : ((p : O) ^ 1) ∈ Ideal.span {ϖ ^ 1}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p 1 h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ) →
    Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ)) ≤ Nat.card (IsLocalRing.ResidueField O) := by
  intro hT p _ K hK O _ _ _ _ ϖ hϖ M _ _ e ρ h
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p 1 h
  intro hc
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.finite_card_torsionLevel_fractionRingQuot hϖ e 1
  haveI : Finite (Lev M (ϖ ^ 1)) := hfin
  haveI : Fact (p ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  obtain ⟨⟨eH⟩, -, -, -, hb⟩ := hT p K hK 1 (Lev M (ϖ ^ 1)) (levRepZ p 1 h ρ) one_pos hc
  set ρ' := levRepZ p 1 h ρ
  set χ := Formalism.GaloisCohomology.cycK p K 1

  let W := ↥(H0 ((twDual χ ρ').comp (MonoidHom.id _)))
  haveI : Finite (TDual (ZMod (p ^ 1)) (Lev M (ϖ ^ 1))) :=
    (finite_card_dual (F := ZMod (p ^ 1)) (V := Lev M (ϖ ^ 1))).1
  haveI : Finite W := Subtype.finite
  have hW : Nat.card W ≤ Nat.card (Lev M (ϖ ^ 1)) :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      (finite_card_dual (F := ZMod (p ^ 1)) (V := Lev M (ϖ ^ 1))).2.le
  obtain ⟨hfd, hcd⟩ := finite_card_dual (F := ZMod (p ^ 1)) (V := W)
  let E := LinearEquiv.congrRight (M := W) eH
  haveI : Finite (W →ₗ[ZMod (p ^ 1)] H2 ((charRep χ).comp (MonoidHom.id _))) :=
    Finite.of_equiv _ E.symm.toEquiv
  have h1 : Nat.card (H2 ρ') ≤ Nat.card (W →ₗ[ZMod (p ^ 1)] H2 ((charRep χ).comp (MonoidHom.id _))) :=
    Nat.card_le_card_of_injective _ hb.1
  have h2 : Nat.card (W →ₗ[ZMod (p ^ 1)] H2 ((charRep χ).comp (MonoidHom.id _))) = Nat.card W :=
    (Nat.card_congr E.toEquiv).trans hcd
  calc Nat.card (H2 ρ') ≤ Nat.card W := h1.trans h2.le
    _ ≤ Nat.card (Lev M (ϖ ^ 1)) := hW
    _ = Nat.card (IsLocalRing.ResidueField O) := hcard.trans (pow_one _)

end GlobalTheory.ShapeNeg
