import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitInverseExpansionEquivariantLabelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantBijectionLargerClosedFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantBijectionsFamiliesSectionsDifferBySca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gs_liftFun_top {S0 : Scheme.{0}} (A : Over S0) {T : Over S0} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤))
    {Z : Scheme.{0}} (q : Z ⟶ (T ⊗ A).left) (z : Z) (hz : q z ∈ W) :
    gs q z W (liftFun A W r) = gs (q ≫ (fst T A).left) z ⊤ r :=
  (gs_res q z le_top hz _).trans (gs_pull q (fst T A).left z ⊤ trivial r)

theorem fvalue_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ E₀ (Φ₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → H0 C.A.L (C.n ^ j)), Eqv D.toPre C.A (Kb R) (C.n ^ j) (C.lab j) E₀ → (∀ F₀ s, F₀.Over s → Agree C.A.L (E₀ s) (Φ₀ F₀)) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j)), (∀ F₀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J J', Good C.P.L.L z J → Good C.A.L z J' → sval (Φ F₀) p z J = (gw wA p z (J (p ≫ C.α)) (J' p) ^ (C.n ^ j)).val * sval (Φ₀ F₀) p z J') → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ c : F, c ≠ 0 ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J := by
  intro R _ _ _ hR D C j wA hwA E₀ Φ₀ hE₀ hΦ₀ Φ hΦ W _ _ _ T F _ _ _ _ em hem
  obtain ⟨lab, E, hlab, hE, hT⟩ := GlobalTheory.T.trait_inverse_expansion_equivariant_labels R hR D C j wA hwA W T F em hem
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  obtain ⟨E', hE', hAg⟩ := GlobalTheory.T.exists_equivariant_bijection_larger_closed_field R hR D C.A (C.n ^ j) hodd (C.lab j) E₀ Φ₀ hE₀ hΦ₀ F em lab hlab
  haveI : CharZero R := hR.2
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.Mum.eqv_eq_smul R (maximalIdeal R) D C.A F (C.n ^ j) hodd lab E E' hE hE'
  refine ⟨(c₀ : F)⁻¹, inv_ne_zero c₀.ne_zero, ?_⟩
  intro F₀ σ hσ Z p p' h1 h2 z J hJ
  obtain ⟨s, hs, -⟩ := GlobalTheory.Mum.IntFam.existsUnique_over R (maximalIdeal R) D.toPre (C.n ^ j) F₀ F
  obtain ⟨J', hJ', -⟩ := exists_good C.A.L C.A.isLB z (K := Empty) (fun e => e.elim) (fun e => e.elim)
    (fun a => a.elim) (fun k => k.elim)
  set q := p' ≫ (snd (TFK (R := R) F) C.A.A).left with hq
  have e1 := hT F₀ s σ hs hσ Z p p' h1 h2 z J J' hJ hJ'
  have e2 : sval (E' s) p' z J' = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)) * sval (E s) p' z J' := by
    unfold sval
    refine (congrArg (gs p' z _) (hc₀ s _)).trans ?_
    exact (gs_mul p' z _ (hJ'.mem _ p') _ _).trans (congrArg (· * _) (gs_liftFun_top _ _ _ _ _ (hJ'.mem _ p')))
  have e3 := hAg F₀ s hs Z p' q (Category.comp_id _).symm z J' hJ'
  have e4 := hΦ F₀ Z q z J J' hJ hJ'
  have hβ : J (q ≫ C.α) = J (p ≫ T.β) := by rw [h1, hq, Category.assoc]
  rw [hβ] at e4
  have huv : gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)⁻¹) *
      gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)) = 1 := by
    rw [← gs_mul (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ trivial, fnF, fnF, ← map_mul, inv_mul_cancel₀ c₀.ne_zero,
      map_one, gs_eq (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ trivial, map_one, map_one]
  rw [e1, e4, ← e3, e2]
  linear_combination (-(gw wA q z (J (p ≫ T.β)) (J' q) ^ (C.n ^ j)).val * sval (E s) p' z J') * huv

end GlobalTheory.Mum
