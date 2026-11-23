import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Formalism.LocalToGlobal.ProjectiveLattices.TensPtsSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieRankSum

theorem sum_lieMult {E : Type} [Field E] [NumberField E] {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {g : ℕ} (hG : SmoothOfRelativeDimension g G.hom) (act : OAct (𝓞 E) G) {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (t : Sp k ⟶ S) (rk : (𝓞 E →+* k) → ℕ) (h : ∀ σ, LieMult act t σ (rk σ)) :
    ∑ σ : E →+* k, rk (σ.comp (algebraMap (𝓞 E) E)) = g := by
  classical
  have hk := isGrpPullback_pullback G t
  have hd : SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hk.1 hG
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis _ hd
  let actk := OAct.pullback t G act
  have hak : ∀ a, (actk.act a).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (act.act a).left :=
    fun a => pullback.lift_fst _ _ _
  obtain ⟨ρ, hρ⟩ := LieEigen.exists_action hv actk
  have hinj : Function.Injective fun σ : E →+* k => σ.comp (algebraMap (𝓞 E) E) := fun σ σ' e =>
    IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => RingHom.congr_fun e x
  have hσ : EigenSplit.IsSplitting fun σ : E →+* k => (RingHom.id k).comp (σ.comp (algebraMap (𝓞 E) E)) :=
    EigenSplit.isSplitting_of_isDomain hinj (NumberField.Embeddings.card E k) _
      (EigenSplit.isUnit_discr_of_charZero k)
  have hint := EigenSplit.isInternal_eigenSub hσ ρ
  have e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hint).finrank_eq
  rw [Module.finrank_directSum, Module.finrank_fin_fun] at e
  rw [← e]
  exact Finset.sum_congr rfl fun σ _ => (LieEigen.finrank_of_lieMult hk hv hak hρ (h _)).symm

theorem rank_mul_finrank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (act : OAct (𝓞 E) G) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : Sp k ⟶ S) (rk : (𝓞 E →+* k) → ℕ) (r : ℕ), (∀ σ : 𝓞 E →+* k, LieMult act t σ (rk σ) ∧ rk σ + rk (σ.comp (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)) = r) → r * Module.finrank ℚ E = 2 * g := by
  intro E _ _ _ S G _ _ g hG act k _ _ _ t rk r h
  have h₁ := sum_lieMult hG act t rk fun σ => (h σ).1
  let c : (E →+* k) ≃ (E →+* k) :=
    ⟨fun σ => σ.comp (IsCMField.complexConj E : E →+* E), fun σ => σ.comp (IsCMField.complexConj E : E →+* E),
      fun σ => RingHom.ext fun a => by simp, fun σ => RingHom.ext fun a => by simp⟩
  have h₂ := (Equiv.sum_comp c fun σ => rk (σ.comp (algebraMap (𝓞 E) E))).trans h₁
  have h₃ : ∑ σ : E →+* k, (rk (σ.comp (algebraMap (𝓞 E) E)) + rk ((c σ).comp (algebraMap (𝓞 E) E))) =
      ∑ _σ : E →+* k, r := Finset.sum_congr rfl fun σ _ => (h _).2
  rw [Finset.sum_add_distrib, h₁, h₂, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    smul_eq_mul] at h₃
  rw [mul_comm, ← h₃, two_mul]

end GlobalTheory.LieRankSum
