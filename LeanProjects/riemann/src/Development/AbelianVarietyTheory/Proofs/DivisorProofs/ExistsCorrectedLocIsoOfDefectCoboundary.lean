import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqZeroOfMemMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentialsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_corr_of_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ E : GlobForm s₀ →+ C0 S'.F, (∀ w, S'.IsIdealValuedLiftSystemCochain (E w)) → (∀ (r : R) w, E (π r • w) = r • E w) → (∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = d0 S'.F (E w) U V a) → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar S S' Φ θ hθ E hEI hEs hEd

  have hext : ∀ U : AffOp X₀, ∃! η : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj U,
      (∀ b w, η (S.p U b • w) = (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) b * η w) ∧
      (∀ w, η w ∈ I.map (algebraMap R (S'.F.obj U))) ∧ ∀ w : GlobForm s₀, η (w.1 U) = E w U := fun U ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U (S.F.obj U) (S'.F.obj U) (S.p U) (S.semi U)
      (S.surj U) (S.ker U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) ((Pi.evalAddMonoidHom _ U).comp E)
      (fun r w ↦ by simp [hEs]) (fun w ↦ hEI w U)

  choose η hη using fun U ↦ (hext U).exists
  have hψ : ∀ U : AffOp X₀, ∃ ψ : S.F.obj U →ₐ[R] S'.F.obj U,
      IsTheta I (S.p U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) ψ (-η U) := fun U ↦
    (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj U) I hI π hπ (S.p U) (S.semi U) (S.surj U)
      (S.ker U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)).2 (-η U)
      (fun b w ↦ by rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, (hη U).1, mul_neg])
      (fun w ↦ by rw [AddMonoidHom.neg_apply]; exact neg_mem ((hη U).2.1 w))
  choose ψ hψ using hψ
  have hψv : ∀ U b, ψ U b = Φ.φ U b + η U (D R₀ (Sec s₀ U.unop.1) (S.p U b)) := fun U b ↦ by
    have h := (hψ U).der b
    rw [AddMonoidHom.neg_apply] at h
    change -η U _ = Φ.φ U b - ψ U b at h
    linear_combination h
  refine ⟨ψ, fun U b ↦ ?_, fun U V a b ↦ ?_⟩
  · rw [hψv, map_add, Φ.red, (S'.ker U _).2 ((hη U).2.1 _), add_zero]
  ·
    let α : S.F.obj U →ₐ[R] S'.F.obj V := (mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)
    let χ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V := θ U V a + (mp S'.F a).toAddMonoidHom.comp (η U) -
      (η V).comp (p1 (OAff s₀) a).toAddMonoidHom
    have hχ : ∀ w, χ w = θ U V a w + mp S'.F a (η U w) - η V (p1 (OAff s₀) a w) := fun _ ↦ rfl

    have hmemV : ∀ w, η V w ∈ I.map (algebraMap R (S'.F.obj V)) := (hη V).2.1
    have hdiff : ∀ c : S.F.obj U, ∀ x ∈ I.map (algebraMap R (S'.F.obj V)),
        (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (mp S.F a c) * x = α c * x := by
      intro c x hx
      have h1 := (hθ U V a).der c
      have h2 : α c - (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (mp S.F a c) ∈ I.map (algebraMap R (S'.F.obj V)) :=
        h1 ▸ (hθ U V a).mem _
      have h3 := mul_eq_zero_of_mem_map hI h2 hx
      rw [sub_mul] at h3
      exact (sub_eq_zero.1 h3).symm
    have hu := exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U (S.F.obj U) (S'.F.obj V) (S.p U) (S.semi U)
      (S.surj U) (S.ker U) α 0 (fun r w ↦ by simp) (fun w ↦ zero_mem _)
    have hχ0 : χ = 0 := by
      refine hu.unique ⟨fun b w ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩ ⟨fun b w ↦ by simp, fun w ↦ zero_mem _, fun w ↦ rfl⟩
      · rw [hχ, hχ, (hθ U V a).smul, (hη U).1, oneFormsMapOfFunctorMorphism_smul, map_mul]
        rw [← S.nat a b, (hη V).1, hdiff _ _ (hmemV _)]
        simp only [α, AlgHom.coe_comp, Function.comp_apply]
        ring
      · rw [hχ]
        exact sub_mem (add_mem ((hθ U V a).mem w) (algHom_mem_map I _ ((hη U).2.1 w))) (hmemV _)
      · rw [hχ, hEd, amitsur_d0_apply, (hη U).2.2, ← w.2 a, (hη V).2.2]
        simp
    have h0 : χ (D R₀ (Sec s₀ U.unop.1) (S.p U b)) = 0 := by rw [hχ0]; rfl
    rw [hχ, p1_D] at h0
    have hn : mp (OAff s₀) a (S.p U b) = S.p V (mp S.F a b) := (S.nat a b).symm
    rw [hn] at h0
    have h1 := (hθ U V a).der b
    simp only [α, AlgHom.coe_comp, Function.comp_apply] at h1
    rw [hψv, hψv, map_add]
    simp only [AlgEquiv.coe_toAlgHom] at h0 h1 ⊢
    linear_combination h0 - h1

end GlobalTheory.LiftSys
