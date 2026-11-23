import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqZeroOfMemMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearLiftOfProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUniqueStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_natLift_of_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsLift L' n l → ∀ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) → (∀ (r : R) w, u (π r • w) = r • u w) → (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) → (∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T)) → ∃ l' : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T, L.IsLift L' n l' ∧ L.IsNat L' n l' := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar C' _ F' L L' n l hl κ u hκ hus hum hκd
  have hext : ∀ T : C', ∃! ξ : Ω[Sec s₀ (n.G.obj T).unop.1⁄R₀] →+ L'.B T,
      (∀ b w, ξ (L.p (n.G.obj T) b • w) = l T b * ξ w) ∧
      (∀ w, ξ w ∈ I.map (algebraMap R (L'.B T))) ∧ ∀ w : GlobForm s₀, ξ (w.1 (n.G.obj T)) = u w T := fun T ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar (n.G.obj T) (L.B (n.G.obj T)) (L'.B T) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (l T) ((Pi.evalAddMonoidHom _ T).comp u)
      (fun r w ↦ by simp [hus]) (fun w ↦ hum w T)
  choose ξ hξ using fun T ↦ (hext T).exists
  have hψ : ∀ T : C', ∃ ψ : L.B (n.G.obj T) →ₐ[R] L'.B T,
      IsTheta I (L.p (n.G.obj T)) (l T) ψ (-ξ T) := fun T ↦
    (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (L.B (n.G.obj T)) (Sec s₀ (n.G.obj T).unop.1) (L'.B T) I hI π hπ (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (l T)).2 (-ξ T)
      (fun b w ↦ by rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, (hξ T).1, mul_neg])
      (fun w ↦ by rw [AddMonoidHom.neg_apply]; exact neg_mem ((hξ T).2.1 w))
  choose ψ hψ using hψ
  have hψv : ∀ T b, ψ T b = l T b + ξ T (D R₀ (Sec s₀ (n.G.obj T).unop.1) (L.p _ b)) := fun T b ↦ by
    have h := (hψ T).der b
    rw [AddMonoidHom.neg_apply] at h
    change -ξ T _ = l T b - ψ T b at h
    linear_combination h
  refine ⟨ψ, fun T b ↦ ?_, fun T T' a b ↦ ?_⟩
  · rw [hψv, map_add, hl, (L'.ker T _).2 ((hξ T).2.1 _), add_zero]
  · let α : L.B (n.G.obj T) →ₐ[R] L'.B T' := (L'.ρ a).comp (l T)
    let χ : Ω[Sec s₀ (n.G.obj T).unop.1⁄R₀] →+ L'.B T' := κ T T' a + (L'.ρ a).toAddMonoidHom.comp (ξ T) -
      (ξ T').comp (p1 (OAff s₀) (n.G.map a)).toAddMonoidHom
    have hχ : ∀ w, χ w = κ T T' a w + L'.ρ a (ξ T w) - ξ T' (p1 (OAff s₀) (n.G.map a) w) := fun _ ↦ rfl
    have hmemV : ∀ w, ξ T' w ∈ I.map (algebraMap R (L'.B T')) := (hξ T').2.1
    have hdiff : ∀ c : L.B (n.G.obj T), ∀ x ∈ I.map (algebraMap R (L'.B T')),
        l T' (L.ρ (n.G.map a) c) * x = α c * x := by
      intro c x hx
      have h1 := (hκ T T' a).der c
      have h2 : α c - l T' (L.ρ (n.G.map a) c) ∈ I.map (algebraMap R (L'.B T')) :=
        h1 ▸ (hκ T T' a).mem _
      have h3 := mul_eq_zero_of_mem_map hI h2 hx
      rw [sub_mul] at h3
      exact (sub_eq_zero.1 h3).symm
    have hu := exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar (n.G.obj T) (L.B (n.G.obj T)) (L'.B T') (L.p _)
      (L.semi _) (L.surj _) (L.ker _) α 0 (fun r w ↦ by simp) (fun w ↦ zero_mem _)
    have hχ0 : χ = 0 := by
      refine hu.unique ⟨fun b w ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩ ⟨fun b w ↦ by simp, fun w ↦ zero_mem _, fun w ↦ rfl⟩
      · rw [hχ, hχ, (hκ T T' a).smul, (hξ T).1, oneFormsMapOfFunctorMorphism_smul, map_mul]
        rw [← L.nat (n.G.map a) b, (hξ T').1, hdiff _ _ (hmemV _)]
        simp only [α, AlgHom.coe_comp, Function.comp_apply]
        ring
      · rw [hχ]
        exact sub_mem (add_mem ((hκ T T' a).mem w) (algHom_mem_map I _ ((hξ T).2.1 w))) (hmemV _)
      · rw [hχ, hκd, (hξ T).2.2, ← w.2 (n.G.map a), (hξ T').2.2]
        simp
    have h0 : χ (D R₀ (Sec s₀ (n.G.obj T).unop.1) (L.p _ b)) = 0 := by rw [hχ0]; rfl
    rw [hχ, p1_D] at h0
    have hn : mp (OAff s₀) (n.G.map a) (L.p _ b) = L.p _ (L.ρ (n.G.map a) b) := (L.nat (n.G.map a) b).symm
    rw [hn] at h0
    have h1 := (hκ T T' a).der b
    simp only [α, AlgHom.coe_comp, Function.comp_apply] at h1
    rw [hψv, hψv, map_add]
    linear_combination h0 - h1

end GlobalTheory.LiftSys
