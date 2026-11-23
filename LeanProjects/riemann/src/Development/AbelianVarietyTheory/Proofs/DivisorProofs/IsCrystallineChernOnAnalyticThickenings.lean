import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isChern_real : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X) (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ z : SecondDeRham s, IsChern (dp0 B) s M z → ∃ (i : K.Obj → M.ι) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) ∧ (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) ∧ (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ ((show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) ∧ r.coef.pull2 z = GlobalTheory.CatCoh.H2.mk K.Oc ℓ := by
  intro I _ g Λ _ F B _ X s σ K r M j hj z hz
  obtain ⟨i₀, hi₀, u₀, ℓ₀, h1, h2, h3⟩ := hz
  let G : K.Obj ⥤ (IsSmall (dp0 B) s M.U).FullSubcategory :=
    ObjectProperty.lift _ r.functor fun T ↦ ⟨j T.k, fun p _ ↦ hj T.k (Set.mem_univ _)⟩
  let n : GlobalTheory.CatCoh.CoefMap σ ((IsSmall (dp0 B) s M.U).ι ⋙ O (dp0 B) s) K.Oc :=
    { G := G
      α := fun T ↦ RingHom.id T.C
      naturality := fun _ _ ↦ rfl
      smul := fun T b c ↦ r.coef.smul T b c }
  refine ⟨fun T ↦ i₀ (G.obj T), fun T T' φ ↦ u₀ _ _ (G.map φ), n.pullbackTwoCocycle ℓ₀, fun T ↦ hi₀ (G.obj T),
    fun T T' φ _ ↦ h1 _ _ (G.map φ), fun T T' T'' φ ψ ↦ ?_, ?_⟩
  · have h := h2 _ _ _ (G.map φ) (G.map ψ)
    rw [← G.map_comp] at h
    exact h
  · rw [← n.pullCohomologyTwo_class, ← h3]
    obtain ⟨z, rfl⟩ := GlobalTheory.CatCoh.H2.mk_surjective _ z
    rfl

end GlobalTheory.AnPer
