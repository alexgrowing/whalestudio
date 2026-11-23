import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

open scoped TensorProduct

namespace GlobalTheory.AffChartSmooth

theorem mem_of_closedPoint_mem {R : Type} [CommRing R] [IsLocalRing R] {U : Set (Sp R)}
    (hU : IsOpen U) (h : IsLocalRing.closedPoint R ∈ U) (x : Sp R) : x ∈ U := by
  have hx : (x : PrimeSpectrum R) ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal x.2.ne_top)
  exact hx.mem_open hU h

theorem exists_smooth_chart : ∀ (Λ : Type) [CommRing Λ] (ι₀ : Λ →+* ℂ) (M : Scheme.{0}) (s : M ⟶ Sp Λ) (V : M.Opens) (d : ℕ),
    SmoothOfRelativeDimension d (V.ι ≫ s) → ∀ (R : Type) [CommRing R] [Algebra ℂ R] [IsLocalRing R] (b : Sp R ⟶ M),
    (∀ x, b.base x ∈ V) → b ≫ s = spMap ((algebraMap ℂ R).comp ι₀) →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra ℂ B) (_ : Algebra.Smooth ℂ B) (g : Sp B ⟶ M) (j : B →ₐ[ℂ] R),
      spMap (j : B →+* R) ≫ g = b := by
  intro Λ _ ι₀ M s V d hd R _ _ _ b hbV hbs
  haveI : Smooth (V.ι ≫ s) := SmoothOfRelativeDimension.smooth d _
  obtain ⟨W, hW, hxW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp M.isBasis_affineOpens)
    (hbV (IsLocalRing.closedPoint R))
  have hbW : ∀ x, b.base x ∈ W := fun x =>
    mem_of_closedPoint_mem (U := b.base ⁻¹' (W : Set M)) (W.2.preimage b.base.hom.continuous) hxW x
  haveI : Smooth ((Scheme.Opens.ι (X := M) W) ≫ s) := by
    rw [← Scheme.homOfLE_ι M hWV, Category.assoc]; infer_instance
  have hWa : IsAffineOpen W := hW
  let e := hWa.isoSpec
  let f : Spec Γ(M, W) ⟶ Sp Λ := e.inv ≫ (Scheme.Opens.ι (X := M) W) ≫ s
  have hf : Smooth f := inferInstance
  let φ := Spec.preimage f
  have hφ : φ.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 (by rw [Spec.map_preimage]; exact hf)

  letI : Algebra Λ Γ(M, W) := φ.hom.toAlgebra
  haveI : Algebra.Smooth Λ Γ(M, W) := RingHom.smooth_algebraMap.1 hφ
  letI : Algebra Λ ℂ := ι₀.toAlgebra
  have hrange : Set.range b.base ⊆ Set.range (Scheme.Opens.ι (X := M) W).base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hbW x
  let b' : Sp R ⟶ W := IsOpenImmersion.lift (Scheme.Opens.ι (X := M) W) b hrange
  have hb' : b' ≫ (Scheme.Opens.ι (X := M) W) = b := IsOpenImmersion.lift_fac _ _ _
  let ψ := Spec.preimage (b' ≫ e.hom)
  have hψ : Spec.map ψ = b' ≫ e.hom := Spec.map_preimage _
  have hcomp : φ ≫ ψ = CommRingCat.ofHom ((algebraMap ℂ R).comp ι₀) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, Spec.map_preimage]
    simp only [f, Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hb', hbs]
  letI : Algebra Λ R := ((algebraMap ℂ R).comp ι₀).toAlgebra
  haveI : IsScalarTower Λ ℂ R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g' : Γ(M, W) →ₐ[Λ] R :=
    { ψ.hom with
      commutes' := fun r => by
        have := congrArg (fun h => h.hom r) hcomp
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
        exact this }
  let j : ℂ ⊗[Λ] Γ(M, W) →ₐ[ℂ] R :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ R) g' (fun _ _ => Commute.all _ _)
  refine ⟨ℂ ⊗[Λ] Γ(M, W), inferInstance, inferInstance, inferInstance,
    spMap (Algebra.TensorProduct.includeRight (R := Λ) (A := ℂ) (B := Γ(M, W))).toRingHom ≫ e.inv ≫ (Scheme.Opens.ι (X := M) W), j, ?_⟩
  have hj : (j : ℂ ⊗[Λ] Γ(M, W) →+* R).comp (Algebra.TensorProduct.includeRight (R := Λ) (A := ℂ) (B := Γ(M, W))).toRingHom = ψ.hom := by
    ext a
    simp [j, g']
  rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hj]
  change Spec.map ψ ≫ _ = _
  rw [hψ, Category.assoc, Iso.hom_inv_id_assoc, hb']

end GlobalTheory.AffChartSmooth
