import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenStabilizer

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison.GeoB

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

theorem exists_galMap_apply [IsGalois k Ω] (y z : GlobalTheory.Et.geom Ω p)
    (h : pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) y =
      pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) z) :
    ∃ σ : Ω ≃ₐ[k] Ω, GlobalTheory.Et.galMap Ω p σ y = z := by
  set ψ := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with hψ
  obtain ⟨R, f, hf, x₀, hx₀⟩ := Scheme.exists_Spec_apply_eq (pullback.fst p ψ y)
  let κ : CommRingCat.of k ⟶ R := Spec.preimage (f ≫ p)
  let _ : Algebra k R := κ.hom.toAlgebra
  let iΩ : CommRingCat.of Ω ⟶ CommRingCat.of (Ω ⊗[k] R) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let iR : R ⟶ CommRingCat.of (Ω ⊗[k] R) := CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  have hout : IsPullback (Spec.map iΩ) (Spec.map iR) ψ (f ≫ p) := by
    have := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k Ω R)
    rw [← Spec.map_preimage (f ≫ p)]
    exact this
  have t : IsPullback (pullback.snd p ψ) (pullback.fst p ψ) ψ p := (IsPullback.of_hasPullback p ψ).flip
  have L := IsPullback.of_right' hout t
  set Φ := t.lift (Spec.map iΩ) (Spec.map iR ≫ f) (by rw [hout.w, Category.assoc]) with hΦ
  have hΦs : Φ ≫ pullback.snd p ψ = Spec.map iΩ := t.lift_fst _ _ _
  have hΦf : Φ ≫ pullback.fst p ψ = Spec.map iR ≫ f := t.lift_snd _ _ _
  have hrange : ∀ w : GlobalTheory.Et.geom Ω p, pullback.fst p ψ w ∈ Set.range f → ∃ P, Φ P = w := by
    intro w hw
    have : w ∈ Set.range (pullback.fst (pullback.fst p ψ) f) := by
      rw [Scheme.Pullback.range_fst]; exact hw
    obtain ⟨v, rfl⟩ := this
    refine ⟨L.isoPullback.inv v, ?_⟩
    rw [← Scheme.Hom.comp_apply, L.isoPullback_inv_fst]
  obtain ⟨P, rfl⟩ := hrange y ⟨x₀, hx₀⟩
  obtain ⟨Q, rfl⟩ := hrange z ⟨x₀, hx₀.trans h⟩
  have hfst : ∀ P, pullback.fst p ψ (Φ P) = f (Spec.map iR P) := fun P => by
    rw [← Scheme.Hom.comp_apply, hΦf, Scheme.Hom.comp_apply]
  have hPQ : Spec.map iR P = Spec.map iR Q := f.isOpenEmbedding.injective (by rw [← hfst, ← hfst, h])
  have hPQ' : P.asIdeal.comap iR.hom = Q.asIdeal.comap iR.hom := congrArg PrimeSpectrum.asIdeal hPQ
  have : P.asIdeal.IsPrime := P.2
  have : Q.asIdeal.IsPrime := Q.2
  obtain ⟨σ, hσ⟩ := GeoA.exists_comap_eq (k := k) (Ω := Ω) R P.asIdeal Q.asIdeal hPQ'
  refine ⟨σ, ?_⟩
  let T : CommRingCat.of (Ω ⊗[k] R) ⟶ CommRingCat.of (Ω ⊗[k] R) :=
    CommRingCat.ofHom (GeoA.act R σ).toRingEquiv.toRingHom
  have hTR : iR ≫ T = iR := by
    ext r
    change GeoA.act R σ (1 ⊗ₜ r) = 1 ⊗ₜ r
    simp
  have hTΩ : iΩ ≫ T = CommRingCat.ofHom (σ : Ω →+* Ω) ≫ iΩ := by
    ext a
    change GeoA.act R σ (a ⊗ₜ 1) = σ a ⊗ₜ 1
    simp
  have heq : Spec.map T ≫ Φ = Φ ≫ GlobalTheory.Et.galMap Ω p σ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_fst, hΦf, ← Category.assoc, ← Spec.map_comp, hTR]
    · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_snd, hΦs, ← Category.assoc, hΦs, ← Spec.map_comp,
        ← Spec.map_comp, hTΩ]
  have hTP : Spec.map T P = Q := PrimeSpectrum.ext (by rw [Spec.map_apply]; exact hσ.symm)
  rw [← hTP, ← Scheme.Hom.comp_apply, ← heq, Scheme.Hom.comp_apply]

end CrystallineSemistableComparison.GeoB
