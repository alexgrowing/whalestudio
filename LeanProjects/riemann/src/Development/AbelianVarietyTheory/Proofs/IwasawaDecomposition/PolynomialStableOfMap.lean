import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.Models

namespace GlobalTheory.TorRef

theorem polStable_of_polMap (hM : PolMapSt) : PolStableSt := by
  intro E _ _ _ H D l Xo c Y T φ hφ hpol σ γ γ₀ r ν hσ _ hγ hr
  haveI := c.fin
  haveI : NumberField c.F := {}
  have hβ : IsDedFrac (algebraMap (𝓞 c.F) c.F) := ⟨⟨inferInstance, inferInstance⟩, inferInstance,
    (inferInstance : IsFractionRing (𝓞 c.F) c.F)⟩
  have hO : Algebra.FiniteType ℤ (𝓞 c.F) := inferInstance
  have inv : ∀ {R : Type} [CommRing R] (g : R ≃+* R), spMap g.toRingHom ≫ spMap g.symm.toRingHom = 𝟙 _ := by
    intro R _ g
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact g.apply_symm_apply x
  have hj : T.Z.j ≫ T.Z.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, T.Z.jQ_over]
  have e : spMap (algebraMap (𝓞 c.F) c.F) ≫ spMap γ₀.toRingHom = spMap γ.toRingHom ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    first
    | exact congrArg _ (hγ x)
    | simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]; exact congrArg _ (hγ x)
    | simp [hγ x]
  obtain ⟨π, hπ, mu, hfin, hjπ, hm, hBD⟩ := hM E H D l l Xo Xo c c (𝓞 c.F) (𝓞 c.F) _ _ T.Z T.Z T.BD T.BD φ T.m0
    γ₀.toRingHom σ r.hom ν hβ hβ hO hφ hσ hpol hpol (by rw [hj, reassoc_of% hr, reassoc_of% hj, e])
  have : IsIso (spMap γ₀.toRingHom) := ⟨⟨spMap γ₀.symm.toRingHom, inv γ₀, inv γ₀.symm⟩⟩
  have hπe : π = pullback.lift π T.Z.s hπ ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
  have : IsFinite π := by
    rw [hπe]
    infer_instance
  have : IsIntegralHom π := inferInstance
  obtain ⟨-, -, -, h1, h2, h3, h4⟩ := GlobalTheory.genericPart_dense_proOpen (𝓞 c.F) c.F T.Z.X _ T.Z.s T.Z.jQ T.Z.flat
    T.Z.proj T.Z.jQ_open T.Z.jQ_dense
  have hN : IsLocallyNoetherian T.Z.X :=
    (GlobalTheory.genericPart_dense_proOpen (𝓞 c.F) c.F T.Z.X _ T.Z.s T.Z.jQ T.Z.flat T.Z.proj T.Z.jQ_open T.Z.jQ_dense).1
  obtain ⟨ρ', ⟨k1, k2⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart T.Z.X _ T.Z.X T.Z.X T.Z.j T.Z.normal h1 h2 h3 h4
    π (𝟙 _) (r.inv ≫ T.Z.j) this (by rw [Category.assoc, hjπ, Iso.inv_hom_id_assoc, Category.comp_id])
  have : ∀ x : T.Z.X, _root_.IsReduced (T.Z.X.presheaf.stalk x) := fun x =>
    have := (T.Z.normal x).1
    inferInstance
  have := isReduced_of_isReduced_stalk T.Z.X
  haveI : IsDominant T.Z.j := h3
  have hρ : π ≫ ρ' = 𝟙 _ := by
    refine ext_of_isDominant_of_isSeparated π ?_ T.Z.j ?_
    · rw [Category.assoc, k2, Category.comp_id, Category.id_comp]
    · rw [reassoc_of% hjπ, k1, Iso.hom_inv_id_assoc, Category.comp_id]
  exact ⟨⟨π, ρ', hρ, k2⟩, mu, hπ, hjπ, hm, hBD.symm⟩

end GlobalTheory.TorRef
