import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency.types false in

theorem modelAway_basic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (a : 𝓞 c.F) (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (C : Model Xo c ω), IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ a R _ b.toAlgebra → ∀ jX : Xo.XF c ⟶ pullback Z.s (spMap b), jX ≫ pullback.fst _ _ = Z.j → IsOpenImmersion (pullback.fst Z.s (spMap b)) ∧ IsLocallyNoetherian (pullback Z.s (spMap b)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (pullback Z.s (spMap b)) ∧ (∃ z : pullback Z.s (spMap b) ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) ∧ IsPreimmersion jX ∧ Flat jX ∧ IsDominant jX ∧ QuasiCompact jX ∧ jX ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap ω ∧ (∀ u : Xo.XF c ⟶ pullback Z.s (spMap b), u ≫ pullback.fst _ _ = Z.j → u = jX) := by
  intro E _ _ _ H D l Xo c Z R _ a b ω _ _ hωb hloc jX hjX
  have := c.fin
  have : NumberField c.F := {}

  have hb : IsOpenImmersion (spMap b) := by
    let := b.toAlgebra
    exact IsOpenImmersion.of_isLocalization (R := 𝓞 c.F) (S := R) a
  have hfst : IsOpenImmersion (pullback.fst Z.s (spMap b)) := inferInstance
  obtain ⟨hN, -, -, hpre, hfl, hdom, hqc⟩ :=
    genericPart_dense_proOpen (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open Z.jQ_dense
  have hj : Z.j = Z.jQ ≫ pullback.fst _ _ := rfl
  rw [hj] at hjX

  have hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (pullback Z.s (spMap b)) := by
    delta ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme
    intro x
    obtain ⟨h1, h2⟩ := Z.normal (pullback.fst Z.s (spMap b) x)
    let e := (asIso ((pullback.fst Z.s (spMap b)).stalkMap x)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  have hprop : IsProper Z.s := by
    obtain ⟨N, i, hi, e⟩ := Z.proj
    have := isProper_str (𝓞 c.F) N
    rw [← e]; infer_instance
  have hZfl : Flat Z.s := Z.flat
  have hZint : LocallyOfFiniteType (spMap (algebraMap ℤ (𝓞 c.F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_finite (RingHom.finite_algebraMap.mpr inferInstance)
  have hZintf : Flat (spMap (algebraMap ℤ (𝓞 c.F))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hc1 : IsDominant (jX ≫ pullback.fst Z.s (spMap b)) := hjX ▸ hdom
  have hc2 : IsPreimmersion (jX ≫ pullback.fst Z.s (spMap b)) := hjX ▸ hpre
  have hc3 : Flat (jX ≫ pullback.fst Z.s (spMap b)) := hjX ▸ hfl
  have hc4 : QuasiCompact (jX ≫ pullback.fst Z.s (spMap b)) := hjX ▸ hqc
  refine ⟨hfst, isLocallyNoetherian_of_isOpenImmersion (pullback.fst Z.s (spMap b)), hnorm,
    ⟨pullback.fst _ _ ≫ Z.s ≫ spMap (algebraMap ℤ (𝓞 c.F)), inferInstance, inferInstance⟩,
    IsPreimmersion.of_comp jX (pullback.fst Z.s (spMap b)),
    MorphismProperty.of_postcomp @Flat (W' := @IsOpenImmersion) _ _ hfst hc3,
    IsDominant.of_comp_of_isOpenImmersion jX (pullback.fst Z.s (spMap b)),
    QuasiCompact.of_comp jX (pullback.fst Z.s (spMap b)), ?_, ?_⟩
  · rw [← cancel_mono (spMap b), Category.assoc, ← pullback.condition, ← Category.assoc, hjX, Category.assoc,
      pullback.condition, ← Category.assoc, Z.jQ_over, Category.assoc]
    congr 1
    rw [← hωb]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  · intro u hu
    rw [hj] at hu
    exact (cancel_mono (pullback.fst Z.s (spMap b))).mp (hu.trans hjX.symm)

end GlobalTheory
