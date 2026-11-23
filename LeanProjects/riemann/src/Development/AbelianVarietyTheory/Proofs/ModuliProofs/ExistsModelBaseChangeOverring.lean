import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem surjectiveOnStalks_of_dedekind_overring {O O' F : Type} [CommRing O] [IsDedekindDomain O] [Field F]
    [Algebra O F] [IsFractionRing O F] [CommRing O'] (β' : O' →+* F) (b : O →+* O') (hβ' : Function.Injective β')
    (h : ∀ x, β' (b x) = algebraMap O F x) : b.SurjectiveOnStalks := by
  intro P' hP'
  rw [RingHom.surjective_localRingHom_iff]
  intro s
  obtain ⟨x, y, hy, hs⟩ := IsFractionRing.div_surjective (A := O) (β' s)
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyF : algebraMap O F y ≠ 0 := fun e => hy0 (IsFractionRing.injective O F (by rw [e, map_zero]))
  have h1 : (1 : O') ∉ P' := P'.primeCompl.one_mem
  have key : ∀ u v : O, v * x = u * y → b v * s = b u := by
    intro u v e
    apply hβ'
    have e' := congrArg (algebraMap O F) e
    rw [map_mul, map_mul] at e'
    rw [map_mul, h, h, ← hs, ← mul_div_assoc, e', mul_div_assoc, div_self hyF, _root_.mul_one]
  by_cases hP : P'.comap b = ⊥
  · refine ⟨x, y, 1, h1, fun hm => hy0 ?_, by rw [_root_.one_mul, _root_.one_mul]; exact key x y (mul_comm _ _)⟩
    have : y ∈ P'.comap b := hm
    rwa [hP, Ideal.mem_bot] at this
  · have hd := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O hP
      (Localization.AtPrime (P'.comap b))
    have inj : Function.Injective (algebraMap O (Localization.AtPrime (P'.comap b))) :=
      IsLocalization.injective _ (P'.comap b).primeCompl_le_nonZeroDivisors
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap O (Localization.AtPrime (P'.comap b)) x) (algebraMap O _ y)
    obtain ⟨u, v, rfl⟩ := IsLocalization.exists_mk'_eq (P'.comap b).primeCompl c
    have hv : b v ∉ P' := v.2
    rcases hc with hc | hc
    · have e : u * x = v * y := by
        apply inj
        rw [map_mul, map_mul, ← hc, ← IsLocalization.mk'_spec' (Localization.AtPrime (P'.comap b)) u v]
        ring
      have e' := key _ _ e
      refine ⟨v, u, 1, h1, fun hm => hv ?_, by rw [_root_.one_mul, _root_.one_mul]; exact e'⟩
      rw [← e']
      exact P'.mul_mem_right _ hm
    · have e : v * x = u * y := by
        apply inj
        rw [map_mul, map_mul, ← hc, ← IsLocalization.mk'_spec' (Localization.AtPrime (P'.comap b)) u v]
        ring
      exact ⟨u, v, 1, h1, hv, by rw [_root_.one_mul, _root_.one_mul]; exact key _ _ e⟩

theorem flat_of_dedekind_of_injective {O O' : Type} [CommRing O] [IsDedekindDomain O] [CommRing O'] [IsDomain O']
    (b : O →+* O') (hb : Function.Injective b) : b.Flat := by
  algebraize [b]
  refine IsDedekindDomain.flat_iff_torsion_eq_bot.2 ?_
  rw [eq_bot_iff]
  rintro x ⟨a, ha⟩
  have ha' : b a * x = 0 := by
    rw [Submonoid.smul_def, Algebra.smul_def] at ha
    exact ha
  rcases mul_eq_zero.1 ha' with e | e
  · exact absurd (hb (by rw [e, map_zero])) (nonZeroDivisors.ne_zero a.2)
  · exact e

theorem isNormalScheme_of_flat_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : Y ⟶ X) [Flat f] [SurjectiveOnStalks f]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := by
  intro y
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks f y
  obtain ⟨h₁, h₂⟩ := hX (f y)
  let e := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

theorem Models.Cpt.exists_above_isIso_of_overring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (O' : Type) [CommRing O'] (β' : O' →+* F) (b : O →+* O') (C : Cpt c t β) (ν : SABMap t t (𝟙 U)), ν.φ = 𝟙 _ → IsDedFrac β → IsDedFrac β' → β'.comp b = β → ∃ (C' : Cpt c t β') (a : C'.Above C b (𝟙 U) ν), IsIso (pullback.lift a.π C'.s a.π_over) := by
  intro E _ _ _ H U F O _ _ c t β O' _ β' b C ν hν hβ hβ' hb
  obtain ⟨⟨_, _⟩, -, hF⟩ := hβ
  obtain ⟨⟨_, -⟩, -, hF'⟩ := hβ'
  have inj' : Function.Injective β' := by
    letI := β'.toAlgebra
    exact IsFractionRing.injective O' F
  have hbx : ∀ x, β' (b x) = β x := fun x => congrArg (fun f : O →+* F => f x) hb
  have inj : Function.Injective β := by
    letI := β.toAlgebra
    exact IsFractionRing.injective O F
  have injb : Function.Injective b := fun x y e => inj (by rw [← hbx, ← hbx, e])
  have hS : SurjectiveOnStalks (spMap b) := by
    letI := β.toAlgebra
    exact (HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)).2
      (surjectiveOnStalks_of_dedekind_overring β' b inj' hbx)
  have hFl : Flat (spMap b) := by
    rw [Flat.SpecMap_iff]
    exact flat_of_dedekind_of_injective b injb
  have hS' : SurjectiveOnStalks (pullback.fst C.s (spMap b)) :=
    MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback _ _).flip hS
  have hsp : spMap β' ≫ spMap b = spMap β := by
    rw [← hb, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hp : IsPullback (pullback.fst (pullback.snd C.s (spMap b)) (spMap β') ≫ pullback.fst C.s (spMap b))
      (pullback.snd (pullback.snd C.s (spMap b)) (spMap β')) C.s (spMap β) := by
    rw [← hsp]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  have hj : ((C.jQ ≫ hp.isoPullback.inv) ≫ pullback.fst (pullback.snd C.s (spMap b)) (spMap β')) ≫
      pullback.fst C.s (spMap b) = C.jQ ≫ pullback.fst _ _ := by
    simp only [Category.assoc, hp.isoPullback_inv_fst]
  obtain ⟨t', ⟨mu⟩⟩ : ∃ t' : SAB H (pullback C.s (spMap b)), Nonempty (SABMap t' C.t (pullback.fst C.s (spMap b))) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (pullback.fst C.s (spMap b)) C.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t t' ((C.jQ ≫ hp.isoPullback.inv) ≫
      pullback.fst (pullback.snd C.s (spMap b)) (spMap β')), C.m.φ = m'.φ ≫ mu.φ := by
    have aux : ∀ (g : U ⟶ pullback C.s (spMap b)) (e : U ⟶ C.X) (n : SABMap t C.t e),
        g ≫ pullback.fst C.s (spMap b) = e → ∃ m' : SABMap t t' g, n.φ = m'.φ ≫ mu.φ := by
      rintro g e n rfl
      exact ObjMaps.exists_sab_cancel mu n
    exact aux _ _ C.m hj
  have := C.flat
  have := C.jQ_open
  have hr : Set.range (C.jQ ≫ hp.isoPullback.inv) = hp.isoPullback.hom ⁻¹' Set.range C.jQ := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, by simp⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, by simp [hu]⟩
  have hiso : IsIso (pullback.lift (pullback.fst C.s (spMap b)) (pullback.snd C.s (spMap b)) pullback.condition) := by
    rw [pullback.lift_fst_snd]
    infer_instance
  refine ⟨⟨pullback C.s (spMap b), pullback.snd _ _,
    isNormalScheme_of_flat_of_surjectiveOnStalks (pullback.fst C.s (spMap b)) C.normal,
    ProjSpace.isProjOver_pullback_snd b C.proj, inferInstance, C.jQ ≫ hp.isoPullback.inv, ?_, inferInstance, ?_, t', m', ?_⟩,
    ⟨pullback.fst _ _, pullback.condition, inferInstance, mu, ?_, ?_⟩, hiso⟩
  · rw [Category.assoc, hp.isoPullback_inv_snd, C.jQ_over]
  · rw [hr]
    exact C.jQ_dense.preimage hp.isoPullback.hom.isOpenEmbedding.isOpenMap
  · rw [hr, ← C.ab_gen]
    ext x
    simp only [Set.mem_preimage]
    rw [← abLocus_pullback abLocusOne C.t.semi mu.cart.1, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      hp.isoPullback_hom_fst]
  · exact hj.trans (Category.id_comp _).symm
  · refine hm'.symm.trans ?_
    rw [hν, Category.id_comp]

end GlobalTheory
