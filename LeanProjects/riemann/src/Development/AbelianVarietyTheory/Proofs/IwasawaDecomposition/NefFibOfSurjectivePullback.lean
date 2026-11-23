import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonnegStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforwardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreimagePositiveResidueDegreeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGenericStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.NefDescent

theorem fibre_point (W Z : Scheme.{0}) (g : W ⟶ Z) [QuasiCompact g] [LocallyOfFiniteType g] (z : Z)
    (hz : z ∈ Set.range g) : ∃ w, g w = z ∧ 0 < g.residueDegree w :=
  GlobalTheory.T.exists_preimage_positive_residue_degree W Z g z hz

theorem red_genericPoint (W : Scheme.{0}) (w : W) (Z : Closeds W) (hZ : (Z : Set W) = closure {w})
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme] :
    redι Z (genericPoint _) = w := by
  have h1 : closure {redι Z (genericPoint _)} = closure ({w} : Set W) := by
    rw [← Set.image_singleton, IsClosedMap.closure_image_eq_of_continuous (redι Z).isClosedMap
      (redι Z).continuous, (genericPoint_spec _).def, Set.image_univ, range_redι]
    exact hZ
  exact (inseparable_iff_closure_eq.2 h1).eq

theorem dim_eq_one (Z' Z : Scheme.{0}) [IsIntegral Z'] [IsIntegral Z] [IsNoetherian Z] (f : Z' ⟶ Z) [IsProper f]
    (hd : topologicalKrullDim Z = 1) (hη : f (genericPoint Z') = genericPoint Z)
    (hdeg : 0 < f.residueDegree (genericPoint Z')) : topologicalKrullDim Z' = 1 :=
  GlobalTheory.T.krullDim_one_of_finite_generic Z' Z f hd hη hdeg

theorem isFinite_of_dim (Z' Z : Scheme.{0}) [IsIntegral Z'] [IsIntegral Z] [IsNoetherian Z'] (f : Z' ⟶ Z) [IsProper f]
    (hd' : topologicalKrullDim Z' = 1) (hd : topologicalKrullDim Z = 1)
    (hη : f (genericPoint Z') = genericPoint Z) : IsFinite f := by
  have hsurj : Function.Surjective f := by
    have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    have hm : genericPoint Z ∈ Set.range f := ⟨_, hη⟩
    have : closure {genericPoint Z} ⊆ Set.range f := hc.closure_subset_iff.2 (Set.singleton_subset_iff.2 hm)
    rw [(genericPoint_spec Z).def] at this
    exact fun z => this (Set.mem_univ z)
  obtain ⟨x, hx⟩ := ProperCurve.exists_ne_genericPoint hd
  obtain ⟨x₀, rfl⟩ := hsurj x
  have := ProperCurve.locallyQuasiFinite_of_ne hd' f (x₀ := x₀) (by rw [hη]; exact hx)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

theorem nefFib_of_pull : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), Function.Surjective π → ∀ (L : HermLB p), ArInt.NefFib (L.pull π hπ) → ArInt.NefFib L := by
  intro k _ _ X Y p q hp hq π hπ hsurj L hL
  refine GlobalTheory.T.nefFib_of_curve_degrees_nonneg k X p L ?_
  intro Z i _ _ r _ _ hd
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hq).1
  have : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π p
  have : Surjective π := ⟨hsurj⟩
  have : IsNoetherian Y := isNoetherian_of_isProjOver hq
  have : IsNoetherian X := isNoetherian_of_isProjOver hp
  have : IsNoetherian Z := by
    have := LocallyOfFiniteType.isLocallyNoetherian i
    have := QuasiCompact.compactSpace_of_compactSpace i
    exact {}
  let g := pullback.snd π i
  have : IsProper g := inferInstance
  have : Surjective g := inferInstance
  obtain ⟨w, hw, hdeg⟩ := fibre_point _ Z g (genericPoint Z) (g.surjective _)
  let C : Closeds (pullback π i : Scheme.{0}) := ⟨closure {w}, isClosed_closure⟩
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  have hgen := red_genericPoint _ w C rfl
  let f := redι C ≫ g
  let i' := redι C ≫ pullback.fst π i
  have hη : f (genericPoint _) = genericPoint Z := by
    simp only [f, Scheme.Hom.comp_apply, hgen, hw]
  have hdeg' : 0 < f.residueDegree (genericPoint _) := by
    simp only [f, CurveDegreesCompare.residueDegree_comp, hgen, GlobalTheory.Published.residueDegree_of_isClosedImmersion, mul_one]
    exact hdeg
  have hd' := dim_eq_one _ Z f hd hη hdeg'
  have : IsNoetherian (Scheme.IdealSheafData.vanishingIdeal C).subscheme := by
    have := LocallyOfFiniteType.isLocallyNoetherian i'
    have := QuasiCompact.compactSpace_of_compactSpace i'
    exact {}
  have : IsFinite f := isFinite_of_dim _ Z f hd' hd hη
  letI : Algebra (ZMod r) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) := algebraΓAlong (ZMod r) f
  have h1 := hL _ i' (ZMod r) hd'
  have hN : (L.B.pull i).IsLB := LB.isLB_pull L.isLB i
  have hcomm : i' ≫ π = f ≫ i := by simp only [i', f, g, Category.assoc, pullback.condition]
  have e1 : topSelfIntersection (ZMod r) ((L.pull π hπ).B.pull i') 1 = topSelfIntersection (ZMod r) ((L.B.pull i).pull f) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod r) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB π) i')
      (fun _ => LB.isLB_pull hN f) fun _ => ?_
    show pull i' (pull π (cls L.B L.isLB)) = pull f (pull i (cls L.B L.isLB))
    rw [← pull_comp, ← pull_comp, hcomm]
  have e2 : topSelfIntersection (ZMod r) ((L.B.pull i).pull f) 1 = interNumOn (ZMod r) f (fun _ : Fin 1 => L.B.pull i) :=
    (interNumOn_const_eq_topSelf (k := ZMod r) (fun _ => rfl) hN 1).symm
  have e3 : interNumOn (ZMod r) f (fun _ : Fin 1 => L.B.pull i) = interNumOn (ZMod r) f ![L.B.pull i] :=
    congrArg _ (funext fun j => by fin_cases j; rfl)
  have hproj : IsProjOver (strHom (ZMod r) Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod r) Z ≫ spMap (Int.castRingHom (ZMod r)) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod r) Z ≫ spMap (Int.castRingHom (ZMod r))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod r) Z) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod r)))
    exact ProperCurve.isProjOver_of_isProper _ hd
  have e4 := GlobalTheory.T.intersection_number_finite_pushforward (ZMod r) Z _ f hproj hd hη (L.B.pull i) hN
  have e5 : interNum (ZMod r) (structureModule Z) ![L.B.pull i] = topSelfIntersection (ZMod r) (L.B.pull i) 1 := by
    rw [topSelf_def]
    exact congrArg _ (funext fun j => by fin_cases j; rfl)
  have hT : 0 ≤ (f.residueDegree (genericPoint _) : ℤ) * topSelfIntersection (ZMod r) (L.B.pull i) 1 := by
    rw [← e5, ← e4, ← e3, ← e2, ← e1]
    exact h1
  exact nonneg_of_mul_nonneg_right hT (by exact_mod_cast hdeg')

end GlobalTheory.NefDescent
