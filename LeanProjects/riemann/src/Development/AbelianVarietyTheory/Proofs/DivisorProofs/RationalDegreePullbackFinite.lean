import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.RatFibreDeg

theorem residueDegree_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : X ⟶ Y) [SurjectiveOnStalks f]
    (x : X) : f.residueDegree x = 1 := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have hs : Function.Surjective (f.residueFieldMap x) := by
    intro a
    obtain ⟨b, rfl⟩ := X.residue_surjective x a
    obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
    exact ⟨Y.residue _ c, congr($(Scheme.residue_residueFieldMap f x).hom c)⟩
  exact Module.finrank_of_bijective_algebraMap ⟨(f.residueFieldMap x).hom.injective, hs⟩

theorem apply_genericPoint_of_flat {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [Flat f] : f (genericPoint X) = genericPoint Y := by
  obtain ⟨z, hz, e⟩ := Flat.generalizingMap f (genericPoint_specializes (f (genericPoint X)))
  rw [← e, (hz.antisymm (genericPoint_specializes z)).eq]

variable {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k)

theorem flat_fst : Flat (ratFibre.fst p) := by
  have : Flat (spMap (Int.castRingHom ℚ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat ℚ (nonZeroDivisors ℤ))
  exact MorphismProperty.of_isPullback (P := @Flat) (ratFibre.isPullback p).flip inferInstance

theorem isPreimmersion_fst : IsPreimmersion (ratFibre.fst p) := by
  have : IsPreimmersion (spMap (Int.castRingHom ℚ)) :=
    IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion) (ratFibre.isPullback p).flip
    inferInstance

theorem ratDeg_pull : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (Y : Scheme.{0})
    [IsIntegral X] [IsIntegral Y] (ν : Y ⟶ X) [IsFinite ν], IsProjCurve ℚ (ratFibre p) →
    IsProjCurve ℚ (ratFibre (ν ≫ p)) → ν (genericPoint Y) = genericPoint X →
    ∀ L : LB X, L.IsLB →
      ratDeg (ν ≫ p) (L.pull ν) = (ν.residueDegree (genericPoint Y) : ℤ) * ratDeg p L := by
  intro k _ X p Y _ _ ν _ hX hY hν L hL
  have := hX.isIntegral
  have := hY.isIntegral
  have := flat_fst p
  have := flat_fst (ν ≫ p)
  have := isPreimmersion_fst p
  have := isPreimmersion_fst (ν ≫ p)
  have : IsFinite (ratFibre.map p ν) :=
    MorphismProperty.of_isPullback (P := @IsFinite) (ratFibre.isPullback_map p ν) inferInstance
  have e := ratFibre.map_fst p ν
  have gX := apply_genericPoint_of_flat (ratFibre.fst p)
  have gY := apply_genericPoint_of_flat (ratFibre.fst (ν ≫ p))
  have hg : ratFibre.map p ν (genericPoint _) = genericPoint _ := by
    refine (ratFibre.fst p).isEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, gY, hν, gX]
  have hr : (ratFibre.map p ν).residueDegree (genericPoint _) =
      ν.residueDegree (genericPoint Y) := by
    have h₁ := CurveDegreesCompare.residueDegree_comp (ratFibre.map p ν) (ratFibre.fst p)
      (genericPoint _)
    rw [e, CurveDegreesCompare.residueDegree_comp, gY] at h₁
    simpa only [residueDegree_of_surjectiveOnStalks, mul_one, one_mul] using h₁.symm
  have hf (r : ℚ) : (ratFibre.map p ν).appTop (algebraMap ℚ Γ(ratFibre p, ⊤) r) =
      algebraMap ℚ Γ(ratFibre (ν ≫ p), ⊤) r :=
    RingHom.congr_fun (RingHom.ext_rat ((ratFibre.map p ν).appTop.hom.comp (algebraMap ℚ _))
      (algebraMap ℚ _)) r
  have hN := Semi.LB.isLB_pull hL (ratFibre.fst p)
  have hM := Semi.LB.isLB_pull hL ν
  have h₁ := ProjFin.interNumOn_eq_residueDegree_mul ℚ _ _ (ratFibre.map p ν) hX.isProjOver
    hX.dim_eq hg _ hN
  have h₂ := interNumOn_eq_interNum_pull (k := ℚ) (L := ![L.pull (ratFibre.fst p)]) hf
    (fun i => by fin_cases i; exact hN)
  have hM' := Semi.LB.isLB_pull hM (ratFibre.fst (ν ≫ p))
  rw [ratDeg_eq_degLB hM, ratDeg_eq_degLB hL, hX.degLB_eq_interNum hN, hY.degLB_eq_interNum hM',
    ← hr, ← h₁, h₂]
  refine interNum_congr_cls _ _ (fun i => by fin_cases i; exact hM')
    (fun i => by fin_cases i; exact Semi.LB.isLB_pull hN _) fun i => ?_
  fin_cases i
  refine (CechPic.cls_pull hM _ _).trans (Eq.trans ?_ (CechPic.cls_pull hN _ _).symm)
  rw [CechPic.cls_pull hL ν hM, CechPic.cls_pull hL _ hN, ← CechPic.pull_comp, ← CechPic.pull_comp, e]

end GlobalTheory.RatFibreDeg
