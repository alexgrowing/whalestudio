import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinatesCompareNormalisedGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomInducedMapsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleIsoUniformisedGroupGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomTorsionCompatiblePeriodsLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgClosedFieldTorsionMapsCommuteHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPeriodsProjectionPeriodPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctorialOfUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
noncomputable section

namespace GlobalTheory.Mum.PowData

open GlobalTheory.Mum.FactorPol

set_option maxHeartbeats 1000000 in

theorem periodRel_of_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (h : D₀.toPre.X →+ D.toPre.X) (k : D.toPre.X →+ D₀.toPre.X), Lin U.toUnifPre U₀.toUnifPre q qB h → OnTorus U₀.toUnifPre U.toUnifPre j k → (∀ y, D₀.toPre.c (k y) = D.toPre.c y ≫ qB) ∧ PeriodRel D.toPre D₀.toPre qB h k := by
  intro R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG hG₀ U U₀ q inc j hinc hj iq adj qB h k L T
  have hA := hR.1
  have := hR.2
  have := U.gen_hom
  have := U₀.gen_hom
  haveI := hinc
  haveI := hj
  haveI : IsMonHom q := L.1
  obtain ⟨k', tk'⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre inc hinc
  have un₀ := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre
  have un := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D D A A G G U.toUnifPre U.toUnifPre
  have kh : ∀ χ, k' (h χ) = χ := congrFun ((un₀ _).2 _ _ (iq ▸ onTorus_comp tk' L.2.2.2) onTorus_id)
  have hinj : Function.Injective h := Function.LeftInverse.injective kh
  have C := GlobalTheory.Mum.Two.coord_of_lin R _ hA D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre q qB h L
  obtain ⟨c, hc, gc⟩ : ∃ c : A.A ⟶ A₀.A, IsMonHom c ∧ Gen₀ U.toUnifPre U₀.toUnifPre q c :=
    ⟨U.gen.inv ≫ (Over.pullback (jK R)).map q ≫ U₀.gen.hom, inferInstance, by simp [Gen₀]⟩
  obtain ⟨c', hc', gc'⟩ : ∃ c' : A₀.A ⟶ A.A, IsMonHom c' ∧ Gen₀ U₀.toUnifPre U.toUnifPre j c' :=
    ⟨U₀.gen.inv ≫ (Over.pullback (jK R)).map j ≫ U.gen.hom, inferInstance, by simp [Gen₀]⟩
  haveI := hc
  haveI := hc'
  obtain ⟨E, eG, eA⟩ := (GlobalTheory.UT.functorial_of_unif R _ hA D A G hG U).1 (q ≫ j) (c ≫ c') inferInstance inferInstance
    (by
      unfold Gen₀ at gc gc'
      rw [Functor.map_comp, Category.assoc, gc', ← Category.assoc, gc, Category.assoc])
  have hL := U.LG.isLB
  have hL₀ := U₀.LG.isLB

  have lamE : ∀ (T' : Over (Sp R)) (x y : T' ⟶ G),
      lam (cls U.LG.L hL) (x ≫ q ≫ j) y = lam (cls U₀.LG.L hL₀) (x ≫ q) (y ≫ q) := fun T' x y => by
    rw [lam_comm, ← Category.assoc, adj, lam_comm]
  have lamE' : ∀ (T' : Over (Sp R)) (x y : T' ⟶ G),
      lam (cls U.LG.L hL) x (y ≫ q ≫ j) = lam (cls U₀.LG.L hL₀) (x ≫ q) (y ≫ q) := fun T' x y => by
    rw [← Category.assoc, adj]
  have adjE : LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E.aG] U.LG.L) :=
    (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cube_two hL _ _ _).trans (Eq.trans (by rw [eG, lamE, lamE']) (cls_cube_two hL _ _ _).symm))
  have H₂ : LBIso (cubeLB G₀ ![fst G G ≫ q, snd G G ≫ q] U₀.LG.L)
      (cubeLB G ![fst G G ≫ E.aG, snd G G ≫ 𝟙 G] U.LG.L) :=
    (cls_eq_iff (LB.isLB_linComb hL₀ _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cube_two hL₀ _ _ _).trans (Eq.trans (by rw [eG, Category.comp_id, lamE]) (cls_cube_two hL _ _ _).symm))
  have H₃ := GlobalTheory.Mum.Two.lbIso_cubeLB_generic R _ D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre q q E.aG (𝟙 _) c c E.aA (𝟙 _)
    gc gc E.ext (by simp [Gen₀]) H₂
  obtain ⟨Ω, _, _, _, K⟩ := GlobalTheory.Mum.Two.exists_key R _ hA D D₀ A A₀ G G₀ hG hG₀ U U₀ q c qB h hc gc L C hinj
  obtain ⟨φ, hφ, hhφ⟩ := GlobalTheory.Mum.Two.periods_of_key R _ hA D D₀ A A₀ G G₀ hG hG₀ U U₀ q c qB h hc gc L C E E adjE H₃
    Ω K

  have eh : (⇑E.h : D.toPre.X → D.toPre.X) = ⇑h ∘ ⇑k :=
    (un _).2 _ _ (eG ▸ (lin_of_endU E).1.2.2.2) (onTorus_comp L.2.2.2 T)
  have hφk : ∀ y, φ y = k y := fun y => hinj ((hhφ y).trans (congrFun eh y))
  have hB := D.tau_bimult
  refine ⟨fun y => ?_, fun χ => ?_⟩
  · obtain ⟨g', ha, hg'⟩ := hφ y _ (GlobalTheory.TorusExt.isIota_iota hB y)
    have h1 := ha.1
    rw [hg'.1, (GlobalTheory.TorusExt.isIota_iota hB y).1] at h1
    rw [← hφk]
    refine GlobalTheory.Mum.Two.Fac.pt_ext R D₀.toPre Ω _ _ ?_
    simpa only [Category.assoc] using h1
  · obtain ⟨u, hu, -⟩ := C χ
    refine ⟨u, hu, fun y z J hJ => ?_⟩
    obtain ⟨g', ha, hg'⟩ := hφ y _ (GlobalTheory.TorusExt.isIota_iota hB y)
    have e := GlobalTheory.Mum.Two.act_val_frac R D₀.toPre D.toPre qB h Ω y (φ y) _ g' (GlobalTheory.TorusExt.isIota_iota hB y) hg' ha χ u hu
      z J hJ
    rwa [hφk] at e

end GlobalTheory.Mum.PowData
