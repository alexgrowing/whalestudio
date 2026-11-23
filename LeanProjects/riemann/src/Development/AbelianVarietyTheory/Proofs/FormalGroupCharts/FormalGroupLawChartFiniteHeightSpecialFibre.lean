import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.LocallyOfFiniteTypePullbackUnit
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PowSpanXLeAndFiniteQuotientOfLeSupPowSucc
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FiniteTorsionSpecialFibreOfUnif
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsToJetEq
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsNilpotentOfMemKerJetTruncR
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsUniversalChartOfFormalGroupChartStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFormalGroupLawOfChartOfJetChartStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsSeriesOfMorphismInChartsPowMulFormalGroupLawStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteHeight

theorem id_pow_left_proj {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (N : ℕ) :
    (𝟙 G' ^ N).left ≫ φ = φ ≫ (𝟙 G ^ N).left := by
  have h1 : (ObjPull.pushEquiv h G' (𝟙 G')).left = φ := Category.id_comp _
  have h2 : ObjPull.pushEquiv h G' (𝟙 G' ^ N) = ObjPull.pushEquiv h G' (𝟙 G') ≫ 𝟙 G ^ N := by
    rw [map_pow, MonObj.comp_pow, Category.comp_id]
  rw [← ObjPull.pushEquiv_left h, h2, Over.comp_left, h1]

theorem finite_torsion_pull {S S' Z : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (t : Z ⟶ S') (r : Z ⟶ S) (hr : t ≫ f = r) (N : ℕ)
    (hf : Finite {x : Over.mk r ⟶ G // x ^ N = 1}) :
    Finite {x : Over.mk t ⟶ G' // x ≫ (𝟙 G' ^ N) = 1} := by
  subst hr
  let e := ObjPull.pushEquiv h (Over.mk t)
  refine Finite.of_injective (β := {x : Over.mk (t ≫ f) ⟶ G // x ^ N = 1})
    (fun x => ⟨e x.1, ?_⟩) ?_
  · have hx : x.1 ^ N = 1 := by
      have := x.2
      rwa [MonObj.comp_pow, Category.comp_id] at this
    have : (e x.1) ^ N = 1 := by rw [← map_pow, hx, map_one]
    exact this
  · intro x y hxy
    exact Subtype.ext (e.injective (congrArg Subtype.val hxy))

theorem exists_pow_span_X_le_span_map_residue_mulF : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T)))) (_ : Out.UnifPre (maximalIdeal T) D A G) (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∀ N : ℕ, 1 ≤ N → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS (ResidueField T) 1 d)) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (mulF F.F N j)) := by
  intro T _ _ _ G _ _ D A U d F x hx N hN
  obtain ⟨x0, hu, hρ⟩ := GlobalTheory.T.isUniversalChart_of_formalGroupChart T G U.smooth d F x hx
  have hlaw := GlobalTheory.T.isFormalGroupLawOfChart_of_jetChart T G d F x hx x0 hu hρ
  have hmap := GlobalTheory.T.isSeriesOfMorphismInCharts_pow_mulFormalGroupLaw T G d x0 hu F.F hlaw N
  have hp := isGrpPullback_pullback G (Spec.map (CommRingCat.ofHom (residue T)))
  obtain ⟨x', hu', -, hm, -⟩ := GlobalTheory.ChartBaseChange.chartBaseChange GlobalTheory.JetSer.jetAlg
    (GlobalTheory.JetSer.serSt_of_jetAlgSt GlobalTheory.JetSer.jetAlg) T (ResidueField T) (residue T) G _ _ hp d x0 hu
  have hm' := hm _ _ _ (id_pow_left_proj hp N) hmap
  have hsm := U.smooth
  have : LocallyOfFiniteType ((Over.pullback (Spec.map (CommRingCat.ofHom (residue T)))).obj G).hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hp.1 inferInstance
  obtain ⟨M, hM⟩ := GlobalTheory.JetSer.exists_pow_le_span_sup_pow_succ (ResidueField T) _ _ (by
      rw [MonObj.comp_pow, Category.comp_id]
      have : η[(Over.pullback (Spec.map (CommRingCat.ofHom (residue T)))).obj G] = 1 := by
        rw [Hom.one_def, toUnit_unit, Category.id_comp]
      rw [this, one_pow]) (fun Ω _ _ t => by
      obtain ⟨b, rfl⟩ := Spec.map_surjective t
      refine finite_torsion_pull hp _ (Geo.Tor.spMap (b.hom.comp (residue T))) ?_ N
        (GlobalTheory.finite_torsion_special_fibre_of_unif T G D A U Ω _ (fun a ha => ?_) N hN)
      · rw [← Spec.map_comp]
        rfl
      · rw [RingHom.comp_apply, (residue_eq_zero_iff a).2 ha, map_zero]) d x' hu' _ hm'
  exact ⟨M, (GlobalTheory.pow_span_X_le_and_finite_quotient_of_le_sup_pow_succ _ _ _ M hM).1⟩

end GlobalTheory.FiniteHeight
