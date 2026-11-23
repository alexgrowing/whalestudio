import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedClosureOfPointProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosureClosedSubschemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureIntegralEqGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsomOfChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArith
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mix.cycInt_genericFibre : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f : CxPts p (τ.comp (algebraMap k K)) → ℝ) (x : G), Order.coheight x = 1 → cycInt (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) x = cycInt L f (j x) := by
  intro k K _ _ _ _ X G _ p q j hp τ e hX L f x hx
  obtain ⟨hGi, hGn, hGproj, hGdim, hgen, hinj, hstalk, hcoh, hempty⟩ :=
    GlobalTheory.Mix.genericFibre_facts k K X G p q j hp (e + 1) hX
  obtain ⟨hZi, hZgen, hZdim, hZuniv⟩ := GlobalTheory.ClosFacts.clos_facts X (j x)
  obtain ⟨hxi, hxgen, -, hxuniv⟩ := GlobalTheory.ClosFacts.clos_facts G x

  have hK : CharZero K := by
    have := hX.charZero_base
    exact (RingHom.charZero_iff (IsFractionRing.injective k K)).1 inferInstance
  have hc : CharZero Γ(clos (j x), ⊤) := by
    obtain ⟨g0, hg0, -, -, -⟩ := hZuniv (clos x) (closι x ≫ j) (by
      simp only [Scheme.Hom.comp_apply, hxgen])
    have : IsDomain Γ(clos x, ⊤) := inferInstance
    let φ : K →+* Γ(clos x, ⊤) :=
      ((closι x ≫ q).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    have : CharZero Γ(clos x, ⊤) := (RingHom.charZero_iff φ.injective).1 hK
    exact g0.appTop.hom.charZero
  have hdim : topologicalKrullDim (clos (j x)) = (e + 1 : ℕ) := by
    rw [hZdim]
    have h1 := (GlobalTheory.MixHt.dimOne k X p (GlobalTheory.MixHt.isAmb_of_isArithVar hX) (e + 1) hX.dim_eq).1 (j x)
    exact h1.1 ((hcoh x).trans hx)
  have hZ : IsArithVar (closι (j x) ≫ p) e := hX.of_isClosedImmersion (closι (j x)) hc hdim
  haveI := hZi
  let G' := Limits.pullback (closι (j x) ≫ p) (spMap (algebraMap k K))
  let j' : G' ⟶ clos (j x) := Limits.pullback.fst _ _
  let q' : G' ⟶ Sp K := Limits.pullback.snd _ _
  have hp' : IsPullback j' q' (closι (j x) ≫ p) (spMap (algebraMap k K)) := IsPullback.of_hasPullback _ _
  obtain ⟨hG'i, -, hG'proj, -, hG'gen, -, -, -, -⟩ :=
    GlobalTheory.Mix.genericFibre_facts k K (clos (j x)) G' (closι (j x) ≫ p) q' j' hp' e hZ
  have hw : (j' ≫ closι (j x)) ≫ p = q' ≫ spMap (algebraMap k K) := by
    rw [Category.assoc]; exact hp'.w
  let g : G' ⟶ G := hp.lift (j' ≫ closι (j x)) q' hw
  have hg1 : g ≫ j = j' ≫ closι (j x) := hp.lift_fst _ _ hw
  have hg2 : g ≫ q = q' := hp.lift_snd _ _ hw
  have hp'' : IsPullback j' (g ≫ q) (closι (j x) ≫ p) (spMap (algebraMap k K)) := by rw [hg2]; exact hp'
  have hsq : IsPullback g j' j (closι (j x)) := IsPullback.of_right hp''.flip hg1 hp.flip
  have : IsClosedImmersion g := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip inferInstance
  have hgx : g (genericPoint G') = x := by
    apply hinj
    rw [← Scheme.Hom.comp_apply, hg1, Scheme.Hom.comp_apply, hG'gen, hZgen]
  have hproj'' : IsProjOver (g ≫ q) := by rw [hg2]; exact hG'proj
  obtain ⟨-, h1⟩ := GlobalTheory.T.mixed_chern_integral_point_closure_closed_subscheme K G G' q (g ≫ q) τ hGproj g rfl e (fun i => (L i).bc hp.w τ)
    (fun y => f (bcPt hp.w τ y))
  obtain ⟨-, h2⟩ := GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre k K (clos (j x)) G' (closι (j x) ≫ p) (g ≫ q) j' hp'' τ e hZ
    (fun i => (L i).pull (closι (j x)) rfl)
  have h3 := fun i => GlobalTheory.Mix.BcPull.bc_pull_isom k K (algebraMap k K) X G (clos (j x)) G' p q j hp.w (closι (j x)) j' g hg1
    hp''.w τ (L i)
  have h4 := GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver K G' (g ≫ q) τ hproj'' e _ _ h3
  conv_lhs => rw [← hgx]
  rw [h1]
  have h5 := (h2 (fun y => f (ptMap (closι (j x)) rfl _ y))).2
  change _ = Mix.int _ _
  rw [← h5]
  unfold Mix.int
  rw [h4 1, h4 (-1)]
  congr 2 <;> (funext y; exact congrArg f (Subtype.ext (by
    simp only [bcPt_val, PtsOver.map_val, ptMap, Category.assoc, hg1])))
