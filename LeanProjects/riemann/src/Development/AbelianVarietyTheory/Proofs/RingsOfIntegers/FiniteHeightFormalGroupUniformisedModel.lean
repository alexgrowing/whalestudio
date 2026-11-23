import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalGroupLawChartFiniteHeightSpecialFibre
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsReindexFin
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsLawOfOfMatch

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceFinHt

theorem oact_natCast {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (n : ℕ) : act.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h := act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact mul_left_cancel (a := act.act 0) (by rw [← h, _root_.mul_one])
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]

theorem exists_pow_le_of_isMapOf (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G]
    [IsCommMonObj G] (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T))))
    (U : Out.UnifPre (maximalIdeal T) D A G) (d : ℕ) (x0 : GlobalTheory.JetSer.Fam G (Fin d)) (hu : Chart.IsUnivChart G d x0)
    (N : ℕ) (hN : 1 ≤ N) (φ : Pt T 1 d) (hmap : GlobalTheory.JetSer.IsMapOf x0 x0 (𝟙 G ^ N) φ) :
    ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS (ResidueField T) 1 d)) ^ M ≤
      Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (φ j)) := by
  have hp := isGrpPullback_pullback G (Spec.map (CommRingCat.ofHom (residue T)))
  obtain ⟨x', hu', -, hm, -⟩ := GlobalTheory.ChartBaseChange.chartBaseChange GlobalTheory.JetSer.jetAlg
    (GlobalTheory.JetSer.serSt_of_jetAlgSt GlobalTheory.JetSer.jetAlg) T (ResidueField T) (residue T) G _ _ hp d x0 hu
  have hm' := hm _ _ _ (GlobalTheory.FiniteHeight.id_pow_left_proj hp N) hmap
  have hsm := U.smooth
  have : LocallyOfFiniteType ((Over.pullback (Spec.map (CommRingCat.ofHom (residue T)))).obj G).hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hp.1 inferInstance
  obtain ⟨M, hM⟩ := GlobalTheory.JetSer.exists_pow_le_span_sup_pow_succ (ResidueField T) _ _ (by
      rw [MonObj.comp_pow, Category.comp_id]
      have : η[(Over.pullback (Spec.map (CommRingCat.ofHom (residue T)))).obj G] = 1 := by
        rw [Hom.one_def, toUnit_unit, Category.id_comp]
      rw [this, one_pow]) (fun Ω _ _ t => by
      obtain ⟨b, rfl⟩ := Spec.map_surjective t
      refine GlobalTheory.FiniteHeight.finite_torsion_pull hp _ (Geo.Tor.spMap (b.hom.comp (residue T))) ?_ N
        (GlobalTheory.finite_torsion_special_fibre_of_unif T G D A U Ω _ (fun a ha => ?_) N hN)
      · rw [← Spec.map_comp]
        rfl
      · rw [RingHom.comp_apply, (residue_eq_zero_iff a).2 ha, map_zero]) d x' hu' _ hm'
  exact ⟨M, (GlobalTheory.pow_span_X_le_and_finite_quotient_of_le_sup_pow_succ _ _ _ M hM).1⟩

theorem finHt_of_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → FinHt B := by
  intro E _ _ _ H Dw l Xo c inst hstar
  obtain rfl := GlobalTheory.PowGerm.starSt E H inst hstar
  letI := H.starRing
  intro T io y C hC B hB N hN
  obtain ⟨-, P, -⟩ := hC
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hB
  obtain ⟨x, hx, hm⟩ := GlobalTheory.PowGerm.univConv T.V C.I.G.G _ C.xT
    (GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C) _ (GlobalTheory.PowGerm.oneCol _)
  have hc := C.chartT
  have hf := C.frameT
  rw [← h1, ← h2] at hc
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6] at hf
  have hl := (GlobalTheory.LinkLaw.linkLaw E H T.V C.I.G _ B C.tgT C.xT C.eT C.wPT hc hf C.primT x hx hm).2 (N : 𝓞 E)
  rw [oact_natCast] at hl
  exact exists_pow_le_of_isMapOf T.V C.I.G.G P.D P.A P.U.toUnifPre _ x hx N hN _ hl

end GlobalTheory.PlaceFinHt
