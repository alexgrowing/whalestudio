import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingThick
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcRigidityTwoModelsOfMono

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ

theorem exists_generic_lift {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {k : Type} [Field k] (bF : c.F →+* k) {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) (χ : Sp (PowerSeries k) ⟶ Y.X)
    (hχ : χ ≫ Y.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β))
    {S : Type} [CommRing S] [Nontrivial S] (ι : PowerSeries k →+* S) (hι : IsUnit (ι PowerSeries.X))
    (z : Sp S ⟶ Xo.XF c) (hz : z ≫ Y.j = spMap ι ≫ χ) :
    ∃ y : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c, y ≫ Y.j = Out.jK (PowerSeries k) ≫ χ ∧
      y ≫ pullback.snd _ _ = Out.jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF := by
  have := Y.jQ_open
  have w : (Out.jK (PowerSeries k) ≫ χ) ≫ Y.s =
      (Out.jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF) ≫ spMap β := by
    rw [Category.assoc, hχ, spMap_comp]; simp only [Category.assoc]
  obtain ⟨q⟩ : Nonempty (Sp S) := (inferInstance : Nonempty (PrimeSpectrum S))
  have hq : PowerSeries.X ∉ (spMap ι q).asIdeal := fun h =>
    q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ι PowerSeries.X ∈ q.asIdeal from h) hι)
  obtain ⟨p₀, hp₀⟩ := mem_range_jK _ hq
  have hr : Set.range (pullback.lift _ _ w) ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = p₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing (PowerSeries k))) _ _
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hp₀,
      ← Scheme.Hom.comp_apply, ← hz, Scheme.Hom.comp_apply]
    exact GlobalTheory.ThetaShiftProofs.j_mem_abLocus Y _
  have hy := IsOpenImmersion.lift_fac Y.jQ _ hr
  refine ⟨IsOpenImmersion.lift Y.jQ _ hr, ?_, ?_⟩
  · unfold Model.j
    rw [← Category.assoc, hy, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, hy, pullback.lift_snd]

theorem isArcFr_eq_of_overBase : Out.Laws → Out.Laws2 → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn Dw l (RingHom.id c.F) k bF) (V V' : ValuationSubring ℂ) (Y : Model Xo c (c.V V).subtype) (Y' : Model Xo c (c.V V').subtype) (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : Wit Y (a.restrict (c.V V).subtype) χ) (W' : Wit Y' (a.restrict (c.V V').subtype) χ'), χ ≫ Y.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V).subtype) → χ' ≫ Y'.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V').subtype) → ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR k)) (th : a.D₀.P.L.Sec), ThNZ th → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Nontrivial S] (ι : PowerSeries k →+* S) (y y' : FrPt Xo c S), IsUnit (ι PowerSeries.X) → IsArcFr W e th ι y → IsArcFr W' e th ι y' → y = y' := by
  intro h1 h2 h5 E _ _ _ H Dw l Xo c k _ bF a V V' Y Y' χ χ' W W' hχ hχ' e th hth S _ _ _ ι y y' hι hy hy'
  have hj : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  have hj' : Mono Y'.j := GlobalTheory.ThetaShiftProofs.mono_j Y' (mono_spMap_subtype _)
  obtain ⟨y₀, a₁, a₂⟩ := exists_generic_lift bF Y χ hχ ι hι hy.choose
    hy.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  obtain ⟨y₀', b₁, b₂⟩ := exists_generic_lift bF Y' χ' hχ' ι hι hy'.choose
    hy'.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  obtain ⟨rfl, hψ⟩ := GlobalTheory.arc_rigidity_two_models_of_mono h1 h2 h5 E H Dw l Xo c k bF a _ _ _ _ Y Y' χ χ' W W' y₀ y₀' a₁ b₁ a₂ b₂
  obtain ⟨ψ, hψ⟩ := hψ hj
  have hy₁ := GlobalTheory.ArcQ.isArcFr_of_agree h1 h2 E H Dw l Xo c k bF a _ _ _ _ Y Y' χ χ' W W' ψ hψ y₀ a₁ b₁ hj e th hth S ι y hι hy
  exact (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ Y' k _ _ χ' W' e th hth S ι y' hy').1 hj' y hy₁

end GlobalTheory.ArcQ
