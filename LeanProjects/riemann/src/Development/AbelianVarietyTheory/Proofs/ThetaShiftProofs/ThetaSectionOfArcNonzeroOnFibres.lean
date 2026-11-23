import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ThetaAllFibres

theorem exists_mem_of_flat {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    (U : X.Opens) {x : X} (hx : p x = IsLocalRing.closedPoint R) (hU : x ∈ U) (g : Sp R) :
    ∃ y : X, p y = g ∧ y ∈ U := by
  have hs : g ⤳ p x := hx ▸ IsLocalRing.specializes_closedPoint (R := R) g
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap p hs
  exact ⟨y, e, hy.mem_open U.isOpen hU⟩

theorem mem_nonzeroLocus_of_h0Sec {X : Scheme.{0}} {L : LB X} {σ : Out.H0 L 1} {θ : LB.Sec L} (h : SectionOfLineBundleOne σ θ) {x : X}
    (hx : x ∈ Out.nonzeroLocus σ) : x ∈ Out.nonzeroLocus θ := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have le : LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun y hy => Set.mem_iInter.1 hy 0
  rw [h j le] at hj
  erw [Scheme.basicOpen_res] at hj
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j 0, hj.2⟩

theorem nonzeroLocus_eq_of_heq {S : Scheme.{0}} {G : Over S} [GrpObj G] {L L' : RigLB G} (e : L' = L)
    {θ : LB.Sec L.L} {θ' : LB.Sec L'.L} (h : HEq θ θ') : Out.nonzeroLocus θ = Out.nonzeroLocus θ' := by
  subst e
  rw [eq_of_heq h]

theorem X_notMem_or_eq_closedPoint {A : Type} [CommRing A] [IsLocalRing A] (hA : IsField A)
    (g : PrimeSpectrum (PowerSeries A)) :
    PowerSeries.X ∉ g.asIdeal ∨ g = IsLocalRing.closedPoint (PowerSeries A) := by
  refine or_iff_not_imp_left.2 fun h => ?_
  rw [not_not] at h
  refine PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal g.isPrime.ne_top) fun f hf => ?_)
  have h₀ : PowerSeries.constantCoeff f = 0 := by
    by_contra hne
    obtain ⟨b, hb⟩ := hA.mul_inv_cancel hne
    exact (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal f).1 hf))
      (PowerSeries.isUnit_iff_constantCoeff.2 (IsUnit.of_mul_eq_one b hb))
  obtain ⟨q, rfl⟩ := PowerSeries.X_dvd_iff.2 h₀
  exact g.asIdeal.mul_mem_right _ h

theorem theta_nonzero_on_fibres : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (θ : LB.Sec W.t.PP.L), ThNZ th → ThetaOf W th θ → (IsField A ∨ PushInvertible Y.t.G Y.t.PP.L) → ∀ g : Sp (PowerSeries A), (IsField A → PowerSeries.X ∉ g.asIdeal ∨ g = IsLocalRing.closedPoint (PowerSeries A)) ∧ ∃ x : W.t.G.left, W.t.G.hom x = g ∧ x ∈ Out.nonzeroLocus θ := by
  intro hL _ E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W th θ hth hθ _ g
  refine ⟨fun hA => X_notMem_or_eq_closedPoint hA g, ?_⟩
  obtain ⟨σ, fam, θ', hE, hp, h0, he⟩ := hθ
  have hI : Ideal.span {(PowerSeries.X : PowerSeries A)} ≤ IsLocalRing.maximalIdeal (PowerSeries A) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have := W.t.semi.geomConnected
  have := W.P.U.smooth
  obtain ⟨σ₀, -, -, -, -, hu, -, hz⟩ := GlobalTheory.ThetaUnit.exists_theta hL.globalFns hL.secBaseChange hI W.P.U (fam 0)
    ((GlobalTheory.ThetaUnit.existsUnique_pullTerm W th).2 (fam 0) hp hth _)
  obtain rfl := hu σ fam rfl hE
  obtain ⟨x, hx, hn⟩ := (hz σ 1 ((GlobalTheory.ThetaUnit.secIsMul_iff _ _ _ _).2 (one_smul _ _).symm)).2.1 isUnit_one
  rw [nonzeroLocus_eq_of_heq W.P.bundle he]
  exact exists_mem_of_flat W.t.G.hom _ hx (mem_nonzeroLocus_of_h0Sec h0 hn) g

end GlobalTheory.ThetaAllFibres
