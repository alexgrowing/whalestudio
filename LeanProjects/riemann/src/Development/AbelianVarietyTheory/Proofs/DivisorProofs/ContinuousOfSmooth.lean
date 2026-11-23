import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

namespace GlobalTheory.HomChgConj

section Atlas

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem continuous_of_smooth {f : X → ℝ} (h : A.Smooth f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨j, hj⟩ := A.cover x
  have h1 := (h j).continuousOn
  rw [Set.preimage_univ, Set.inter_univ] at h1
  have h2 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    h1.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))
  refine (h2.comp ((A.chart j).continuousAt hj)).congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem dense_compl_bd {Z : Set X} {r : X → ℝ} {Om : LocPot X} (h : IsBd A Z r Om) : Dense Zᶜ := by
  refine interior_eq_empty_iff_dense_compl.1 (Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_)
  obtain ⟨j, hj⟩ := A.cover x
  have ho := (A.chart j).isOpen_inter_preimage_symm (isOpen_interior (s := Z))
  have hp := ho.measure_pos MeasureTheory.volume
    ⟨A.chart j x, (A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  exact hp.ne' (MeasureTheory.measure_mono_null
    (Set.inter_subset_inter_right _ (Set.preimage_mono interior_subset)) (h.2.1 j))

end Atlas

theorem down_conj {F : Type} [Field F] [NumberField F] {Y : Var F} {V : Cover Y} {e : ℕ} {M : Man e} {I : ManIs M Y}
    {ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)} {π : ∀ σ, CxPts V.p σ → M.X (ε σ)}
    (hd : V.IsDown I ε π) {σ σ' : 𝓞 F →+* ℂ} {z : CxPts V.p σ} {z' : CxPts V.p σ'}
    (h : z'.1 = spMap (starRingEnd ℂ) ≫ z.1) :
    (I.pt _ (π σ' z')).1 = spMap (starRingEnd ℂ) ≫ (I.pt _ (π σ z)).1 := by
  have h0 : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  have : IsPreimmersion V.j := MorphismProperty.of_isPullback V.pb.flip h0
  obtain ⟨w, h₁, h₂⟩ := (hd σ).2 z
  obtain ⟨w', h₁', h₂'⟩ := (hd σ').2 z'
  have h₃ : w' = spMap (starRingEnd ℂ) ≫ w := by rw [← cancel_mono V.j, h₁', Category.assoc, h₁, h]
  rw [← h₂, ← h₂', h₃, Category.assoc]

theorem chg_conj {D : D7} {O : Setup D} (h : O.Core) (c : O.s.Comp) (R : Option ℝ) (u : D.what₂.Tau → Fin O.N → ℝ)
    {σ σ' : D.what₂.LL →+* ℂ} {y : Pts (O.var c) σ} {y' : Pts (O.var c) σ'} (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    O.chg c R u σ' y' = O.chg c R u σ y := by
  obtain ⟨x, P, h⟩ := h
  have hu : under y' = under y := ConjMet.base_conj (Y := O.Φ.C c) e
  refine Finset.sum_congr rfl fun z _ => congrArg _ ?_
  have h₁ : y ∈ Var.eqnSet σ (divOf (O.Φ.C c) (O.ex z)) (eqn (divOf (O.Φ.C c) (O.ex z)) (under y)) :=
    Base.isEqn_eqn _ _
  have h₂ : y' ∈ Var.eqnSet σ' (divOf (O.Φ.C c) (O.ex z)) (eqn (divOf (O.Φ.C c) (O.ex z)) (under y')) :=
    Base.isEqn_eqn _ _
  obtain ⟨a, b, -⟩ := mets_conj D _ _ _ _ _ O.s x O.Φ c σ σ' _ y y' _ e h₁
  have k : ∀ (m : Var.Met (O.var c) σ (divOf (O.Φ.C c) (O.ex z))) (m' : Var.Met (O.var c) σ' (divOf (O.Φ.C c) (O.ex z))),
      m'.h (eqn (divOf (O.Φ.C c) (O.ex z)) (under y)) y' = m.h (eqn (divOf (O.Φ.C c) (O.ex z)) (under y)) y →
      lnN (C := cxSt _) m' (genAt _ (under y')) y' = lnN (C := cxSt _) m (genAt _ (under y)) y := fun m m' hm => by
    refine congrArg (Real.log · / 2) ((Var.pn_frame h₂).trans (Eq.trans ?_ (Var.pn_frame h₁).symm))
    rw [hu, hm]
  rw [lnRatio, lnRatio, h.hm_eq, h.h0_eq]
  exact congrArg₂ (· - ·) (k _ _ (a R)) (k _ _ b)

theorem ext_conj {D : D7} {O : Setup D} (hO : O.Core) {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y} (h : O.Reads A T H)
    (c : O.s.Comp) (u : D.what₂.Tau → Fin O.N → ℝ) {g : (T.M c).Fun} (hg : (T.M c).Smooth g)
    (he : ∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph u σ x) {a a' : Fin ((T.M c).n + 1)}
    {x : (T.M c).X a} {x' : (T.M c).X a'}
    (e : ((h.man c).pt a' x').1 = spMap (starRingEnd ℂ) ≫ ((h.man c).pt a x).1) : g a' x' = g a x := by
  let I := h.man c
  have hσ : I.ε a' = (starRingEnd ℂ).comp (I.ε a) := ConjMet.emb_conj (Y := O.Φ.C c) e
  let j : (T.M c).X a → (T.M c).X a' := fun z => (I.pt a').symm (ConjChart.conjPts (O.var c).str hσ (I.pt a z))
  have hj : Continuous j := (I.pt a').symm.continuous.comp
    ((ConjChart.conjPts (O.var c).str hσ).continuous.comp (I.pt a).continuous)
  have hj' : ∀ z, (I.pt a' (j z)).1 = spMap (starRingEnd ℂ) ≫ (I.pt a z).1 := fun z => by
    simp only [j, Homeomorph.apply_symm_apply]
    rfl
  have key : g a' ∘ j = g a := by
    refine Continuous.ext_on (dense_compl_bd ((T.M c).bd a)) ((continuous_of_smooth (hg a')).comp hj)
      (continuous_of_smooth (hg a)) fun z hz => ?_
    have hu : under (I.pt a' (j z)) = under (I.pt a z) := ConjMet.base_conj (Y := O.Φ.C c) (hj' z)
    have hz' : j z ∉ (T.M c).Z a' := fun h' => hz (((h.an c).Z a z).2 (hu ▸ ((h.an c).Z a' _).1 h'))
    change g a' (j z) = g a z
    rw [he _ _ hz', he _ _ hz, (h.an c).ph u _ _ hz', (h.an c).ph u _ _ hz]
    exact chg_conj hO c none u (hj' z)
  obtain rfl : x' = j x := (I.pt a').injective (Subtype.ext (e.trans (hj' x).symm))
  exact congrFun key x

theorem isConj_pull : ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H) (c : O.s.Comp)
    (u : D.what₂.Tau → Fin O.N → ℝ) (g : (T.M c).Fun), (T.M c).Smooth g →
    (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph u σ x) → ∀ (V : Cover (O.var c))
    (ε : (𝓞 D.what₂.LL →+* ℂ) → Fin ((T.M c).n + 1)) (π : ∀ σ, GlobalTheory.CxPts V.p σ → (T.M c).X (ε σ)),
    V.IsDown (h.man c) ε π → ∀ t : ℝ, ∀ σ σ',
      (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => t : (T.M c).Fun))) σ)).IsConj
        (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => t : (T.M c).Fun))) σ')) := by
  intro D O hO A T H h c u g hg he V ε π hd t σ σ' _ y y' e _
  have := ext_conj hO h c u hg he (down_conj hd e)
  change (2 : ℝ) * (g _ _ - t) = 2 * (g _ _ - t)
  rw [this]

end GlobalTheory.HomChgConj
