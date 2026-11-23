import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetry
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InterpChgCover

theorem down_conj {F : Type} [Field F] [NumberField F] {Y : GlobalTheory.ProjVar.Var F} {V : Cover Y} {e : ℕ} {M : Man e}
    {I : ManIs M Y} {ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)} {π : ∀ σ, GlobalTheory.CxPts V.p σ → M.X (ε σ)} (hd : V.IsDown I ε π)
    {σ σ' : 𝓞 F →+* ℂ} {z : GlobalTheory.CxPts V.p σ} {z' : GlobalTheory.CxPts V.p σ'} (h : z'.1 = spMap (starRingEnd ℂ) ≫ z.1) :
    (I.pt _ (π σ' z')).1 = spMap (starRingEnd ℂ) ≫ (I.pt _ (π σ z)).1 := by
  have : Mono (spMap (algebraMap (𝓞 F) F)) := by
    have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
    infer_instance
  have : Mono V.j := (MorphismProperty.monomorphisms _).of_isPullback V.pb.flip this
  obtain ⟨w, h₁, h₂⟩ := (hd σ).2 z
  obtain ⟨w', h₁', h₂'⟩ := (hd σ').2 z'
  have h₃ : w' = spMap (starRingEnd ℂ) ≫ w := by rw [← cancel_mono V.j, h₁', Category.assoc, h₁, h]
  rw [← h₂, ← h₂', h₃, Category.assoc]

theorem lnRatio_eq_h {F : Type} [Field F] [NumberField F] {Y : GlobalTheory.ProjVar.Var F} {σ : F →+* ℂ} {Δ : Y.Dv}
    (m m' : Y.Met σ Δ) (y : Pts Y σ) {x : Y.X} (hx : under y = x) :
    lnRatio (C := cxSt F) m m' y = Real.log (m.h (eqn Δ x) y) / 2 - Real.log (m'.h (eqn Δ x) y) / 2 := by
  subst hx
  have h₁ : y ∈ GlobalTheory.ProjVar.Var.eqnSet σ Δ (eqn Δ (under y)) := Base.isEqn_eqn _ _
  exact congrArg₂ (fun a b => Real.log a / 2 - Real.log b / 2) (GlobalTheory.ProjVar.Var.pn_frame h₁) (GlobalTheory.ProjVar.Var.pn_frame h₁)

theorem chg_conj {D : D7} {O : Setup D} (hO : O.Core) (c : O.s.Comp) (R : Option ℝ) (u : D.what₂.Tau → Fin O.N → ℝ)
    {σ σ' : D.what₂.LL →+* ℂ} {p : Pts (O.var c) σ} {p' : Pts (O.var c) σ'} (e : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) :
    O.chg c R u σ' p' = O.chg c R u σ p := by
  obtain ⟨x, P, hc⟩ := hO
  have hu : under p' = under p := by
    rw [under, e]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg p.1 (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _))
  refine Finset.sum_congr rfl fun r _ => congrArg _ ?_
  have h₁ : p ∈ GlobalTheory.ProjVar.Var.eqnSet σ (divOf (O.Φ.C c) (O.ex r)) (eqn _ (under p)) := Base.isEqn_eqn _ _
  obtain ⟨k₁, k₂, -⟩ := GlobalTheory.ShFam.mets_conj _ _ _ _ _ _ _ x O.Φ c σ σ' (O.ex r) p p' _ e h₁
  rw [hc.hm_eq, hc.h0_eq]
  refine (lnRatio_eq_h _ _ p' hu).trans (Eq.trans ?_ (lnRatio_eq_h _ _ p rfl).symm)
  exact congrArg₂ (fun a b => Real.log a / 2 - Real.log b / 2) (k₁ R) k₂

theorem smooth_phR {D : D7} {O : Setup D} (hO : O.Core) {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y} (h : O.Reads A T H)
    (c : O.s.Comp) {R : ℝ} (hR : 2 ≤ R) (u : D.what₂.Tau → Fin O.N → ℝ) : (T.M c).Smooth ((T.F c).phR R u) := by
  intro a
  obtain ⟨x, P, hc⟩ := hO
  let I := h.man c
  have hm : ∀ n, (O.met.hm c (some R) (I.ε a) n).SmoothOn Set.univ := fun n => by
    rw [hc.hm_eq]
    exact (GlobalTheory.metsOf_smooth _ _ _ _ _ _ _ x O.Φ c (I.ε a) n).1 R hR
  have h0 : ∀ n, (O.met.h0 c (I.ε a) n).SmoothOn Set.univ := fun n => by
    rw [hc.h0_eq]
    exact (GlobalTheory.metsOf_smooth _ _ _ _ _ _ _ x O.Φ c (I.ε a) n).2.1
  have hg : ((O.var c).an (I.ε a)).SmoothOn Set.univ (O.chg c (some R) u (I.ε a)) := by
    intro i
    refine (ContDiffOn.sum (s := Finset.univ) fun r _ => (contDiffOn_const (c := u r.1 r.2)).mul
      (GlobalTheory.HodgeChgSmooth.smoothOn_lnRatio (hm (O.ex r)) (h0 (O.ex r)) i)).congr fun v _ => ?_
    simp [Setup.chg]
  have key := GlobalTheory.HodgeChgSmooth.smoothOn_of_manIs I (O.dim_eq c) a isOpen_univ hg
    (f := (T.F c).phR R u a) fun z _ => (h.an c).phR R hR u a z
  intro j
  simpa using key j

theorem smooth_cInf_conj : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H) (c : O.s.Comp) (R : ℝ), 2 ≤ R → ∀ (u : D.what₂.Tau → Fin O.N → ℝ) (V : Cover (O.var c)) (ε : (𝓞 D.what₂.LL →+* ℂ) → Fin ((T.M c).n + 1)) (π : ∀ σ, GlobalTheory.CxPts V.p σ → (T.M c).X (ε σ)), V.IsDown (h.man c) ε π → (T.M c).Smooth ((T.F c).phR R u) ∧ (∀ σ y, GlobalTheory.CxPts.CInfAt ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u) σ) y) ∧ ∀ σ σ', (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u) σ)).IsConj (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u) σ')) := by
  intro _ _ D O hO A T H h c R hR u V ε π hd
  have hs := smooth_phR hO h c hR u
  refine ⟨hs, GlobalTheory.Mean4O.OnModelCInf.cInfAt_pull _ _ _ _ _ (h.man c) ε π hd _
    fun σ j => (hs σ j).const_smul (2 : ℝ), fun σ σ' _ y y' e _ => ?_⟩
  change (2 : ℝ) * (T.F c).phR R u (ε σ') (π σ' y') = (2 : ℝ) * (T.F c).phR R u (ε σ) (π σ y)
  exact congrArg _ (((h.an c).phR R hR u _ _).trans
    ((chg_conj hO c _ u (down_conj hd e)).trans ((h.an c).phR R hR u _ _).symm))

end GlobalTheory.InterpChgCover

end
