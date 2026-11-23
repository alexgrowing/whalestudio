import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.VMetric

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E E' : X.Modules} {r : ℕ}
  {h : VMetric p E r} {h' : VMetric p E' r} {φ : E ≅ E'}

theorem stepMet_ofIso (hφ : h.IsIsometry h' φ) (fl : Vert.Flag E r) (i : Fin r) :
    h'.stepMet (fl.ofIso φ) i = h.stepMet fl i := by
  refine VMetric.ext (funext fun σ => Met.ext_form fun V s t y hy => ?_)
  exact (Met.form_restrict (h'.met σ) ((fl.ofIso φ).isSubbundle i.succ) ((fl.ofIso φ).isVB i.succ)
    s t hy).trans ((hφ σ V _ _ y hy).trans
      (Met.form_restrict (h.met σ) (fl.isSubbundle i.succ) (fl.isVB i.succ) s t hy).symm)

theorem flagBc_ofIso (hφ : h.IsIsometry h' φ) (fl : Vert.Flag E r) :
    h'.flagBc (fl.ofIso φ) = h.flagBc fl :=
  Finset.sum_congr rfl fun i _ => congrArg (fun g : VMetric p (stepSeq fl i).X₂ (i + 1) =>
    g.bcInt (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)) (stepMet_ofIso hφ fl i)

theorem flagBcFinite_ofIso (hφ : h.IsIsometry h' φ) (fl : Vert.Flag E r) :
    h'.FlagBcFinite (fl.ofIso φ) ↔ h.FlagBcFinite fl :=
  forall_congr' fun i => iff_of_eq (congrArg (fun g : VMetric p (stepSeq fl i).X₂ (i + 1) =>
    g.BcFinite (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)) (stepMet_ofIso hφ fl i))

theorem grLB_ofIso (hφ : h.IsIsometry h' φ) (H : h.IsCInf) (H' : h'.IsCInf) (fl : Vert.Flag E r)
    (i : Fin r) : grLB (fl.ofIso φ) i H' = grLB fl i H := by
  have e : h'.grMet (fl.ofIso φ) i = h.grMet fl i :=
    congrArg (fun g : VMetric p (stepSeq fl i).X₂ (i + 1) =>
      g.quot (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)) (stepMet_ofIso hφ fl i)
  change det (H'.grMet (fl.ofIso φ) i) = det (H.grMet fl i)
  generalize H'.grMet (fl.ofIso φ) i = A
  generalize H.grMet fl i = B
  revert A B
  rw [e]
  intro A B
  rfl

end GlobalTheory.VMetric

theorem GlobalTheory.VMetric.isFlagCh2_ofIso : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (E E' : X.Modules) (r : ℕ) (h : VMetric p E r) (h' : VMetric p E' r)
    (φ : E ≅ E') (H : h.IsCInf) (H' : h'.IsCInf) (fl : Vert.Flag E r) (a : ℝ),
    h.IsIsometry h' φ → (VMetric.IsFlagCh2 H fl a ↔ VMetric.IsFlagCh2 H' (fl.ofIso φ) a) := by
  intro k _ X p _ E E' r h h' φ H H' fl a hφ
  unfold IsFlagCh2
  rw [flagBcFinite_ofIso hφ, flagBc_ofIso hφ]
  simp only [grLB_ofIso hφ H H']
