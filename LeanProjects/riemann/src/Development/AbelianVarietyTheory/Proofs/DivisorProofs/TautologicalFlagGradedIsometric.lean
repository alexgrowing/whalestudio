import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalFlagDetIsometricStatement

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VMetric

open GlobalTheory.VB in

theorem isometric_det_tens_grLB : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (E : X.Modules) (N : ℕ)
    (h : VMetric p E N) (H : h.IsCInf) (fl : GlobalTheory.Vert.Flag E N) (i : Fin N),
    ((VMetric.det (H.restrict (fl.isSubbundle i.castSucc) (fl.isVB i.castSucc))).tens (VMetric.grLB fl i H)).Isometric
      (VMetric.det (H.restrict (fl.isSubbundle i.succ) (fl.isVB i.succ))) := by
  intro k _ X p E N h H fl i
  have hf : IsSubbundle (fl.step i) := ⟨inferInstance, 1, fl.isVB_gr i⟩
  have e := VMetric.isometric_det_tens_det k X p (VMetric.stepSeq fl i) i 1 (h.stepMet fl i)
    (H.restrict _ _) (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) hf
  refine (HermLB.Isometric.tens_right ?_ _).trans e
  refine HermLB.isometric_of_chart (fun c => c) (fun _ => le_rfl) (fun x c c' _ _ => rfl) fun σ c y hy => ?_
  change -Real.log ((((h.stepMet fl i).met σ).restrict hf (fl.isVB i.castSucc)).G c y).det.re =
    -Real.log (((h.met σ).restrict (fl.isSubbundle i.castSucc) (fl.isVB i.castSucc)).G c y).det.re
  have key : ∀ t : Γ(fl.F i.castSucc, c.U), (fl.ι i.succ).app c.U ((fl.step i).app c.U t) =
      (fl.ι i.castSucc).app c.U t := fun t => by
    rw [← fl.step_ι i]; rfl
  have eG : (((h.stepMet fl i).met σ).restrict hf (fl.isVB i.castSucc)).G c y =
      ((h.met σ).restrict (fl.isSubbundle i.castSucc) (fl.isVB i.castSucc)).G c y := by
    ext a b
    exact ((h.met σ).form_restrict (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ hy).trans
      (congrArg₂ (fun s t => (h.met σ).form s t y) (key (c.e a)) (key (c.e b)))
  rw [eG]

end GlobalTheory.VMetric

namespace GlobalTheory.FlagZ.Taut

theorem isometric_grLB_grLine : ∀ (ι : Type) [Fintype ι] (N : ℕ) (fl : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N), GlobalTheory.FlagZ.Taut.IsTaut ι N fl →
  ∀ (a : ι) (i : Fin N), (VMetric.grLB (fl a) i ((HermVB.std (𝟙 (Sp ℤ)) N).cInf.pull (GlobalTheory.FlagZ.flStr ι N) (Category.comp_id _))).Isometric (GlobalTheory.FlagZ.grLine (a, i)) := by
  intro ι _ N fl hfl a i
  have h₁ := VMetric.isometric_det_tens_grLB _ _ _ _
    ((HermVB.std (𝟙 (Sp ℤ)) N).cInf.pull (GlobalTheory.FlagZ.flStr ι N) (Category.comp_id _)) (fl a) i
  have hA := GlobalTheory.T.tautological_flag_det_isometric ι N fl hfl a i.castSucc
  have hB := GlobalTheory.T.tautological_flag_det_isometric ι N fl hfl a i.succ
  set D := GlobalTheory.FlagZ.flDet a i.castSucc
  set G := VMetric.grLB (fl a) i ((HermVB.std (𝟙 (Sp ℤ)) N).cInf.pull (GlobalTheory.FlagZ.flStr ι N) (Category.comp_id _))
  have hD : (D.tens D.dual).Isometric (HermLB.triv (GlobalTheory.FlagZ.flStr ι N)) :=
    (HermLB.isometric_tens_comm _ _).trans (HermLB.isometric_dual_tens D)
  exact (HermLB.isometric_triv_tens G).symm.trans <| (hD.symm.tens_right G).trans <|
    (HermLB.isometric_tens_assoc _ _ _).trans <| (HermLB.Isometric.refl D).tens <|
      (hA.symm.tens_right G).trans (h₁.trans hB)

end GlobalTheory.FlagZ.Taut
