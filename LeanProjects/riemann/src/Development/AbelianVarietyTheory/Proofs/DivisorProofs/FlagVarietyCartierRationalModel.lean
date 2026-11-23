import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietySmoothOverRatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyGeometricallyConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPullbackLocalFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagParahoricRelativeCriterionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectivePointFlagHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFrameParahoricAtPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagHomKeepsRadicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFrameBundleHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricFromFlagFrames

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

theorem GlobalTheory.FlagQ.genericFibre_flagBundle : ∀ (ι : Type) [Fintype ι] (N : ℕ), ∃ (Y : GlobalTheory.ProjVar.Var ℚ) (j : Y.X ⟶ GlobalTheory.FlagZ.Fl ι N) (gr : ι × Fin N → Y.Dv), IsPullback j Y.str (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ)) ∧ Y.dim = dimFl ι N ∧ (∀ x, ∃ r, GlobalTheory.Cartier.Presents (gr x) ((GlobalTheory.FlagZ.grLine x).B.pull j) r) ∧ ∃ (X : GlobalTheory.ProjVar.Var ℚ) (E : GlobalTheory.FlagBundle.Fr (GlobalTheory.FlagBundle.ratOf X) (fun _ : ι => N) 0) (E' : GlobalTheory.FlagBundle.Fr (GlobalTheory.FlagBundle.ratOf Y) (fun _ : ι => N) (fun _ : ι => N)) (φ : X.Fn →ₐ[ℚ] Y.Fn) (f : Y.X ⟶ X.X), X.dim = 0 ∧ GlobalTheory.FlagBundle.Refines E E' φ f ∧ GlobalTheory.GoodMetric.IsGraded E' (fun x => gr (x.1, x.2)) := by
  intro ι _ N
  have := GlobalTheory.T.flag_variety_smooth_over_rat ι N
  have := GlobalTheory.T.flag_variety_geometrically_connected ι N
  obtain ⟨Y, e, hd, he⟩ := GlobalTheory.ProjVar.Var.exists_iso (pullback.snd (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ)))
    (dimFl ι N) (GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap ℤ ℚ) (GlobalTheory.FlagZ.isProjOver_str _ _))
  have hj : IsPullback (e.inv ≫ pullback.fst _ _) Y.str (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ)) :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, ← he, Category.assoc, e.inv_hom_id_assoc]⟩ e.symm rfl
      (by rw [Iso.symm_hom, ← he, e.inv_hom_id_assoc])
  let E' : GlobalTheory.FlagBundle.Fr (GlobalTheory.FlagBundle.ratOf Y) (fun _ : ι => N) (fun _ => N) :=
    { S := fun y => {A | GlobalTheory.FlagQ.IsFrame (e.inv ≫ pullback.fst _ _) y A}
      loc := fun y => by
        obtain ⟨U, A, hy, hA⟩ := GlobalTheory.T.flag_pullback_local_frames ι N Y _ hj y
        exact ⟨U, A, hy, fun τ => (hA y hy).1.det_ne τ,
          fun z hz A' => GlobalTheory.T.flag_parahoric_relative_criterion _ A _ A' (hA z hz).1 (hA z hz).2⟩ }
  obtain ⟨gr, hP, hG⟩ := GlobalTheory.T.graded_metric_from_flag_frames ι N Y _ hj E' fun _ _ => Iff.rfl
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.projective_point_flag_hom Y
  exact ⟨Y, _, gr, hj, hd, hP, GlobalTheory.ProjVar.proj ℚ 0, GlobalTheory.FlagQ.triv ι N, E', φ, GlobalTheory.FlagQ.toPt Y, rfl,
    ⟨fun _ => Nat.zero_le _, hφ, fun z A' hA' A hA => GlobalTheory.T.flag_frame_parahoric_at_points ι N Y _ φ hφ z A' hA' A hA, GlobalTheory.T.flag_hom_keeps_radical Y φ hφ,
      GlobalTheory.T.flag_frame_bundle_hom ι N Y _ hj E' (fun _ _ => Iff.rfl) φ hφ⟩, hG⟩
