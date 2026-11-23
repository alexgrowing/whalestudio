import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmoothHermitianMetricProjectiveVariety
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernDegreePoint
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.PointChern

theorem chernTop_eq_eval {ι : Type} {m : ι → ℕ} {n : ℕ} (hn : n = 0) (R : MvPolynomial (ι × ℕ) ℝ)
    (G : V n → GlobalTheory.FlagBundle.Mat m ℂ) (v : V n) :
    chernTop R G v = MvPolynomial.eval (fun x : ι × ℕ => if x.2 = 0 then (1 : ℝ) else 0) R := by
  subst hn
  have hc (x : ι × ℕ) : chernPoly (fun u => G u x.1) v x.2 =
      algebraMap ℝ (MvPolynomial (Fin 0 × Fin 0) ℂ) (if x.2 = 0 then 1 else 0) := by
    have e : curvPoly (fun u => G u x.1) v = 0 := by
      ext i j; simp [curvPoly]
    rw [chernPoly, e, neg_zero]
    by_cases h : x.2 = 0 <;> simp [Matrix.charpolyRev, Polynomial.coeff_one, h]
  have ha : (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) =
      algebraMap ℝ (MvPolynomial (Fin 0 × Fin 0) ℂ) ∘ (fun x : ι × ℕ => if x.2 = 0 then (1 : ℝ) else 0) :=
    funext hc
  rw [chernTop, ha, MvPolynomial.aeval_algebraMap_apply]
  simp [topCoeff]

theorem chernIntegral_point : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (X : GlobalTheory.ProjVar.Var ℚ)
    (E : GlobalTheory.FlagBundle.Fr (GlobalTheory.FlagBundle.ratOf X) m 0), X.dim = 0 →
    ∃ (σ : ℚ →+* ℂ) (H : GlobalTheory.FlagBundle.Mat m X.Fn → CxPts X.str σ → GlobalTheory.FlagBundle.Mat m ℂ),
      GlobalTheory.GoodMetric.IsMetricOn E ⊤ H ∧ GlobalTheory.GoodMetric.IsGood E ⊤ H ∧
      ∀ (R : MvPolynomial (ι × ℕ) ℝ) (t : ℝ), GlobalTheory.GoodMetric.HasChernIntegral E ⊤ H R t →
        t = MvPolynomial.eval (fun x : ι × ℕ => if x.2 = 0 then (1 : ℝ) else 0) R := by
  intro ι _ m X E hX
  obtain ⟨H, hH⟩ := SmoothMetric.exists_isMetricOn_top ℚ (Rat.castHom ℂ) X ι m E
  refine ⟨Rat.castHom ℂ, H, hH, fun y hy => absurd mem_ptsIn_top hy, fun R t ht => ?_⟩
  obtain ⟨⟨y⟩, hsub⟩ := GlobalTheory.Published.ArDegreeModel.unique_pt X (Rat.castHom ℂ) hX
  have := X.smooth_str
  have := CxPts.secondCountableTopology_of_isProjOver (Rat.castHom ℂ) X.isProjOver
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := X.str) (σ := Rat.castHom ℂ) (D := X.dim) y
  have hV : Subsingleton (V X.dim) := by rw [hX]; infer_instance
  have hvol : (volume : Measure (V X.dim)) Set.univ = 1 := by
    have := (stdOrthonormalBasis ℝ (V X.dim)).volume_parallelepiped
    rwa [Set.eq_univ_of_forall (s := parallelepiped _) fun v =>
      (mem_parallelepiped_iff _ _).2 ⟨0, ⟨le_rfl, zero_le_one⟩, Subsingleton.elim _ _⟩] at this
  have hdet (i j : AlgChart X.str (Rat.castHom ℂ) X.dim) (z : CxPts X.str (Rat.castHom ℂ)) :
      transDet i.e j.e z = 1 := by
    rw [transDet, ContinuousLinearMap.det]
    exact LinearMap.det_eq_one_of_finrank_eq_zero (Module.finrank_zero_of_subsingleton (R := ℂ) (M := V X.dim)) _
  set r := MvPolynomial.eval (fun x : ι × ℕ => if x.2 = 0 then (1 : ℝ) else 0) R
  have hA : MeasurableSet (ptsIn X.str (Rat.castHom ℂ) ⊤) := (isOpen_ptsIn _).measurableSet
  have hAs : ptsIn X.str (Rat.castHom ℂ) ⊤ ⊆ c.e.source := fun z _ => Subsingleton.elim y z ▸ hc
  have hm (ε : ℤˣ) : chernTopPart E H R ε (ptsIn X.str (Rat.castHom ℂ) ⊤) = ENNReal.ofReal ((ε : ℤ) * r) := by
    rw [chernTopPart, glueMeas_apply _ _ (fun i j => i.holo_trans j) ?_ c hA hAs,
      chartMeas_apply_of_subset _ _ hA hAs]
    · simp only [chernTop_eq_eval hX]
      rw [show c.e '' ptsIn X.str (Rat.castHom ℂ) ⊤ = Set.univ from
        Set.eq_univ_of_forall fun v => ⟨y, mem_ptsIn_top, Subsingleton.elim _ _⟩]
      simp [hvol, r]
    · intro i j z _ _
      simp [hdet, chernTop_eq_eval hX]
  obtain ⟨-, h2⟩ := ht
  rw [← h2, Measure.real, Measure.real, hm, hm, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  push_cast
  rcases le_total 0 r with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring

end GlobalTheory.GoodMetric.PointChern
