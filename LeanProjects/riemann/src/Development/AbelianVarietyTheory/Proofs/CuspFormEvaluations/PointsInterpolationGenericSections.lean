import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem addL_zero_pts {D : D7} {j : ℕ} (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  show wadd u (wsmul 0 wL) = u
  cases u
  simp [wadd, wsmul]

theorem rdg_s_apply {D : D7} {T : Top D} {h : LawsP T} {j : ℕ} {hj : InR D j} {n : SecNorm (recB h.toLawsCore)}
    {R : Rdg (recPlusN h j hj n)} {e : R.Y ≃ DomPt T j} (hR : IsRdgU h j hj n R e) {N : ℕ} {wL : WeightFamilies.Wt D j}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (t : Idx D j N → ℂ) (i : Fin (WeightFamilies.dimY D j + 1)) (y : R.Y) :
    R.s w t i y = ∑ k, t (i, k) * rdR h j (w k) (e y).1 (e y).2.1 := by
  simp only [Rdg.s, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]

theorem mem_sp_of_rdOnto {D : D7} {T : Top D} {h : LawsP T} {j : ℕ} {hj : InR D j} {n : SecNorm (recB h.toLawsCore)}
    {R : Rdg (recPlusN h j hj n)} {e : R.Y ≃ DomPt T j} (hR : IsRdgU h j hj n R e) {u : WeightFamilies.Wt D j}
    (hO : RdOnto h j u) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)
    (hf : ∀ k, f k ∈ ((T.U j T.σ₀).X k).SS (laR T j u k)) :
    (fun y => f (e y).1 (e y).2.1) ∈ R.sp u Set.univ := by
  obtain ⟨m, a, F, -, hF⟩ := hO f hf
  have hfun : (fun y => f (e y).1 (e y).2.1) = ∑ i, a i • R.ev ((recPlusN h j hj n).inc u (F i)) := by
    funext y
    rw [hF _ _ (e y).2.2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, Set.mem_univ _, rfl⟩)

theorem points_and_interp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → (∀ q, R.s w t 0 (xs q) ≠ 0 ∧ ∀ i : Fin (WeightFamilies.dimY D j), R.s w t i.succ (xs q) = 0) ∧ ∀ v : Fin δ → ℂ, ∃ f ∈ R.sp wF Set.univ, ∀ q, f (xs q) = v q := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hxs hO

  have hvan : ∀ (k : (T.U j T.σ₀).Comp) (a : Fin (nd ((T.U j T.σ₀).X k))) (p : Fin (Fl.Fl k).δ),
      (Fl.Fl k).s a ((Fl.Fl k).xs p) = 0 := by
    intro k a p
    have hb : (fun _ => (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) ∈
        Bor ((T.U j T.σ₀).X k).Ψ D.R.r := by
      intro τ
      refine ⟨?_, fun a c hca => Matrix.one_apply_ne hca.ne'⟩
      show (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ).det ≠ 0
      simp
    have hself : (Fl.Fl k).xs p = lact 1 (rmul ((Fl.Fl k).xs p)
        (fun _ => (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ))) := by
      funext τ a c
      simp only [lact, rmul, mat, Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), one_mul]
      have hm : (Matrix.of ((Fl.Fl k).xs p τ) : Matrix (Fin D.R.r) (Fin D.R.r) ℂ) * 1 =
          Matrix.of ((Fl.Fl k).xs p τ) := Matrix.mul_one _
      exact (congrFun (congrFun hm a) c).symm
    exact (((Fl.Fl k).S_eq _ ((Fl.Fl k).xs_mem p)).2
      ⟨p, 1, ((T.U j T.σ₀).X k).Γ.one_mem, _, hb, hself⟩) a
  refine ⟨fun q => ⟨?_, fun i => ?_⟩, fun v => ?_⟩
  · rw [rdg_s_apply hR, hxs q]
    dsimp only
    rw [← Fl.h0]
    exact (Fl.Fl _).w0_ne _
  · rw [rdg_s_apply hR, hxs q]
    dsimp only
    have hs := Fl.hs (en q).1 (Fin.cast (A.dim (en q).1).symm i) ((Fl.Fl (en q).1).xs (en q).2)
    have hi : Fin.cast (A.dim (en q).1) (Fin.cast (A.dim (en q).1).symm i) = i := Fin.ext rfl
    rw [hi] at hs
    rw [← hs]
    exact hvan _ _ _
  ·
    have hF : ∀ k : (T.U j T.σ₀).Comp, ∃ F ∈ ((T.U j T.σ₀).X k).SSgt (A.Xa k).Fp 0,
        ∀ p, F ((Fl.Fl k).xs p) = v (en.symm ⟨k, p⟩) := by
      intro k
      obtain ⟨bb, m, h1, h2, h3⟩ := (A.mar k).1
      exact interpStatement_holds _ _ (A.Xa k) (Fl.Fl k)
        (GlobalTheory.ClosedDiscontinuity.propDisc_closed _ _)
        ⟨bb, m, h1, h2, fun x0 hx0 z hz ξ => by simpa using h3 0 (Set.mem_insert _ _) x0 hx0 z hz ξ⟩
        (A.mar k).2.2.1 (fun P hP => by simpa using (A.mar k).2.2.2.2 0 P (by simpa using hP)) _
    choose F hFmem hFval using hF
    have hO0 : RdOnto h j wF := by
      have h0 := hO 0
      rwa [addL_zero_pts] at h0
    have hf : ∀ k, F k ∈ ((T.U j T.σ₀).X k).SS (laR T j wF k) := by
      intro k
      rw [← A.hF k]
      exact (hFmem k).1
    refine ⟨_, mem_sp_of_rdOnto hR hO0 F hf, fun q => ?_⟩
    show F (e (xs q)).1 (e (xs q)).2.1 = v q
    rw [hxs q]
    exact (hFval _ _).trans (by simp)

end GlobalTheory.Shares
