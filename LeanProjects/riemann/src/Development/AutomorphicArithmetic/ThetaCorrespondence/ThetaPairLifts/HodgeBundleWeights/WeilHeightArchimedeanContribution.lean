import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.WeilBound.CoreStatements.NefModelVolumes.NormGenValLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LocalUnitMapSurjective

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PositivityTheory.Xj7N
open GlobalTheory GlobalTheory.CompHS GlobalTheory.Adelic
section Generic
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
end Generic
section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
end Main
theorem weil_height_archimedean_contribution : NV → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → ∀ (N m : ℕ) (b : Module.Basis (Fin N) Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (g : Matrix (Fin N) (Fin m) Y.d.c₂.F) (A : (Y.d.c₂.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) b g A → ∀ (σ : Y.d.c₂.F →+* ℂ) (ρ : Om Z →+* ℂ), ρ.comp (algebraMap Y.d.c₂.F (Om Z)) = σ → ∀ τ : ℕ, 0 < τ → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) τ t, ‖ρ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂))‖ ≤ Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ) (fun i => ρ (genVal Z ((b i : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂))) ^ τ := by
  intro hNV hP D T j Y e o hY hf Z u t hG hB _ _ N m b g A hF σ ρ hρ τ _ f hfs
  have hd : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ g, (Y.dict σ g).2 ∈ ((Y.U σ).X (Y.dict σ g).1).dom := fun σ hσ => by
    obtain ⟨th, hr, hth, hdU⟩ := hY.dictU σ hσ
    exact hdU.2.2.2.1
  have hD : 1 ≤ GlobalTheory.FlagTan.dimFlag (T.Q.Dw j) := by
    have h2 : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q :=
      (hY.unf _ (goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom)).1
    have hm := D.R.two_le_m
    have hk := D.R.m_add_three_le_k
    have h3 : 2 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
      rw [← h2]; unfold Formalism.BasicNotions.Ranks.r; omega
    exact Nat.mul_pos (by omega) (Nat.choose_pos h3)
  obtain ⟨TF⟩ := DifferentiableLines.nonempty_toroidal_flag_bundle hP.p1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.CompHS.TorFlagEx.one_le_of_dimFlag hD)
  have hspan : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ P ∈ holSub (Y.U σ).X (modelWt (Y.U σ) (wtOf (T.Q.Dw j) u 0)),
      ∃ Q ∈ Submodule.span ℂ (rdU (Y.U σ) '' (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0) : Set (Rul Y.d.Xo₂ Y.d.c₂))),
        ∀ w ∈ framesOn (Y.U σ) Z, P w.1 w.2 = Q w.1 w.2 := fun σ hσ P hPh => by
    obtain ⟨m', as, fs, hfs', hPQ⟩ := _root_.PositivityTheory.Xj7N.local_unit_map_surjective hNV hP D T j Y e o hY hf Z TF u hG hB σ hσ P hPh
    choose g' hg hgf using fun i => GlobalTheory.T.extVan_section_has_cusp_form_match D T j Y e o hY hf Z TF u (fs i) (hfs' i)
    refine ⟨∑ i, as i • rdU (Y.U σ) (g' i), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨g' i, hg i, rfl⟩), fun w hw => ?_⟩
    rw [hPQ w hw]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hgf i σ hσ w hw]
  exact norm_small_le hY.unf hd (AllWt.even_wtOf u 0) hspan hF σ ρ hρ τ t f hfs
end PositivityTheory.Xj7N
end
end
