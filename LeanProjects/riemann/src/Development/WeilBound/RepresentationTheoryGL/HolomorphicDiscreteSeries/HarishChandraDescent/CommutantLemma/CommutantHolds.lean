import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Commutant
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothCore
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3.CommutantSmoothMaps

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smooth_map (T : H →L[ℂ] H) (hT : ∀ g ∈ UJset ε, Commute T (ρ g)) {v : H} (hv : IsSmoothVecU ε ρ v) :
    IsSmoothVecU ε ρ (T v) := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfe⟩ := hv g₀ hg₀
  refine ⟨U, (T.restrictScalars ℝ) ∘ F, hU, hgU, (T.restrictScalars ℝ).contDiff.comp_contDiffOn hF,
    fun g hg hgJ => ?_⟩
  have hc := congrArg (fun S : H →L[ℂ] H => S v) (hT g hgJ)
  change ρ g (T v) = T (F g)
  rw [← hfe g hg hgJ]
  exact hc.symm

theorem dS_map (hρ : IsURepOn (UJset ε) ρ) (T : H →L[ℂ] H) (hT : ∀ g ∈ UJset ε, Commute T (ρ g))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v : H} (hv : IsSmoothVecU ε ρ v) :
    dS ρ X (T v) = T (dS ρ X v) := by
  have hf := hasDerivAt_dS hρ hX hv
  have hTf := (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf
  have heq : (fun t : ℝ => ρ (NormedSpace.exp ((t : ℂ) • X)) (T v)) =
      ⇑(T.restrictScalars ℝ) ∘ fun t : ℝ => ρ (NormedSpace.exp ((t : ℂ) • X)) v := by
    funext t
    have hc := congrArg (fun S : H →L[ℂ] H => S v) (hT _ (exp_smul_mem_UJset hX t))
    exact hc.symm
  rw [show dS ρ X (T v) = deriv (fun t : ℝ => ρ (NormedSpace.exp ((t : ℂ) • X)) (T v)) 0 from rfl, heq]
  exact hTf.deriv

end PositivityTheory.RgHe3.CommutantSmoothMaps

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS CommutantSmoothMaps

theorem commutant_holds : Commutant := by
  intro n ε H _ _ _ ρ hρ T hT
  let T' : Module.End ℂ ↥(smD ε ρ) :=
    { toFun := fun x => ⟨T x, (mem_smD_iff _ _ _).2 (smooth_map T hT ((mem_smD_iff _ _ _).1 x.2))⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro c x
        ext
        simp }
  refine ⟨T', fun x => rfl, fun a b x => ?_⟩
  have hxs : IsSmoothVecU ε ρ (x : H) := (mem_smD_iff _ _ _).1 x.2
  apply Subtype.ext
  change T ↑(smE ε ρ a b x) = ↑(smE ε ρ a b (T' x))
  rw [smE_apply hρ, smE_apply hρ]
  change T (dS ρ (S7.cpart1 ε (single a b 1)) ↑x + Complex.I • dS ρ (S7.cpart2 ε (single a b 1)) ↑x) =
    dS ρ (S7.cpart1 ε (single a b 1)) (T ↑x) + Complex.I • dS ρ (S7.cpart2 ε (single a b 1)) (T ↑x)
  rw [map_add, map_smul, dS_map hρ T hT (SmDerA.inG_cpart1 ε _) hxs,
    dS_map hρ T hT (SmDerA.inG_cpart2 ε _) hxs]

end PositivityTheory.RgHe3
