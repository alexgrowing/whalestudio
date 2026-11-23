import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.PairingL2
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasDerivAtLpOfDominated

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open scoped InnerProductSpace

namespace PositivityTheory.PRW.GKD

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def expG (X : Lie E a) (t : ℝ) : GL (Fin a) (Cinf E) := (Matrix.isUnit_exp (t • Matrix.of X)).unit

theorem expG_val (X : Lie E a) (t : ℝ) : (expG X t).val = NormedSpace.exp (t • Matrix.of X) :=
  IsUnit.unit_spec _

theorem expG_zero (X : Lie E a) : expG X 0 = 1 := by
  ext1
  rw [expG_val]
  simp

open scoped Matrix.Norms.Operator in

theorem hasDerivAt_toL_exp (X : Lie E a) (t : ℝ) :
    HasDerivAt (fun s : ℝ => toL (NormedSpace.exp (s • Matrix.of X))) (rmul X (toL (NormedSpace.exp (t • Matrix.of X)))) t := by
  let L : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.of X) t
  exact L.hasFDerivAt.comp_hasDerivAt t h1

theorem hasDerivAt_expG {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (X : Lie E a) (x : GA E a) (t : ℝ) :
    HasDerivAt (fun s => φ (x * infGL E a (expG X s))) (lieD X φ (x * infGL E a (expG X t))) t := by
  have hx : toL (expG X t).val ∈ invSet E a := val_mem_invSet _
  have hf := ((contDiffAt_chart hφ x hx).differentiableAt (by simp)).hasFDerivAt
  have hc := hasDerivAt_toL_exp X t
  rw [← expG_val] at hc
  have h := hf.comp_hasDerivAt t hc
  have e1 : (fun s => φ (x * infGL E a (expG X s))) = chart φ x ∘ fun s : ℝ => toL (NormedSpace.exp (s • Matrix.of X)) := by
    funext s
    rw [Function.comp_apply, ← expG_val, chart_val]
  rw [e1]
  refine h.congr_deriv ?_
  rw [← chart_lieD hφ X x hx, chart_val]

theorem hasDerivAt_R (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    [IsFiniteMeasure (quotMeasure (latticeGL E a) μ)] {φ : Sm E a} (X : Lie E a)
    (hl : MemL2Quotient (latticeGL E a) μ φ.1) (hl' : MemL2Quotient (latticeGL E a) μ (lie E a X φ).1)
    {C : ℝ} (hC : ∀ g, ‖(lie E a X φ).1 g‖ ≤ C) :
    HasDerivAt (fun t => R (latticeGL E a) μ (infGL E a (expG X t)) hl.toL2) hl'.toL2 0 := by
  refine GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve.hasDerivAt_Lp_of_dominated _ _
    (fun t q => descend (latticeGL E a) (fun x => φ.1 (x * infGL E a (expG X t))) q)
    (fun t q => descend (latticeGL E a) (fun x => lieD X φ.1 (x * infGL E a (expG X t))) q)
    (fun _ => C) 0 1 one_pos ?_ ?_ ?_ ?_ ?_
  · intro t
    rw [right_translate_toL2]
    exact (hl.mul_right _).coeFn_toL2
  · have e : (fun q => descend (latticeGL E a) (fun x => lieD X φ.1 (x * infGL E a (expG X 0))) q) =
        descend (latticeGL E a) (lie E a X φ).1 := by
      funext q
      simp [descend, expG_zero]
    rw [e]
    exact hl'.coeFn_toL2
  · exact memLp_const C
  · intro q t _
    exact hasDerivAt_expG φ.2 X q.out t
  · intro q t _
    exact hC _

theorem inner_lie_skew' (hB : GlobalTheory.Published.CuspFormsBoundedGL) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    {π : CuspSub E a} (hπ : IsNormalised π) (X : Lie E a) (f g : π.V) :
    ⟪toL2ₗ μ π.V (memL2_normalised_cusp_form hB μ hπ) (π.op (.lie X) f), toL2ₗ μ π.V (memL2_normalised_cusp_form hB μ hπ) g⟫_ℂ +
      ⟪toL2ₗ μ π.V (memL2_normalised_cusp_form hB μ hπ) f,
        toL2ₗ μ π.V (memL2_normalised_cusp_form hB μ hπ) (π.op (.lie X) g)⟫_ℂ = 0 := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  set hL := memL2_normalised_cusp_form hB μ hπ
  have hbd : ∀ x : π.V, ∃ C : ℝ, ∀ g, ‖(lie E a X x.1).1 g‖ ≤ C := fun x =>
    hB E a _ (π.cusp _ (π.stable (.lie X) x.1 x.2)) fun t g => congrArg norm (hπ _ (π.stable (.lie X) x.1 x.2) t g)
  obtain ⟨C1, h1⟩ := hbd f
  obtain ⟨C2, h2⟩ := hbd g
  have df := hasDerivAt_R μ X (hL f.1 f.2) (hL _ (π.stable (.lie X) f.1 f.2)) h1
  have dg := hasDerivAt_R μ X (hL g.1 g.2) (hL _ (π.stable (.lie X) g.1 g.2)) h2
  have hd := HasDerivAt.inner ℂ df dg
  have hconst : (fun t => ⟪R (latticeGL E a) μ (infGL E a (expG X t)) (hL f.1 f.2).toL2,
      R (latticeGL E a) μ (infGL E a (expG X t)) (hL g.1 g.2).toL2⟫_ℂ) =
      fun _ => ⟪(hL f.1 f.2).toL2, (hL g.1 g.2).toL2⟫_ℂ := funext fun t => inner_R μ _ _ _
  rw [hconst] at hd
  have h0 := hd.unique (hasDerivAt_const _ _)
  simp only [expG_zero, map_one, ContinuousLinearMap.one_apply] at h0
  rw [add_comm]
  exact h0

end PositivityTheory.PRW.GKD

end
