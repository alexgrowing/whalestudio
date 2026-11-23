import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchSm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMdiffPos

noncomputable section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Sd Topology
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Af.Nf

private def incl : (Fin 2 → Fin 2 → ℝ) →L[ℝ] TR.Lie ℚ 2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i j _ => x i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private theorem incl_one : incl (Matrix.of.symm 1) = TR.oneL ℚ 2 := by
  funext i j v
  change (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) i j v
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

open Classical in
private theorem incl_single (v : InfinitePlace ℚ) (i j : Fin 2) :
    incl (Matrix.of.symm (Matrix.single i j 1)) = TR.toL (Matrix.single i j (Pi.single v 1)) := by
  funext a b w
  obtain rfl : v = w := Subsingleton.elim _ _
  change Matrix.single i j (1 : ℝ) a b = Matrix.single i j (Pi.single v (1 : ℝ) : TR.Rinf ℚ) a b v
  by_cases h : i = a ∧ j = b <;> simp [Matrix.single, h]

private theorem chart_near {k M : ℕ} {f : ℍ → ℂ} {φ : GA ℚ 2 → ℂ} (hφ : IsLift k M f φ)
    (γ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℝ) {u : GL (Fin 2) (Af ℚ)} (hu : u ∈ K1G M) :
    arch k (nsl k f h) =ᶠ[𝓝 (Matrix.of.symm 1)]
      TR.chart φ (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u)) ∘ incl := by
  have hc : Continuous fun x : Fin 2 → Fin 2 → ℝ => (Matrix.of x).det :=
    Continuous.matrix_det continuous_id
  have ho : {x : Fin 2 → Fin 2 → ℝ | 0 < (Matrix.of x).det} ∈ 𝓝 (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
    (isOpen_lt continuous_const hc).mem_nhds (by simp)
  refine Filter.eventually_of_mem ho fun x hx => ?_
  have hx' : 0 < (Matrix.of x).det := hx
  let y : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of x) hx'.ne'
  have e : incl x = TR.toL (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) y).val := rfl
  rw [Function.comp_apply, e, TR.chart_val]
  change _ = φ (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u) * upR y)
  rw [mul_assoc, mul_assoc, ← upR_comm, ← mul_assoc (upR h), ← map_mul, hφ γ _ u hu, arch,
    (nslMul k f).1 _ _ h.det_ne_zero hx']
  rfl

end UpperTheory.V.Af.Nf

open UpperTheory.V UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.liftLie :
    UpperTheory.V.Af.Nf.LiftLie := by
  intro k M hM f hf φ hφ v
  have key : ∀ g, (TR.Eop v 0 1 φ).1 g - (TR.Eop v 1 0 φ).1 g = Complex.I * k * φ.1 g ∧
      (TR.Eop v 0 0 φ).1 g - (TR.Eop v 1 1 φ).1 g =
        Complex.I * ((TR.Eop v 0 1 φ).1 g + (TR.Eop v 1 0 φ).1 g) := by
    intro g
    obtain ⟨γ, h, u, hu, rfl⟩ := decomp M hM g
    rw [hφ γ h u hu]
    refine archDer k (nsl k f h) ((nslSl k f).2.2 hf _ h.det_ne_zero)
      (fun i j => (TR.Eop v i j φ).1 (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u))) fun i j => ?_
    rw [(chart_near hφ γ h hu).fderiv_eq,
      fderiv_comp _ (by rw [incl_one]; exact TR.differentiableAt_chart φ.2 _) incl.differentiableAt,
      incl_one, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, incl_single v]
    rfl
  exact ⟨Subtype.ext (funext fun g => (key g).1), Subtype.ext (funext fun g => (key g).2)⟩
