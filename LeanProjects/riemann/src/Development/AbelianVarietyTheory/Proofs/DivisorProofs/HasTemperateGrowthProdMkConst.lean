import Mathlib

noncomputable section

open scoped SchwartzMap

namespace GlobalTheory.SchwartzFstOp

variable {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasTemperateGrowth_prodMk_const (x' : V') : Function.HasTemperateGrowth (fun x : V => (x, x')) := by
  have h := (ContinuousLinearMap.inl ℝ V V').hasTemperateGrowth.add
    (Function.HasTemperateGrowth.const ((0 : V), x'))
  convert h using 1
  funext x
  simp

theorem antilipschitz_prodMk_const (x' : V') : AntilipschitzWith 1 (fun x : V => (x, x')) :=
  AntilipschitzWith.of_le_mul_dist fun x y => by
    simp only [NNReal.coe_one, one_mul, Prod.dist_eq, dist_self]
    exact le_max_left _ _

def sliceCLM (x' : V') : 𝓢(V × V', ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (hasTemperateGrowth_prodMk_const x') (antilipschitz_prodMk_const x')

@[simp] theorem sliceCLM_apply (x' : V') (f : 𝓢(V × V', ℂ)) (x : V) : sliceCLM x' f x = f (x, x') := rfl

def lineSnd (v' : V') : 𝓢(V × V', ℂ) →L[ℂ] 𝓢(V × V', ℂ) :=
  LineDeriv.lineDerivOpCLM ℂ 𝓢(V × V', ℂ) ((0 : V), v')

theorem lineSnd_apply (v' : V') (f : 𝓢(V × V', ℂ)) (p : V × V') :
    lineSnd v' f p = fderiv ℝ f p ((0 : V), v') := by
  rw [lineSnd, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem lineSnd_add (v₁ v₂ : V') (f : 𝓢(V × V', ℂ)) :
    lineSnd (v₁ + v₂) f = lineSnd v₁ f + lineSnd v₂ f := by
  ext p
  simp only [lineSnd_apply, SchwartzMap.add_apply]
  rw [← map_add]
  simp

theorem lineSnd_smul (c : ℝ) (v : V') (f : 𝓢(V × V', ℂ)) :
    lineSnd (c • v) f = (c : ℂ) • lineSnd v f := by
  ext p
  simp only [lineSnd_apply, SchwartzMap.smul_apply]
  rw [show ((0 : V), c • v) = c • ((0 : V), v) by simp, map_smul]
  simp [Complex.real_smul]

def opFst (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (p : W × V') : E :=
  T (sliceCLM p.2 f) p.1

theorem opFst_apply (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (y : W) (x' : V') :
    opFst T f (y, x') = T (sliceCLM x' f) y := rfl

def dSndCLM [FiniteDimensional ℝ V'] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (p : W × V') :
    V' →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v' => opFst T (lineSnd v' f) p
      map_add' := fun v₁ v₂ => by simp [opFst, lineSnd_add]
      map_smul' := fun c v => by
        simp only [opFst, lineSnd_smul, map_smul, SchwartzMap.smul_apply, RingHom.id_apply]
        rw [Complex.coe_smul] }

theorem dSndCLM_apply [FiniteDimensional ℝ V'] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (p : W × V')
    (v' : V') : dSndCLM T f p v' = opFst T (lineSnd v' f) p := rfl

end GlobalTheory.SchwartzFstOp
