import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PRadicalTorusModulusCoords

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

def heisPairMap (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) (w : InfinitePlace E) :
    (ι → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  Matrix.mulVecLin (Matrix.of ![star (vecAt v x₀ w) ᵥ* gramAt h v w,
    star (vecAt v w₀ w) ᵥ* gramAt h v w])

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι] in
theorem heisPairMap_apply (w : InfinitePlace E) (z : ι → ℂ) :
    heisPairMap h v x₀ w₀ w z =
      ![hForm (gramAt h v w) (vecAt v x₀ w) z, hForm (gramAt h v w) (vecAt v w₀ w) z] := by
  funext i
  fin_cases i <;> simp [heisPairMap, hForm, Matrix.mulVec, dotProduct_mulVec]

def heisYAt (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) (w : InfinitePlace E) :
    Submodule ℂ (ι → ℂ) :=
  LinearMap.ker (heisPairMap h v x₀ w₀ w)

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι] in
theorem mem_heisYAt {w : InfinitePlace E} {z : ι → ℂ} :
    z ∈ heisYAt h v x₀ w₀ w ↔ hForm (gramAt h v w) (vecAt v x₀ w) z = 0 ∧
      hForm (gramAt h v w) (vecAt v w₀ w) z = 0 := by
  rw [heisYAt, LinearMap.mem_ker, heisPairMap_apply]
  constructor
  · intro hz
    exact ⟨by simpa using congrFun hz 0, by simpa using congrFun hz 1⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i <;> simp [h0, h1]

theorem finrank_heisYAt (hp : IsHyperbolicPair h x₀ w₀) (w : InfinitePlace E) :
    finrank ℂ (heisYAt h v x₀ w₀ w) + 2 = Fintype.card ι := by
  obtain ⟨hH, -, ha, hb, hab⟩ := hyperbolic_at_place h v hp w
  have hba : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
    rw [← hForm_conj hH, hab, map_one]
  have hs : Function.Surjective (heisPairMap h v x₀ w₀ w) := fun u =>
    ⟨u 0 • vecAt v w₀ w + u 1 • vecAt v x₀ w, by
      rw [heisPairMap_apply]
      funext i
      fin_cases i <;> simp [hForm_add_right, hForm_smul_right, ha, hb, hab, hba]⟩
  have e := LinearMap.finrank_range_add_finrank_ker (heisPairMap h v x₀ w₀ w)
  rw [LinearMap.range_eq_top.2 hs, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fintype_fun_eq_card] at e
  rw [heisYAt]
  omega

def heisYEquiv (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    heisY h v x₀ w₀ ≃ₗ[ℝ] ((w : InfinitePlace E) → heisYAt h v x₀ w₀ w) where
  toFun y w := ⟨(y : InfinitePlace E → ι → ℂ) w, mem_heisYAt.2 (y.2 w)⟩
  invFun z := ⟨fun w => (z w : ι → ℂ), mem_heisY.2 fun w => mem_heisYAt.1 (z w).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def heisYAtEquiv (hp : IsHyperbolicPair h x₀ w₀) (w : InfinitePlace E) :
    heisYAt h v x₀ w₀ w ≃ₗ[ℂ] (Fin (Fintype.card ι - 2) → ℂ) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun]
    have := finrank_heisYAt (v := v) hp w
    omega)

theorem det_heisScale (hp : IsHyperbolicPair h x₀ w₀) (c : InfinitePlace E → ℂ) :
    LinearMap.det (heisScale h v x₀ w₀ c) =
      ∏ w, Complex.normSq (c w) ^ (Fintype.card ι - 2) := by
  set e : heisY h v x₀ w₀ ≃ₗ[ℝ] (InfinitePlace E → Fin (Fintype.card ι - 2) → ℂ) :=
    (heisYEquiv h v x₀ w₀).trans
      (LinearEquiv.piCongrRight fun w => (heisYAtEquiv hp w).restrictScalars ℝ) with he
  set P : (InfinitePlace E → Fin (Fintype.card ι - 2) → ℂ) →ₗ[ℝ]
      (InfinitePlace E → Fin (Fintype.card ι - 2) → ℂ) :=
    LinearMap.pi (fun w => ((c w • LinearMap.id :
      (Fin (Fintype.card ι - 2) → ℂ) →ₗ[ℂ] (Fin (Fintype.card ι - 2) → ℂ)).restrictScalars ℝ).comp
        (LinearMap.proj w)) with hP
  have key : heisScale h v x₀ w₀ c = (e.symm : _ →ₗ[ℝ] _) ∘ₗ P ∘ₗ (e.symm.symm : _ →ₗ[ℝ] _) := by
    apply LinearMap.ext
    intro y
    apply e.injective
    simp only [LinearEquiv.symm_symm, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    funext w
    simp only [he, hP, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply,
      LinearEquiv.restrictScalars_apply, LinearMap.pi_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearMap.restrictScalars_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    rw [← map_smul]
    rfl
  rw [key, LinearMap.det_conj, hP, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one,
    Module.finrank_fin_fun, map_pow, Algebra.norm_complex_apply]

def placeScale (r : InfinitePlace E → ℝ) : (InfinitePlace E → ℝ) →ₗ[ℝ] (InfinitePlace E → ℝ) :=
  LinearMap.pi fun w => (r w • LinearMap.id).comp (LinearMap.proj w)

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem det_placeScale (r : InfinitePlace E → ℝ) : LinearMap.det (placeScale r) = ∏ w, r w := by
  rw [placeScale, LinearMap.det_pi]
  simp

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
