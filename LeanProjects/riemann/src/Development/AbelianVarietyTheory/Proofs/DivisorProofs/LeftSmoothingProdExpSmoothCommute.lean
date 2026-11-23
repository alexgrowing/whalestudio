import Mathlib
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.LeftSmoothing

open scoped Manifold Topology
open Set Filter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem contMDiff_prodExp (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) :
    letI := h.chartedSpace; ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, 𝔤) ∞ (h.prodExp X) := by
  letI := h.chartedSpace
  intro t
  refine h.contMDiffAt_of_val ?_
  have e : (fun s => (((h.prodExp X s : G) : 𝔸ˣ) : 𝔸)) = prodExpVal (fun i => (X i : 𝔸)) :=
    funext fun s => h.val_prodExp X s
  rw [e]
  exact (contDiff_prodExpVal _).contMDiff.contMDiffAt

theorem contDiff_param (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) {f : G → ℂ}
    (hf : h.IsSmoothFun f) (g : G) :
    ContDiff ℝ ∞ (fun p : 𝔤 × (Fin n → ℝ) => f (h.prodExp X p.2 * g * h.expG p.1)) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, 𝔤 × (Fin n → ℝ)) 𝓘(ℝ, 𝔤) ∞
      (fun p : 𝔤 × (Fin n → ℝ) => h.prodExp X p.2 * g * h.expG p.1) :=
    (((contMDiff_prodExp h X).comp contDiff_snd.contMDiff).mul contMDiff_const).mul
      (h.contMDiff_expG_comp contDiff_fst)
  exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf hm).contDiff

theorem continuous_iteratedFDeriv_partial {P T E' : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {Φ : P × T → E'} (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) :
    Continuous (fun p : P × T => iteratedFDeriv ℝ k (fun Y => Φ (Y, p.2)) p.1) := by
  set L := ContinuousLinearMap.inl ℝ P T
  set H : P × T → ContinuousMultilinearMap ℝ (fun _ : Fin k => P) E' :=
    fun q => ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L) (iteratedFDeriv ℝ k Φ q)
  have hH : Continuous H :=
    (ContinuousLinearMap.continuous _).comp (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hpart : ∀ (Z : T) (Y : P), iteratedFDeriv ℝ k (fun Y => Φ (Y, Z)) Y = H (Y, Z) := by
    intro Z Y
    have e : (fun Y => Φ (Y, Z)) = (fun w => Φ (w + (0, Z))) ∘ L := by
      funext Y; simp [L]
    have hΦZ : ContDiff ℝ ∞ (fun w : P × T => Φ (w + (0, Z))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [e, L.iteratedFDeriv_comp_right hΦZ Y (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    simp [H, L]
  have e : (fun p : P × T => iteratedFDeriv ℝ k (fun Y => Φ (Y, p.2)) p.1) = H := by
    funext p; exact hpart p.2 p.1
  rw [e]; exact hH

variable (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ)

noncomputable def integrand (f : G → ℂ) (g : G) (Y : 𝔤) (t : Fin n → ℝ) : ℂ :=
  κ t * f (h.prodExp X t * g * h.expG Y)

noncomputable def conv (f : G → ℂ) (y : G) : ℂ :=
  ∫ t, κ t * f (h.prodExp X t * y)

theorem conv_mul_expG (f : G → ℂ) (g : G) (Y : 𝔤) :
    conv h X κ f (g * h.expG Y) = ∫ t, integrand h X κ f g Y t := by
  simp only [conv, integrand, mul_assoc]

variable {h X κ}

theorem contDiff_slice {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (t : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) :=
  (contDiff_param h X hf g).comp (contDiff_id.prodMk contDiff_const)

theorem iter_integrand_eq {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (k : ℕ) (Y : 𝔤)
    (t : Fin n → ℝ) :
    ParamIntegral.iter (integrand h X κ f g) k Y t =
      (ContinuousLinearMap.mul ℝ ℂ (κ t)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) Y) := by
  rw [ParamIntegral.iter]
  have e : (fun Y => integrand h X κ f g Y t) =
      (ContinuousLinearMap.mul ℝ ℂ (κ t)) ∘ (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) := by
    funext Y; simp [integrand]
  rw [e]
  exact (ContinuousLinearMap.mul ℝ ℂ (κ t)).iteratedFDeriv_comp_left
    (contDiff_slice hf g t).contDiffAt (by exact_mod_cast le_top)

theorem integrand_contDiff {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (t : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun Y => integrand h X κ f g Y t) := by
  have e : (fun Y => integrand h X κ f g Y t) =
      (ContinuousLinearMap.mul ℝ ℂ (κ t)) ∘ (fun Y : 𝔤 => f (h.prodExp X t * g * h.expG Y)) := by
    funext Y; simp [integrand]
  rw [e]
  exact (ContinuousLinearMap.mul ℝ ℂ (κ t)).contDiff.comp (contDiff_slice hf g t)

theorem integrand_cont (hκ : Continuous κ) {f : G → ℂ} (hf : h.IsSmoothFun f) (g : G) (k : ℕ) :
    Continuous (fun p : 𝔤 × (Fin n → ℝ) => ParamIntegral.iter (integrand h X κ f g) k p.1 p.2) := by
  simp_rw [iter_integrand_eq hf]
  have hc := continuous_iteratedFDeriv_partial (contDiff_param h X hf g) k
  have hL : Continuous (fun t => ContinuousLinearMap.mul ℝ ℂ (κ t)) :=
    (ContinuousLinearMap.mul ℝ ℂ).continuous.comp hκ
  have hB := ContinuousLinearMap.continuous₂ (𝕜 := ℝ) (E := ℂ →L[ℝ] ℂ)
    (F := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) ℂ)
    (G := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) ℂ)
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => 𝔤) ℂ ℂ)
  exact hB.comp ((hL.comp continuous_snd).prodMk hc)

theorem integrand_supp (hκs : HasCompactSupport κ) (f : G → ℂ) (g : G) (Y₀ : 𝔤) :
    ∃ U ∈ 𝓝 Y₀, ∃ C : Set (Fin n → ℝ), IsCompact C ∧
      ∀ Y ∈ U, ∀ t ∉ C, integrand h X κ f g Y t = 0 :=
  ⟨univ, univ_mem, tsupport κ, hκs, fun Y _ t ht => by
    simp [integrand, image_eq_zero_of_notMem_tsupport ht]⟩

theorem isSmoothFun_conv (hκ : Continuous κ) (hκs : HasCompactSupport κ) {f : G → ℂ}
    (hf : h.IsSmoothFun f) : h.IsSmoothFun (conv h X κ f) := by
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g
  simp_rw [conv_mul_expG]
  exact contDiff_integral_of_iteratedFDeriv _ (integrand_contDiff hf g)
    (integrand_cont hκ hf g) (integrand_supp hκs f g)

theorem rightDeriv_conv (hκ : Continuous κ) (hκs : HasCompactSupport κ) {f : G → ℂ}
    (hf : h.IsSmoothFun f) (Z : 𝔤) (g : G) :
    h.rightDeriv Z (conv h X κ f) g = conv h X κ (h.rightDeriv Z f) g := by
  show fderiv ℝ (fun Y : 𝔤 => conv h X κ f (g * h.expG Y)) 0 Z = _
  simp_rw [conv_mul_expG]
  rw [← iteratedFDeriv_one_apply (fun _ : Fin 1 => Z),
    iteratedFDeriv_integral_eq _ (integrand_contDiff hf g) (integrand_cont hκ hf g)
      (integrand_supp hκs f g) 1]
  have hint : Integrable (fun t => ParamIntegral.iter (integrand h X κ f g) 1 (0 : 𝔤) t) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((integrand_cont hκ hf g 1).comp (continuous_const.prodMk continuous_id)) ?_
    refine HasCompactSupport.intro hκs fun t ht => ParamIntegral.iter_eq_zero_of_eventually ?_
    exact Eventually.of_forall fun Y => by
      simp [integrand, image_eq_zero_of_notMem_tsupport ht]
  rw [ContinuousMultilinearMap.integral_apply hint]
  simp only [conv]
  congr 1
  funext t
  rw [iter_integrand_eq hf]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.mul_apply']
  rw [iteratedFDeriv_one_apply]
  rfl

variable (h X) in

noncomputable def convEnd (hκ : Continuous κ) (hκs : HasCompactSupport κ) :
    Module.End ℂ (h.smoothFuns (F := ℂ)) where
  toFun f := ⟨conv h X κ f, isSmoothFun_conv hκ hκs f.2⟩
  map_add' f₁ f₂ := by
    apply Subtype.ext
    funext y
    have hc : ∀ f : h.smoothFuns (F := ℂ), Integrable (fun t => κ t * (f : G → ℂ) (h.prodExp X t * y)) := by
      intro f
      have hfc : Continuous (f : G → ℂ) := by
        letI := h.chartedSpace
        exact (show h.IsSmoothFun (f : G → ℂ) from f.2).continuous
      exact (hκ.mul (hfc.comp ((h.continuous_prodExp X).mul continuous_const))).integrable_of_hasCompactSupport
        (hκs.mul_right)
    show ∫ t, κ t * ((f₁ : G → ℂ) + f₂) (h.prodExp X t * y) = (∫ t, κ t * (f₁ : G → ℂ) (h.prodExp X t * y)) + ∫ t, κ t * (f₂ : G → ℂ) (h.prodExp X t * y)
    rw [← integral_add (hc f₁) (hc f₂)]
    congr 1; funext t; simp [mul_add]
  map_smul' c f := by
    apply Subtype.ext
    funext y
    show ∫ t, κ t * (c • (f : G → ℂ)) (h.prodExp X t * y) = c * ∫ t, κ t * (f : G → ℂ) (h.prodExp X t * y)
    rw [← integral_const_mul]
    congr 1; funext t; simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem commute_convEnd (hκ : Continuous κ) (hκs : HasCompactSupport κ) (Z : 𝔤) :
    h.rightDerivEnd (F := ℂ) Z * convEnd h X hκ hκs = convEnd h X hκ hκs * h.rightDerivEnd Z := by
  refine LinearMap.ext fun f => Subtype.ext (funext fun y => ?_)
  exact rightDeriv_conv hκ hκs f.2 Z y

theorem adjoin_commute_convEnd (hκ : Continuous κ) (hκs : HasCompactSupport κ)
    {T : Module.End ℂ (h.smoothFuns (F := ℂ))}
    (hT : T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ)))) :
    T * convEnd h X hκ hκs = convEnd h X hκ hκs * T := by
  have hle : Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) ≤
      Subalgebra.centralizer ℂ {convEnd h X hκ hκs} := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨Z, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro A hA
    rw [Set.mem_singleton_iff] at hA
    subst hA
    exact (commute_convEnd hκ hκs Z).symm
  have := (Subalgebra.mem_centralizer_iff ℂ).1 (hle hT) _ rfl
  exact this.symm

end GlobalTheory.LeftSmoothing

open GlobalTheory.LeftSmoothing in

theorem GlobalTheory.leftSmoothing_prodExp :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (n : ℕ) (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ), Continuous κ → HasCompactSupport κ → ∀ f : h.smoothFuns (F := ℂ), ∃ v : h.smoothFuns (F := ℂ), (∀ y, (v : G → ℂ) y = ∫ t, κ t * (f : G → ℂ) (h.prodExp X t * y)) ∧ ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y, (T v : G → ℂ) y = ∫ t, κ t * (T f : G → ℂ) (h.prodExp X t * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h n X κ hκ hκs f
  refine ⟨convEnd h X hκ hκs f, fun y => rfl, fun T hT y => ?_⟩
  have e := LinearMap.congr_fun (adjoin_commute_convEnd (X := X) hκ hκs hT) f
  simp only [Module.End.mul_apply] at e
  rw [e]
  rfl
