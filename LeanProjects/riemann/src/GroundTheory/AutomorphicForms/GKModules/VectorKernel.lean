import Mathlib
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.GKModules.Garding
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian

namespace GroundTheory.Automorphic

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

theorem rightDeriv_orbit {v : E} (hv : h.IsSmoothVector π v) (X : 𝔤) (g : G) :
    h.rightDeriv X (fun g => π g v) g = π g (h.derivOp π X v) := by
  have e : (fun Y : 𝔤 => π (g * h.expG Y) v) = ((π g).restrictScalars ℝ) ∘ h.expOrbit π v := by
    funext Y
    simp [expOrbit]
  have hd := (h.differentiable_expOrbit π hv 0).hasFDerivAt
  have hc := ((π g).restrictScalars ℝ).hasFDerivAt.comp (0 : 𝔤) hd
  unfold rightDeriv
  rw [e, hc.fderiv]
  rfl

def orbitL : h.smoothVectors π →ₗ[ℂ] h.smoothFuns (F := E) where
  toFun v := ⟨fun g => π g v, v.2⟩
  map_add' v w := by
    apply Subtype.ext
    funext g
    simp
  map_smul' c v := by
    apply Subtype.ext
    funext g
    simp

@[simp] theorem coe_orbitL (v : h.smoothVectors π) :
    ((h.orbitL π v : h.smoothFuns (F := E)) : G → E) = fun g => π g v := rfl

theorem rightUAction_orbitL (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra)
    (v : h.smoothVectors π) :
    h.rightUAction u (h.orbitL π v) = h.orbitL π (h.uAction π u v) := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction generalizing v with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]
    apply Subtype.ext
    funext g
    simp [Module.algebraMap_end_apply]
  | ι X =>
    change h.rightUAction (UniversalEnvelopingAlgebra.ι ℝ X) (h.orbitL π v) =
      h.orbitL π (h.uAction π (UniversalEnvelopingAlgebra.ι ℝ X) v)
    rw [rightUAction_ι, uAction_ι]
    apply Subtype.ext
    funext g
    exact h.rightDeriv_orbit π v.2 (h.ofLie X) g
  | mul a b ha hb =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb, map_add]

def dualComp (l : StrongDual ℂ E) : h.smoothFuns (F := E) →ₗ[ℂ] h.smoothFuns (F := ℂ) where
  toFun f := ⟨fun g => l ((f : G → E) g), by
    show h.IsSmoothFun (fun g => l ((f : G → E) g))
    let _ := h.chartedSpace
    have hf : h.IsSmoothFun (f : G → E) := f.2
    exact (l.restrictScalars ℝ).contDiff.comp_contMDiff hf⟩
  map_add' f f' := by
    apply Subtype.ext
    funext g
    simp
  map_smul' c f := by
    apply Subtype.ext
    funext g
    simp

@[simp] theorem coe_dualComp (l : StrongDual ℂ E) (f : h.smoothFuns (F := E)) :
    ((h.dualComp l f : h.smoothFuns (F := ℂ)) : G → ℂ) = fun g => l ((f : G → E) g) := rfl

theorem dualComp_rightDerivEnd (l : StrongDual ℂ E) (X : 𝔤) (f : h.smoothFuns (F := E)) :
    h.dualComp l (h.rightDerivEnd X f) = h.rightDerivEnd X (h.dualComp l f) := by
  apply Subtype.ext
  funext g
  simp only [coe_dualComp, coe_rightDerivEnd]
  have hf : h.IsSmoothFun (f : G → E) := f.2
  have e : (fun Y : 𝔤 => l ((f : G → E) (g * h.expG Y))) =
      (l.restrictScalars ℝ) ∘ fun Y : 𝔤 => (f : G → E) (g * h.expG Y) := rfl
  have hc := (l.restrictScalars ℝ).hasFDerivAt.comp (0 : 𝔤)
    (h.differentiable_comp_expG hf g 0).hasFDerivAt
  unfold rightDeriv
  rw [show (fun Y : 𝔤 => (fun g => l ((f : G → E) g)) (g * h.expG Y)) =
    (l.restrictScalars ℝ) ∘ fun Y : 𝔤 => (f : G → E) (g * h.expG Y) from e, hc.fderiv]
  rfl

theorem dualComp_laplacian (l : StrongDual ℂ E) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ h.lieSubalgebra) (f : h.smoothFuns (F := E)) :
    h.dualComp l (h.laplacian (F := E) b f) = h.laplacian (F := ℂ) b (h.dualComp l f) := by
  simp only [laplacian, LinearMap.sum_apply, map_sum, Module.End.mul_apply, dualComp_rightDerivEnd]

variable [MeasurableSpace G] [BorelSpace G]

theorem exists_integrated_eq_of_zkFinite [CompleteSpace E] (μ : Measure G) [μ.IsHaarMeasure]
    (Kc : Subgroup G) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℝ h.lieSubalgebra) (b : Module.Basis ι ℝ h.lieSubalgebra) (ε : ι → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : h.lieSubalgebra, B X Y = B Y X)
    (hinv : ∀ X Y Z : h.lieSubalgebra, B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆)
    (hK : ∀ i, ε i = -1 → ∀ t : ℝ, h.expG (t • h.ofLie (b i)) ∈ Kc)
    (v : h.smoothVectors π)
    (hvK : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kc => π k (v : E))))
    (hvZ : FiniteDimensional ℂ
      (Submodule.span ℂ ((fun z => h.uAction π z v) '' (h.centerU : Set _))))
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ κ : G → ℂ, h.IsTestFunction κ ∧ tsupport κ ⊆ U ∧ π.integrated μ κ v = v := by

  let T : E →ₗ[ℂ] (G → E) :=
    { toFun := fun w g => π g w
      map_add' := fun w w' => by funext g; simp
      map_smul' := fun c w => by funext g; simp }
  set o := h.orbitL π v with ho
  have hfK : IsRightKFinite Kc (o : G → E) := by
    unfold IsRightKFinite
    have e : Set.range (fun k : Kc => rightTranslate (k : G) (o : G → E)) =
        T '' Set.range (fun k : Kc => π k (v : E)) := by
      ext f
      constructor
      · rintro ⟨k, rfl⟩
        refine ⟨_, ⟨k, rfl⟩, ?_⟩
        funext g
        simp [T, ho, rightTranslate]
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        refine ⟨k, ?_⟩
        funext g
        simp [T, ho, rightTranslate]
    rw [e, Submodule.span_image]
    infer_instance
  have hfZ : h.IsZFinite o := by
    unfold IsZFinite
    have e : (fun z => h.rightUAction z o) '' (h.centerU : Set _) =
        h.orbitL π '' ((fun z => h.uAction π z v) '' (h.centerU : Set _)) := by
      rw [Set.image_image]
      refine Set.image_congr fun z _ => ?_
      exact h.rightUAction_orbitL π z v
    rw [e, Submodule.span_image]
    infer_instance
  obtain ⟨P, hPm, hPd, hP⟩ :=
    h.exists_aeval_laplacian_eq_zero Kc B b ε hε horth hsymm hinv hK o hfK hfZ
  obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := h.exists_kernel_eq_conv_of_aeval_laplacian μ b P hPm hPd hU
  have htest : h.IsTestFunction κ := ⟨hκs, hκc⟩
  refine ⟨κ, htest, hκU, ?_⟩
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun l => ?_
  have hζ : Polynomial.aeval (h.laplacian (F := ℂ) b) P (h.dualComp l o) = 0 := by
    rw [← AutomorphicForm.map_aeval_apply_of_intertwine (h.dualComp l)
      (fun f => h.dualComp_laplacian l b f) P o, hP, map_zero]
  have h1 := hκ (h.dualComp l o) hζ 1
  simp only [coe_dualComp, ho, coe_orbitL, one_mul, BanachRep.map_one_apply] at h1
  rw [BanachRep.integrated, ← l.integral_comp_comm (h.integrable_smul_orbit π μ htest v), h1]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [mul_comm]

end IsExpLieAlgebra

end

end GroundTheory.Automorphic
