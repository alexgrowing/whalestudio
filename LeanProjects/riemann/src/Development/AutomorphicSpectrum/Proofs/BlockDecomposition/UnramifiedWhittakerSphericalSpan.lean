import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.SphericalSpan

open GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.Spherical

def rightRep (G : Type*) [Group G] : Representation ℂ G (G → ℂ) where
  toFun x :=
    { toFun := fun f g => f (g * x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun f => funext fun g => by simp
  map_mul' x y := LinearMap.ext fun f => funext fun g => by simp [mul_assoc]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]

theorem heckeAct_rightRep_apply {a : GL (Fin n) F → ℂ}
    (ha : a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) {f : GL (Fin n) F → ℂ}
    (hf : f ∈ smoothVectors (rightRep (GL (Fin n) F))) (g : GL (Fin n) F) :
    heckeAct μ (rightRep (GL (Fin n) F)) a f g = ∫ x, a x * f (g * x) ∂μ :=
  dual_heckeAct μ ha hf (LinearMap.proj g)

include μ in

theorem eq_mul_sphericalWhittaker_of_mem_span {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (hψ₁ : ∃ x : F, (GLnLocal.uniformizer F : F) * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) (z : Fin n → ℂˣ)
    {W : GL (Fin n) F → ℂ}
    (hW : W ∈ Submodule.span ℂ {f : GL (Fin n) F → ℂ | ∃ h : GL (Fin n) F,
      f = fun g => Spherical.sphericalWhittaker ψ₀ z (g * h)})
    (hWK : ∀ g, ∀ k ∈ GLnLocal.integralGL F n, W (g * k) = W g) (g : GL (Fin n) F) :
    W g = W 1 * Spherical.sphericalWhittaker ψ₀ z g := by
  have hKc := GLnLocal.isCompact_integralGL F n
  have hKo := GLnLocal.isOpen_integralGL F n
  set ρ := rightRep (GL (Fin n) F) with hρ
  set φ : GL (Fin n) F → ℂ := Spherical.sphericalWhittaker ψ₀ z with hφdef
  have hfix : φ ∈ fixedVectors ρ (GLnLocal.integralGL F n) := fun k hk =>
    funext fun y => sphericalWhittaker_mul_right hψ₀ z y hk
  have hφs : φ ∈ smoothVectors ρ := smooth_of_mem_fixedVectors hKo hfix
  have heig : ∀ h : SphericalHecke μ (F := F) (n := n),
      heckeAct μ ρ (h : HeckeAlgebra μ) φ =
        evalAt z (satakeTransform μ h) • φ := fun h => funext fun y => by
    rw [heckeAct_rightRep_apply μ (h : HeckeAlgebra μ).mem hφs y]
    exact integral_mul_sphericalWhittaker hψ₀ hψ₁ z h y
  have key : ∀ u ∈ Submodule.span ℂ {f : GL (Fin n) F → ℂ | ∃ h : GL (Fin n) F,
      f = fun g => Spherical.sphericalWhittaker ψ₀ z (g * h)},
      u ∈ smoothVectors ρ ∧ ∃ c : ℂ, heckeAct μ ρ (idem μ hKc hKo) u = c • φ := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x₀, rfl⟩ := hx
      have e : (fun g => Spherical.sphericalWhittaker ψ₀ z (g * x₀)) = ρ x₀ φ := rfl
      rw [e]
      refine ⟨?_, evalAt z (satakeTransform μ (HeckeAlgebraLevel.corner hKc hKo
        (leftReg μ x₀ (idem μ hKc hKo)))), ?_⟩
      · let H : Subgroup (GL (Fin n) F) :=
          (GLnLocal.integralGL F n).comap (MulAut.conj x₀⁻¹).toMonoidHom
        have hHo : IsOpen (H : Set (GL (Fin n) F)) :=
          hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
        refine Subgroup.isOpen_mono (H₁ := H) (fun w hw => ?_) hHo
        rw [mem_stabilizerOf, ← Module.End.mul_apply, ← map_mul]
        have : w * x₀ = x₀ * (x₀⁻¹ * w * x₀⁻¹⁻¹) := by group
        rw [this, map_mul, Module.End.mul_apply, hfix (x₀⁻¹ * w * x₀⁻¹⁻¹) hw]
      · rw [heckeAct_idem_apply hKc hKo x₀ hfix, ← heckeAct_corner hKc hKo hfix]
        exact heig (HeckeAlgebraLevel.corner hKc hKo _)
    | zero =>
      exact ⟨zero_mem _, 0, by rw [heckeAct_zero_right (idem μ hKc hKo).mem, zero_smul]⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨hs, c, hc⟩ := hx
      obtain ⟨hs', c', hc'⟩ := hx'
      exact ⟨add_mem hs hs', c + c', by
        rw [heckeAct_add_right (idem μ hKc hKo).mem hs hs', hc, hc', add_smul]⟩
    | smul a x _ hx =>
      obtain ⟨hs, c, hc⟩ := hx
      exact ⟨Submodule.smul_mem _ a hs, a * c, by
        rw [heckeAct_smul_right (idem μ hKc hKo).mem a hs, hc, smul_smul]⟩
  obtain ⟨-, c, hc⟩ := key W hW
  have hWfix : W ∈ fixedVectors ρ (GLnLocal.integralGL F n) := fun k hk =>
    funext fun y => hWK y k hk
  rw [heckeAct_idem_of_mem hKc hKo hWfix] at hc
  have h1 : φ 1 = 1 := sphericalWhittaker_one hψ₀ z
  have hW1 : W 1 = c := by
    rw [hc]
    simp [h1]
  rw [hW1, hc]
  rfl

end GlobalTheory.CompanionTheory.SphericalSpan

open GlobalTheory.CompanionTheory.SphericalSpan in

theorem GlobalTheory.CompanionTheory.SphericalSpan.eq_mul_sphericalWhittaker :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (n : ℕ) (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) →
      (∃ x : F, (GLnLocal.uniformizer F : F) * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) →
      ∀ (z : Fin n → ℂˣ) (W : GL (Fin n) F → ℂ),
        W ∈ Submodule.span ℂ {f : GL (Fin n) F → ℂ | ∃ h : GL (Fin n) F,
          f = fun g => Spherical.sphericalWhittaker ψ₀ z (g * h)} →
        (∀ g, ∀ k ∈ GLnLocal.integralGL F n, W (g * k) = W g) →
        ∀ g, W g = W 1 * Spherical.sphericalWhittaker ψ₀ z g := by
  intro F _ _ _ _ n ψ₀ hψ₀ hψ₁ z W hW hWK g
  borelize (GL (Fin n) F)
  exact eq_mul_sphericalWhittaker_of_mem_span (Measure.haar : Measure (GL (Fin n) F)) hψ₀ hψ₁ z hW
    hWK g

end
