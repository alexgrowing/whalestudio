import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.FrameRead

open Formalism.IndefR.Bridge

theorem linInd_of_basis {K C X M I : Type} [Field K] [Field C] [AddCommGroup X] [Module K X] [AddCommGroup M] [Module C M]
    (φ : K →+* C) (f : X →ₛₗ[φ] M) (b : Module.Basis I K X) (h : LinearIndependent C fun i => f (b i))
    (n : ℕ) (x : Fin n → X) (hx : LinearIndependent K x) : LinearIndependent C fun a => f (x a) := by
  classical
  have h1 : LinearIndependent K fun a => b.repr (x a) :=
    hx.map' b.repr.toLinearMap (LinearMap.ker_eq_bot.2 b.repr.injective)
  have h2 := GlobalTheory.LatBC.linInd_mapRange φ φ.injective h1
  have h3 := h2.map' (Finsupp.linearCombination C fun i => f (b i)) (LinearMap.ker_eq_bot.2 h)
  refine (funext fun a => ?_ : (fun a => f (x a)) = _) ▸ h3
  simp only [Function.comp_apply]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
  conv_lhs => rw [← b.linearCombination_repr (x a), Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  simp only [map_smulₛₗ, Finsupp.sum]

theorem exists_avatar {K C X W M I : Type} [Field K] [Field C] [AddCommGroup X] [Module K X] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup M] [Module C M] [Fintype I] (io : C ≃+* ℂ) {σ : K →+* ℂ} {e0 : K →+* C} (h : ∀ x, io (e0 x) = σ x)
    (b : Module.Basis I K X) (c0 : X →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => c0 (b i))
    (hsp : Submodule.span ℂ (Set.range fun i => c0 (b i)) = ⊤) (Φ : X →ₛₗ[e0] M) (hΦ : LinearIndependent C fun i => Φ (b i)) :
    ∃ θ : W →+ M, (∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w) ∧ (∀ x, θ (c0 x) = Φ x) ∧ Function.Injective θ := by
  classical
  let B : Module.Basis I ℂ W := Module.Basis.mk hli hsp.ge
  have hB : ∀ i, B i = c0 (b i) := fun i => Module.Basis.mk_apply _ _ i
  let θ : W →+ M :=
    { toFun := fun w => ∑ i, io.symm (B.repr w i) • Φ (b i)
      map_zero' := by simp
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib] }
  have hθ : ∀ w, θ w = ∑ i, io.symm (B.repr w i) • Φ (b i) := fun _ => rfl
  have hs : ∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w := fun a w => by
    simp [hθ, Finset.smul_sum, mul_smul]
  have hb : ∀ i, θ (c0 (b i)) = Φ (b i) := fun i => by
    rw [← hB, hθ, B.repr_self, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Finsupp.single_apply, hj.symm]
    · simp
  refine ⟨θ, hs, fun x => ?_, (injective_iff_map_eq_zero θ).2 fun w hw => ?_⟩
  · rw [← b.sum_repr x]
    simp only [map_sum, map_smulₛₗ, hs, hb, ← h, RingEquiv.symm_apply_apply]
  · have := Fintype.linearIndependent_iff.1 hΦ _ ((hθ w).symm.trans hw)
    refine B.ext_elem fun i => ?_
    simpa using this i

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G}
  {χ : J →* ℂˣ}

theorem exists_reading (P : ClassPres ι S σ ρ J χ) {C M : Type} [Field C] [AddCommGroup M] [Module C M] (io : C ≃+* ℂ)
    {e0 : K →+* C} (h : ∀ x, io (e0 x) = σ x) (θ : W →+ M) (hs : ∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w)
    (hinj : Function.Injective θ) (Λ : G →* Module.End C M) (hΛ : ∀ γ w, θ (ρ γ w) = Λ (ι γ) (θ w)) :
    ∃ rd : S.Forms →ₛₗ[e0] (G → M),
      (∀ f γ g, rd f (ι γ * g) = rd f g) ∧
      (∀ f (k : J) g, Λ k (rd f (g * k)) = io.symm (χ k : ℂ) • rd f g) ∧
      (∀ (n : ℕ) (f : Fin n → S.Forms), LinearIndependent K f → LinearIndependent C fun a => rd (f a)) ∧
      (∀ (f f' : S.Forms) (A : Finset G), P.ext f' = dcOp A (P.ext f) → (∀ a ∈ A, Λ a = 1) → ∀ g, rd f' g = ∑ s ∈ A, rd f (g * s)) ∧
      ∀ (f : S.Forms) c, rd f (P.y c) = Λ (P.y c)⁻¹ (θ (P.coef ((f : S.Cl → S.V) c))) := by
  let rd : S.Forms →ₛₗ[e0] (G → M) :=
    { toFun := fun f g => Λ g⁻¹ (θ (P.extL f g))
      map_add' := fun f f' => by funext g; simp only [map_add, Pi.add_apply]
      map_smul' := fun a f => by
        funext g
        simp only [map_smulₛₗ, Pi.smul_apply, hs, ← h, RingEquiv.symm_apply_apply, RingHom.id_apply] }
  have hrd : ∀ f g, rd f g = Λ g⁻¹ (θ (P.ext f g)) := fun _ _ => rfl
  have hm : ∀ a b z, Λ a (Λ b z) = Λ (a * b) z := fun a b z => by rw [map_mul]; rfl
  refine ⟨rd, fun f γ g => ?_, fun f k g => ?_, fun n f hf => ?_, fun f f' A hA h1 g => ?_, fun f c => ?_⟩
  · have := P.extMem_holds f γ g 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at this
    rw [hrd, hrd, this, hΛ, hm]
    congr 2
    group
  · have := P.extMem_holds f 1 g k
    simp only [one_mul, map_one, Module.End.one_apply] at this
    rw [hrd, hrd, this, hs, hm, map_smul]
    congr 3
    group
  · have h1 := linInd_of_basis σ P.extL S.basis P.extBij_holds.1 n f hf
    rw [Fintype.linearIndependent_iff] at h1 ⊢
    intro a ha i
    have h2 := h1 (fun i => io (a i)) (funext fun g => hinj ?_) i
    · simpa using h2
    have h3 := congrArg (fun F => Λ g (F g)) ha
    simp only [Finset.sum_apply, Pi.smul_apply, hrd, map_sum, map_smul, hm, mul_inv_cancel, map_one, Module.End.one_apply,
      Pi.zero_apply, map_zero] at h3
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, hs, RingEquiv.symm_apply_apply, Pi.zero_apply, map_zero]
    exact h3
  · rw [hrd, hA, dcOp, map_sum, map_sum]
    refine Finset.sum_congr rfl fun s hs' => ?_
    have e : Λ s⁻¹ = 1 := by
      have := map_mul Λ s⁻¹ s
      rw [h1 s hs', mul_one, inv_mul_cancel, map_one] at this
      exact this.symm
    rw [hrd, mul_inv_rev, map_mul, e, one_mul]
  · rw [hrd, P.ext_rep]

end GlobalTheory.FrameRead
