import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocFlat.CQLast

open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem eq_zero_of_hat_eq_zero (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) {n : Type} [Fintype n] [DecidableEq n] {f : (n → k) → ℂ} (hf : f ∈ SB (n → k))
    (h0 : ∀ η, GlobalTheory.StepData.hat ψ ν (-1) f η = 0) (a : n → k) : f a = 0 := by
  classical
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨c, hc⟩ := (GlobalTheory.SplitWeil.conductor_exists k).1 ψ hψ hne
  set μ : Measure (n → k) := Measure.pi fun _ => ν with hμ
  have hF : ∀ y, ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0 := by
    intro y
    have h1 := h0 (-y)
    simp only [GlobalTheory.StepData.hat] at h1
    rw [← h1]
    congr 1
    funext x
    rw [neg_dotProduct, neg_one_mul, neg_neg, dotProduct_comm]
  set g : (n → k) → ℂ := fun x => f (x + a) with hgdef
  have hg : g ∈ SB (n → k) :=
    ⟨hf.1.comp_continuous (continuous_add_const a), hf.2.comp_homeomorph (Homeomorph.addRight a)⟩
  have hpsi : ∀ u v : k, (ψ (u + v) : ℂ) = ψ u * ψ v := fun u v => by
    rw [AddChar.map_add_eq_mul, Circle.coe_mul]
  have hpsi' : ∀ u : k, (ψ (-u) : ℂ) * ψ u = 1 := fun u => by
    rw [← hpsi, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
  have hG : ∀ y, ∫ x, g x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0 := by
    intro y
    have e : ∀ x, g x * (ψ (x ⬝ᵥ y) : ℂ) = (ψ (-(a ⬝ᵥ y)) : ℂ) * (f (x + a) * ψ ((x + a) ⬝ᵥ y)) := by
      intro x
      rw [add_dotProduct, hpsi, hgdef]
      linear_combination (f (x + a) * (ψ (x ⬝ᵥ y) : ℂ)) * (hpsi' (a ⬝ᵥ y)).symm
    simp_rw [e]
    rw [integral_const_mul, integral_add_right_eq_self (fun x => f x * (ψ (x ⬝ᵥ y) : ℂ)) a, hF, mul_zero]
  obtain ⟨s, hs⟩ := FourierPi.fourier_inversion_pi μ hc hg
  simp only [hG, integral_zero] at hs
  have hpos : ∀ r : kˣ, 0 < μ.real (FourierPi.box n r) := by
    intro r
    refine ENNReal.toReal_pos ((FourierPi.isOpen_box r).measure_pos μ ⟨0, ?_⟩).ne'
      (FourierPi.isCompact_box r).measure_lt_top.ne
    simp [FourierPi.box, cball]
  have h2 : g 0 = 0 := by
    rcases mul_eq_zero.1 hs.symm with h | h
    · exfalso
      have := mul_pos (hpos s) (hpos (c * s⁻¹))
      exact this.ne' (by exact_mod_cast h)
    · exact h
  simpa [hgdef] using h2

def withLast {n n' : Type} (x₀ : Matrix n n' k) (y : n → k) : Matrix n (n' ⊕ Unit) k :=
  fromCols x₀ (Matrix.of fun r (_ : Unit) => y r)

theorem withLast_toCols {n n' : Type} (x : Matrix n (n' ⊕ Unit) k) :
    withLast x.toCols₁ (fun r => x r (Sum.inr ())) = x := by
  ext r (j | u)
  · rfl
  · cases u; rfl

theorem continuous_withLast {n n' : Type} (x₀ : Matrix n n' k) : Continuous (withLast x₀) := by
  refine continuous_matrix fun i j => ?_
  rcases j with a | u
  · simp only [withLast, Matrix.fromCols_apply_inl]; exact continuous_const
  · simp only [withLast, Matrix.fromCols_apply_inr, Matrix.of_apply]; exact continuous_apply i

theorem slice_mem_SB {n n' : Type} [Fintype n] [Fintype n'] {Ψ : Matrix n (n' ⊕ Unit) k → ℂ}
    (hΨ : Ψ ∈ SB (Matrix n (n' ⊕ Unit) k)) (x₀ : Matrix n n' k) :
    (fun y : n → k => Ψ (withLast x₀ y)) ∈ SB (n → k) := by
  have := GlobalTheory.SplitWeil.t2Space k
  have hcl : Topology.IsClosedEmbedding (withLast x₀) :=
    Function.LeftInverse.isClosedEmbedding (f := fun x : Matrix n (n' ⊕ Unit) k => fun r => x r (Sum.inr ()))
      (fun y => rfl) (by fun_prop) (continuous_withLast x₀)
  exact ⟨hΨ.1.comp_continuous (continuous_withLast x₀), hΨ.2.comp_isClosedEmbedding hcl⟩

def partialHat (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ) (n n' : Type)
    [Fintype n] [Fintype n'] :
    SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (Matrix n n' k × (n → k) → ℂ) where
  toFun Ψ p := GlobalTheory.StepData.hat ψ ν (-1) (fun y => Ψ.1 (withLast p.1 y)) p.2
  map_add' Ψ Ψ' := by
    funext p
    simp only [GlobalTheory.StepData.hat, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (GlobalTheory.StepData.integrable_hat ψ ν (-1) hψ (slice_mem_SB Ψ.2 p.1) p.2)
      (GlobalTheory.StepData.integrable_hat ψ ν (-1) hψ (slice_mem_SB Ψ'.2 p.1) p.2)
  map_smul' a Ψ := by
    funext p
    simp only [GlobalTheory.StepData.hat, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact integral_const_mul a _

theorem partialHat_injective (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] :
    Function.Injective (partialHat ν ψ hψ n n') := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Ψ h
  ext x
  have h1 := eq_zero_of_hat_eq_zero ν ψ hψ hne (slice_mem_SB Ψ.2 x.toCols₁)
    (fun η => congrFun h (x.toCols₁, η)) (fun r => x r (Sum.inr ()))
  simpa [withLast_toCols] using h1

def coupleBil (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ) (n n' Z : Type)
    [Fintype n] [Fintype n'] :
    SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (Matrix n n' k × Matrix (Z ⊕ Unit) n k → ℂ) :=
  LinearMap.mk₂ ℂ (fun g Ψ q => g.1 q.2.toRows₁ * partialHat ν ψ hψ n n' Ψ (q.1, q.2 (Sum.inr ())))
    (fun g g' Ψ => by funext q; simp [add_mul])
    (fun a g Ψ => by funext q; simp [mul_assoc])
    (fun g Ψ Ψ' => by funext q; simp [mul_add])
    (fun a g Ψ => by funext q; simp; ring)

theorem coupleBil_injective (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] :
    Function.Injective (TensorProduct.lift (coupleBil ν ψ hψ n n' Z)) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  let b := Module.Free.chooseBasis ℂ (SB (Matrix Z n k))
  set c := TensorProduct.equivFinsuppOfBasisLeft b t with hc
  have ht' : t = c.sum fun i m => b i ⊗ₜ m := by
    rw [hc, ← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hm : ∀ (x₀ : Matrix n n' k) (η : n → k) (x : Matrix Z n k),
      ∑ i ∈ c.support, (b i).1 x * partialHat ν ψ hψ n n' (c i) (x₀, η) = 0 := by
    intro x₀ η x
    have hrow : (fromRows x (Matrix.of fun (_ : Unit) r => η r)) (Sum.inr ()) = η := by
      funext r; simp
    have := congrFun ht (x₀, fromRows x (Matrix.of fun (_ : Unit) r => η r))
    simp only [ht', Finsupp.sum, map_sum, TensorProduct.lift.tmul] at this
    simpa [coupleBil, Finset.sum_apply, hrow] using this
  have hzero : c = 0 := by
    ext i : 1
    by_cases hi : i ∈ c.support
    · have hP : partialHat ν ψ hψ n n' (c i) = partialHat ν ψ hψ n n' 0 := by
        rw [map_zero]
        funext p
        have hli := (linearIndependent_iff'.mp b.linearIndependent) c.support
          (fun j => partialHat ν ψ hψ n n' (c j) p)
          (by
            ext x
            simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
              ZeroMemClass.coe_zero, Pi.zero_apply]
            rw [← hm p.1 p.2 x]
            exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)) i hi
        simpa using hli
      simpa using partialHat_injective ν ψ hψ hne n n' hP
    · simp [Finsupp.notMem_support_iff.mp hi]
  rw [ht', hzero]
  simp

theorem exists_pair_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype Z] [DecidableEq Z] (M : Type) [AddCommGroup M] [Module ℂ M] (Bl : SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M), ∃ Λ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] M, (∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k)) (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), (∀ q, Ξ.1 q = Ψ₂.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) (q.2 (Sum.inr ()))) → Λ Ξ = Bl Ψ₂ Ψ₁) ∧ ∀ (Ξ₁ : SB (Matrix n n' k)) (a : SB (Matrix Z n k)) (c : SB (Matrix n Unit k)) (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), (∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → (∀ q, Ξ.1 q = Ξ₁.1 q.1 * (a.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (q.2 (Sum.inr ())))) → Λ Ξ = Bl a Ψ₁ := by
  intro k _ _ _ _ _ _ ν hν ψk hψ hne n n' Z _ _ _ _ _ _ M _ _ Bl
  classical
  set T := TensorProduct.lift (coupleBil ν ψk hψ n n' Z) with hT
  have hinj := coupleBil_injective ν ψk hψ hne n n' Z
  let eT := LinearEquiv.ofInjective T hinj
  let W : Submodule ℂ (SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)) :=
    (LinearMap.range T).comap (SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)).subtype
  let res : W →ₗ[ℂ] LinearMap.range T :=
    (SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)).subtype.restrict (fun x hx => hx)
  let Λ₀ : W →ₗ[ℂ] M := (TensorProduct.lift Bl).comp (eT.symm.toLinearMap.comp res)
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend Λ₀
  have key : ∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k))
      (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), Ξ.1 = T (Ψ₂ ⊗ₜ Ψ₁) → Λ Ξ = Bl Ψ₂ Ψ₁ := by
    intro Ψ₁ Ψ₂ Ξ hΞ
    have hmem : Ξ ∈ W := ⟨Ψ₂ ⊗ₜ Ψ₁, hΞ.symm⟩
    have h1 := LinearMap.congr_fun hΛ ⟨Ξ, hmem⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
    rw [h1]
    have h2 : res ⟨Ξ, hmem⟩ = eT (Ψ₂ ⊗ₜ Ψ₁) := Subtype.ext (by
      rw [LinearEquiv.ofInjective_apply]
      exact hΞ)
    simp only [Λ₀, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h2, LinearEquiv.symm_apply_apply,
      TensorProduct.lift.tmul]
  refine ⟨Λ, fun Ψ₁ Ψ₂ Ξ h => key Ψ₁ Ψ₂ Ξ (funext fun q => ?_),
    fun Ξ₁ a c Ψ₁ Ξ h1 h2 => key Ψ₁ a Ξ (funext fun q => ?_)⟩
  · rw [h q, hT, TensorProduct.lift.tmul]
    rfl
  · rw [h2 q, hT, TensorProduct.lift.tmul]
    have e : (fun y => Ψ₁.1 (withLast q.1 y)) = fun y => Ξ₁.1 q.1 * c.1 (Matrix.of fun r (_ : Unit) => y r) := by
      funext y
      rw [h1]
      rfl
    change _ = a.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (withLast q.1 y)) (q.2 (Sum.inr ()))
    rw [e]
    simp only [GlobalTheory.StepData.hat, mul_assoc]
    rw [integral_const_mul]
    ring

end GlobalTheory.LocFlat.CQLast
