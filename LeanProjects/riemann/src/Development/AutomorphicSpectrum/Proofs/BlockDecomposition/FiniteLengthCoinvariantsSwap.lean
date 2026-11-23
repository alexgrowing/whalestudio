import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen.Swap

section Abstract

variable {Γ G V V' : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem coinv_of_intertwine (τ : Representation ℂ (Γ × G) V) (τ' : Representation ℂ (Γ × G) V')
    (ψ ψ' : Γ →* ℂˣ) (T : V ≃ₗ[ℂ] V') (θ : Γ →* Γ) (θ' : G →* G)
    (hθ : Function.Surjective θ) (hθ' : Function.Surjective θ')
    (hT : ∀ γ g v, T (τ (γ, g) v) = τ' (θ γ, θ' g) (T v)) (hψ : ∀ γ, ψ' (θ γ) = ψ γ)
    (h : HasFiniteLength (coinv τ' ψ')) : HasFiniteLength (coinv τ ψ) := by
  have key : ∀ (γ : Γ) (v : V), T (τ (γ, 1) v - (ψ γ : ℂ) • v) =
      τ' (θ γ, 1) (T v) - (ψ' (θ γ) : ℂ) • T v := fun γ v => by
    rw [map_sub, map_smul, hT, map_one, hψ]
  have hrel : (twRel (τ.comp (MonoidHom.inl Γ G)) ψ).map (T : V →ₗ[ℂ] V') =
      twRel (τ'.comp (MonoidHom.inl Γ G)) ψ' := by
    unfold twRel
    rw [Submodule.map_span]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨γ, v, rfl⟩, rfl⟩
      exact ⟨θ γ, T v, key γ v⟩
    · rintro ⟨γ', v', rfl⟩
      obtain ⟨γ, rfl⟩ := hθ γ'
      refine ⟨_, ⟨γ, T.symm v', rfl⟩, ?_⟩
      have := key γ (T.symm v')
      rw [LinearEquiv.apply_symm_apply] at this
      exact this
  let E : (coinv τ ψ).Equiv ((coinv τ' ψ').comp θ' : Representation ℂ G _) :=
    Representation.Equiv.mk (Submodule.Quotient.equiv _ _ T hrel) fun g =>
      Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        show Submodule.Quotient.mk (T (τ (1, g) v)) = Submodule.Quotient.mk (τ' (1, θ' g) (T v))
        rw [hT, map_one])
  exact HasFiniteLength.of_equiv ((hasFiniteLength_comp_iff _ θ' hθ').2 h) E.symm

end Abstract

section Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def invT (n : Type) [Fintype n] [DecidableEq n] : GL n k →* GL n k where
  toFun g := ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul]; simp, by rw [← transpose_mul]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp [transpose_mul])

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem invT_invT (g : GL a k) : invT a (invT a g) = g := Units.ext (transpose_transpose _)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem invT_surjective : Function.Surjective (invT a : GL a k → GL a k) :=
  fun g => ⟨invT a g, invT_invT g⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_invT (g : GL a k) :
    GeneralLinearGroup.det (invT a g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  refine Units.ext ?_
  show ((g⁻¹).valᵀ).det = ((g⁻¹ : GL a k).val).det
  rw [det_transpose]

def trHomeo (a b : Type) : Matrix b a k ≃ₜ Matrix a b k where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

def trSB (a b : Type) : SB (Matrix b a k) ≃ₗ[ℂ] SB (Matrix a b k) where
  toFun Φ := ⟨fun y => Φ.1 yᵀ, Φ.2.1.comp_continuous (trHomeo b a).continuous,
    Φ.2.2.comp_homeomorph (trHomeo b a)⟩
  invFun Φ := ⟨fun y => Φ.1 yᵀ, Φ.2.1.comp_continuous (trHomeo a b).continuous,
    Φ.2.2.comp_homeomorph (trHomeo a b)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv Φ := Subtype.ext (funext fun y => congrArg Φ.1 (transpose_transpose y))
  right_inv Φ := Subtype.ext (funext fun y => congrArg Φ.1 (transpose_transpose y))

theorem omChar_swap (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) :
    omChar b a μ (invT b h, invT a g) = omChar a b μ (g, h) := by
  simp only [omChar, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
    detChar_apply, det_invT, MonoidHom.inv_apply, map_inv, neg_div, absPow_neg, inv_inv, mul_inv]
  exact mul_comm _ _

theorem trSB_omega (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (Φ : SB (Matrix b a k)) :
    trSB a b (omega a b μ (g, h) Φ) = omega b a μ (invT b h, invT a g) (trSB a b Φ) := by
  refine Subtype.ext (funext fun y => ?_)
  show (omChar a b μ (g, h) : ℂ) * Φ.1 (act yᵀ (g, h)) =
    (omChar b a μ (invT b h, invT a g) : ℂ) * Φ.1 (act y (invT b h, invT a g))ᵀ
  have e : act yᵀ (g, h) = (act y (invT b h, invT a g))ᵀ := by
    show (h⁻¹).val * yᵀ * g.val = (g.valᵀ * y * (h⁻¹).valᵀ)ᵀ
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [omChar_swap, e]

end Model

theorem coinv_swap_finiteLength : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ χ : kˣ →* ℂˣ), HasFiniteLength (coinv (omega b a μ⁻¹) (detChar b χ⁻¹)) → HasFiniteLength (coinv ((omega a b μ⁻¹).comp (MulEquiv.prodComm (M := GL b k) (N := GL a k)).toMonoidHom) (detChar b χ)) := by
  intro k _ _ _ _ a b _ _ _ _ μ χ h
  refine coinv_of_intertwine _ _ _ _ (trSB a b) (invT b) (invT a) invT_surjective invT_surjective
    (fun γ g v => trSB_omega μ⁻¹ g γ v) (fun γ => ?_) h
  simp [det_invT]

end GlobalTheory.CompanionTheory.ThetaGLLen.Swap
