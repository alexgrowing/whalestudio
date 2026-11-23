import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2

open Module
open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.L2.Indef

theorem mem_range_adjoint_of_ker_stable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (Θ : E →ₗ[ℂ] F) (T T' : E →ₗ[ℂ] E) (hT' : T' = LinearMap.adjoint T)
    (hker : ∀ u, Θ u = 0 → Θ (T' u) = 0) {y : E} (hy : y ∈ LinearMap.range (LinearMap.adjoint Θ)) :
    T y ∈ LinearMap.range (LinearMap.adjoint Θ) := by
  obtain ⟨z, rfl⟩ := hy
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range (LinearMap.adjoint Θ)), Submodule.mem_orthogonal]
  intro v hv
  have hΘv : Θ v = 0 := by
    have h := (Submodule.mem_orthogonal _ _).1 hv (LinearMap.adjoint Θ (Θ v)) ⟨Θ v, rfl⟩
    rw [LinearMap.adjoint_inner_left] at h
    exact inner_self_eq_zero.1 h
  rw [← LinearMap.adjoint_inner_left, ← hT', LinearMap.adjoint_inner_right, hker v hΘv, inner_zero_left]

theorem semilin_comp_eq_constr {ι k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module ℂ W]
    {σ : k →+* ℂ} (b : Basis ι k V) (j : V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (b i))
    (hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun i => j (b i))) (f : V →ₗ[k] V) (x : V) :
    j (f x) = (Basis.mk hli hsp).constr ℂ (fun i => j (f (b i))) (j x) := by
  have h := b.ext (f₁ := j.comp f)
    (f₂ := ((Basis.mk hli hsp).constr ℂ (fun i => j (f (b i)))).comp j) (fun i => by
      simp only [LinearMap.comp_apply]
      rw [show j (b i) = Basis.mk hli hsp i from (Basis.mk_apply hli hsp i).symm, Basis.constr_basis])
  exact LinearMap.congr_fun h x

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem jR_opR (hR : X.KFormR) (t : Bs.Tup) (i : A.OpR t) (x : A.FR t) :
    X.jR t (A.opR t i x) = X.opC t i (X.jR t x) := by
  unfold opC
  rw [dif_pos (hR t)]
  exact semilin_comp_eq_constr _ (X.jR t) (hR t).1 (hR t).2.ge (A.opR t i) x

theorem jL_opL (hL : X.KFormL) (j : Bs.J) (t : Bs.Tup) (i : A.OpL j t) (x : A.FL j t) :
    X.jL j t (A.opL j t i x) = X.opLC j t i (X.jL j t x) := by
  unfold opLC
  rw [dif_pos (hL j t)]
  exact semilin_comp_eq_constr _ (X.jL j t) (hL j t).1 (hL j t).2.ge (A.opL j t i) x

theorem cutStable : X.CutStable := by
  intro hR hL hkR hkL haR haL
  unfold DefSub.Stable
  refine ⟨fun t i => ?_, fun j t i => ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    show X.jR t (A.opR t i x) ∈ LinearMap.range (LinearMap.adjoint (X.Θ t))
    rw [jR_opR X hR]
    obtain ⟨i', hi'⟩ := haR t i
    exact mem_range_adjoint_of_ker_stable (X.Θ t) (X.opC t i) (X.opC t i') hi'
      (fun u hu => hkR t i' u hu) (y := X.jR t x) hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    show X.jL j t (A.opL j t i x) ∈ LinearMap.range (LinearMap.adjoint (X.θ' j t))
    rw [jL_opL X hL]
    obtain ⟨i', hi'⟩ := haL j t i
    exact mem_range_adjoint_of_ker_stable (X.θ' j t) (X.opLC j t i) (X.opLC j t i') hi'
      (fun u hu => hkL j t i' u hu) (y := X.jL j t x) hx

end CxData

end Formalism.IndefR.Cx
