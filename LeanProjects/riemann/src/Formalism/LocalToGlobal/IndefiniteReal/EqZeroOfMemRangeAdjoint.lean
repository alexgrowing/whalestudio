import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem eq_zero_of_mem_range_adjoint {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) {w : E}
    (hw : w ∈ LinearMap.range (LinearMap.adjoint T)) (h : T w = 0) : w = 0 := by
  obtain ⟨z, rfl⟩ := hw
  have : ⟪LinearMap.adjoint T z, LinearMap.adjoint T z⟫_ℂ = 0 := by
    rw [LinearMap.adjoint_inner_left, h, inner_zero_right]
  exact inner_self_eq_zero.1 this

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

def uQ (t : Bs.Tup) : Fin ((lv (fc X.zs) b).dQ t) → X.FC t :=
  fun k => X.jR t (cr.toR X.zs b t (Pi.single k 1))

theorem iC_eq_comp (t : Bs.Tup) (c : Fin ((lv (fc X.zs) b).dQ t) → ℂ) :
    X.iC cr b t c = X.Θ t (lin (X.uQ cr b t) c) := by
  simp only [iC, uQ, lin_apply, map_sum, map_smul]

theorem lin_uQ_cpt (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    lin (X.uQ cr b t) (cpt Bs.v0.embedding x) = X.jR t (cr.toR X.zs b t x) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin ((lv (fc X.zs) b).dQ t) → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, lin_apply, uQ, cpt]

theorem gram_uQ (hIso : X.IsoR cr b) (t : Bs.Tup) :
    Matrix.gram ℂ (X.uQ cr b t) = ((X.nP b : ℝ) : ℂ) • metOf ((lv (fc X.zs) b).XQ t Bs.v0) := by
  have hs : ∀ i, (fun j => Bs.v0.embedding ((Pi.single i (1 : K) : Fin ((lv (fc X.zs) b).dQ t) → K) j)) =
      (Pi.single i 1 : Fin ((lv (fc X.zs) b).dQ t) → ℂ) := by
    intro i; funext j; by_cases h : j = i <;> simp [h]
  ext i k
  rw [Matrix.gram_apply, uQ, uQ, hIso t, Formalism.L2.DIV.majAt_eq, hs, hs, Matrix.smul_apply, smul_eq_mul]
  congr 1
  simp [Matrix.mulVec_single, dotProduct, Pi.single_apply]

theorem lin_uQ_injective (hW : (lv (fc X.zs) b).WF) (hn : 0 < X.nP b) (hIso : X.IsoR cr b) (t : Bs.Tup) :
    Function.Injective (lin (X.uQ cr b t)) := by
  refine lin_injective (Matrix.linearIndependent_of_posDef_gram ?_)
  rw [X.gram_uQ cr b hIso t]
  exact (metOfSpec _ _ (hW.XQ_quot t Bs.v0).1).1.smul (Complex.zero_lt_real.mpr hn)

end CxData

open CxData in

theorem cutRows {Bs : DefBase K} {A : DefAmb Bs} {X : CxData A} {fc : DefSub A → DefFace Bs} (cr : Crd A fc)
    (cv : CrdV A) (b : Bool) : X.CutRows cr cv b := by
  intro hW hpos hIso hZ hV0' hRat hDn hUp hB hParts
  have hV0 : ∀ t x, X.jR t (cr.toR X.zs b t x) ∈ X.V0C cv b t :=
    fun t x => Submodule.subset_span ⟨_, hV0' t x, rfl⟩
  have hadj : ∀ t c, lin (X.uQ cr b t) c ∈ LinearMap.range (LinearMap.adjoint (X.Θ t)) := by
    intro t c
    rw [lin_apply]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hZ t _)
  have hv0 : ∀ t c, lin (X.uQ cr b t) c ∈ X.V0C cv b t := by
    intro t c
    rw [lin_apply]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hV0 t _)
  have hinj : ∀ t, Function.Injective (X.iC cr b t) := by
    intro t c c' h
    apply X.lin_uQ_injective cr b hW (hpos.2.2 b) hIso t
    rw [← sub_eq_zero, ← map_sub]
    refine eq_zero_of_mem_range_adjoint (X.Θ t) ?_ ?_
    · rw [map_sub]; exact sub_mem (hadj t c) (hadj t c')
    · rw [map_sub, map_sub, ← X.iC_eq_comp cr b, ← X.iC_eq_comp cr b, h, sub_self]
  have hrange : ∀ t, LinearMap.range (X.iC cr b t) = X.EEl b := by
    intro t
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      rw [X.iC_eq_comp cr b]
      exact hDn t ⟨_, hv0 t c, rfl⟩
    · rw [← hParts.2]
      refine iSup_le fun p => ?_
      intro e he
      have hc : (0 : ℝ) < X.κ Bs.v0 * ∏ j, X.lam j t p Bs.v0 :=
        mul_pos (hpos.1 _) (Finset.prod_pos fun j _ => hpos.2.1 j t p Bs.v0)
      have h1 : LinearMap.adjoint (X.Θ t) e ∈ LinearMap.range (LinearMap.adjoint (X.Θ t)) ⊓ X.V0C cv b t :=
        ⟨⟨e, rfl⟩, hUp t ⟨e, he.2, rfl⟩⟩
      rw [← hRat t] at h1
      have h2 : Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dQ t) → K => X.jR t (cr.toR X.zs b t x)) ≤
          LinearMap.range (lin (X.uQ cr b t)) := by
        rw [Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        exact ⟨cpt Bs.v0.embedding x, X.lin_uQ_cpt cr b t x⟩
      obtain ⟨c', hc'⟩ := h2 h1
      refine ⟨(((X.κ Bs.v0 * ∏ j, X.lam j t p Bs.v0 : ℝ) : ℂ))⁻¹ • c', ?_⟩
      have hc0 : (((X.κ Bs.v0 * ∏ j, X.lam j t p Bs.v0 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hc.ne'
      rw [X.iC_eq_comp cr b, map_smul, map_smul, hc', hB t p e he, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨⟨hinj Bs.μ0, fun t => ⟨hinj t, by rw [hrange, hrange]⟩, hrange Bs.μ0⟩, ?_⟩
  intro t p x hx y
  rw [X.iC_eq_comp cr b, X.lin_uQ_cpt cr b] at hx ⊢
  rw [X.iC_eq_comp cr b, X.lin_uQ_cpt cr b]
  have hEl : X.Θ t (X.jR t (cr.toR X.zs b t x)) ∈ X.EEl b := hDn t ⟨_, hV0 t x, rfl⟩
  have hBB := hB t p _ ⟨hx, hEl⟩
  have hw : LinearMap.adjoint (X.Θ t) (X.Θ t (X.jR t (cr.toR X.zs b t x))) =
      (((X.κ Bs.v0 * ∏ j, X.lam j t p Bs.v0 : ℝ) : ℂ)) • X.jR t (cr.toR X.zs b t x) := by
    rw [← sub_eq_zero]
    refine eq_zero_of_mem_range_adjoint (X.Θ t) (sub_mem ⟨_, rfl⟩ (Submodule.smul_mem _ _ (hZ t x))) ?_
    rw [map_sub, map_smul, hBB, sub_self]
  rw [← LinearMap.adjoint_inner_left, hw, inner_smul_left, hIso t x y, Complex.conj_ofReal]
  push_cast
  ring

end Formalism.IndefR.Cx
