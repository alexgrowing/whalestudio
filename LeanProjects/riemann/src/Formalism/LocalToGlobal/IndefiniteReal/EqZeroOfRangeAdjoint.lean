import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem eq_zero_of_range_adjoint {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F) {u : E}
    (hu : u ∈ LinearMap.range (LinearMap.adjoint f)) (h0 : f u = 0) : u = 0 := by
  obtain ⟨w, rfl⟩ := hu
  have h : ⟪(LinearMap.adjoint f) w, (LinearMap.adjoint f) w⟫_ℂ = 0 := by
    rw [LinearMap.adjoint_inner_left, h0, inner_zero_right]
  exact inner_self_eq_zero.mp h

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

def uL (j : Bs.J) (t : Bs.Tup) : Fin ((lv (fc X.zs) b).dZ j t) → X.FLC j t :=
  fun k => X.jL j t (cr.toL X.zs b j t (Pi.single k 1))

theorem tC_eq (j : Bs.J) (t : Bs.Tup) (c : Fin ((lv (fc X.zs) b).dZ j t) → ℂ) :
    X.tC cr b j t c = X.θ' j t (lin (X.uL cr b j t) c) := by
  simp only [tC, uL, lin, Fintype.linearCombination_apply, map_sum, map_smul]

theorem jL_toL (j : Bs.J) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.jL j t (cr.toL X.zs b j t x) = lin (X.uL cr b j t) (cpt Bs.v0.embedding x) := by
  have hx : x = ∑ k, x k • (Pi.single k (1 : K) : Fin ((lv (fc X.zs) b).dZ j t) → K) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul, map_smulₛₗ, lin, Fintype.linearCombination_apply, cpt, uL]

theorem lin_mem {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} {v : Fin n → E} {S : Submodule ℂ E}
    (h : ∀ k, v k ∈ S) (c : Fin n → ℂ) : lin v c ∈ S := by
  simp only [lin, Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun k _ => S.smul_mem _ (h k)

theorem gram_uL (hI : X.IsoL cr b) (j : Bs.J) (t : Bs.Tup) :
    Matrix.gram ℂ (X.uL cr b j t) = ((X.nP b : ℝ) : ℂ) • metOf ((lv (fc X.zs) b).XT j t Bs.v0) := by
  ext k l
  rw [Matrix.gram_apply]
  simp only [uL]
  rw [hI j t (Pi.single k 1) (Pi.single l 1)]
  simp [Matrix.smul_apply, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, metOf, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem lin_uL_injective (hW : (lv (fc X.zs) b).WF) (hn : 0 < X.nP b) (hI : X.IsoL cr b) (j : Bs.J) (t : Bs.Tup) :
    Function.Injective (lin (X.uL cr b j t)) := by
  apply lin_injective
  apply Matrix.linearIndependent_of_posDef_gram
  rw [X.gram_uL cr b hI j t]
  exact (metOfSpec _ _ ((hW.XT_herm j t).1 Bs.v0)).1.smul (Complex.zero_lt_real.mpr hn)

end CxData

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs}

theorem cutLifts (cr : Crd A fc) (cv : CrdV A) (b : Bool) : X.CutLifts cr cv b := by
  intro hW hpos _hK hI hZ hV hR hDn hUp hA hP
  have hZk : ∀ j t k, X.uL cr b j t k ∈ LinearMap.range (LinearMap.adjoint (X.θ' j t)) :=
    fun j t k => hZ j t (Pi.single k 1)
  have hVk : ∀ j t k, X.uL cr b j t k ∈ X.goodPartComplexPoints cv b j t :=
    fun j t k => Submodule.subset_span ⟨_, hV j t (Pi.single k 1), rfl⟩
  have hinj : ∀ j t, Function.Injective (X.tC cr b j t) := by
    intro j t
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [tC_eq] at hc
    apply X.lin_uL_injective cr b hW (hpos.2.2 b) hI j t
    rw [map_zero]
    exact eq_zero_of_range_adjoint _ (lin_mem (hZk j t) c) hc
  have hle : ∀ j t, LinearMap.range (X.tC cr b j t) ≤ LinearMap.range (X.w0C b j) := by
    rintro j t _ ⟨c, rfl⟩
    rw [tC_eq]
    exact hDn j t (Submodule.mem_map_of_mem (lin_mem (hVk j t) c))
  have hspan : ∀ j t, Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dZ j t) → K =>
      X.jL j t (cr.toL X.zs b j t x)) ≤ LinearMap.range (lin (X.uL cr b j t)) := by
    intro j t
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨cpt Bs.v0.embedding x, (X.jL_toL cr b j t x).symm⟩
  refine ⟨fun j t => ⟨hinj j t, le_antisymm (hle j t) ?_⟩, ?_⟩
  · rw [← (hP j).2]
    refine iSup_le fun p => ?_
    intro w hw
    obtain ⟨hwp, hwr⟩ := Submodule.mem_inf.1 hw
    have h1 : LinearMap.adjoint (X.θ' j t) w ∈
        LinearMap.range (LinearMap.adjoint (X.θ' j t)) ⊓ X.goodPartComplexPoints cv b j t :=
      Submodule.mem_inf.2 ⟨⟨w, rfl⟩, hUp j t (Submodule.mem_map_of_mem hwr)⟩
    rw [← hR j t] at h1
    obtain ⟨c, hc⟩ := hspan j t h1
    have hlam := hA j t p w hw
    have hne : ((X.lam j t p Bs.v0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos.2.1 j t p Bs.v0).ne'
    refine ⟨((X.lam j t p Bs.v0 : ℝ) : ℂ)⁻¹ • c, ?_⟩
    rw [map_smul, tC_eq, hc, hlam, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · intro j t p x hx y
    have hx' := hx
    rw [tC_eq, ← jL_toL] at hx'
    rw [tC_eq, tC_eq, ← jL_toL, ← jL_toL]
    have hu : X.jL j t (cr.toL X.zs b j t x) ∈ LinearMap.range (LinearMap.adjoint (X.θ' j t)) := hZ j t x
    have hw : X.θ' j t (X.jL j t (cr.toL X.zs b j t x)) ∈ X.Wp j p ⊓ LinearMap.range (X.w0C b j) := by
      refine Submodule.mem_inf.2 ⟨hx', hle j t ⟨cpt Bs.v0.embedding x, ?_⟩⟩
      rw [tC_eq, jL_toL]
    have hA' := hA j t p _ hw
    have key : LinearMap.adjoint (X.θ' j t) (X.θ' j t (X.jL j t (cr.toL X.zs b j t x))) =
        ((X.lam j t p Bs.v0 : ℝ) : ℂ) • X.jL j t (cr.toL X.zs b j t x) := by
      have hm : LinearMap.adjoint (X.θ' j t) (X.θ' j t (X.jL j t (cr.toL X.zs b j t x))) -
          ((X.lam j t p Bs.v0 : ℝ) : ℂ) • X.jL j t (cr.toL X.zs b j t x) ∈
          LinearMap.range (LinearMap.adjoint (X.θ' j t)) :=
        Submodule.sub_mem _ ⟨_, rfl⟩ (Submodule.smul_mem _ _ hu)
      have h0 : X.θ' j t (LinearMap.adjoint (X.θ' j t) (X.θ' j t (X.jL j t (cr.toL X.zs b j t x))) -
          ((X.lam j t p Bs.v0 : ℝ) : ℂ) • X.jL j t (cr.toL X.zs b j t x)) = 0 := by
        rw [map_sub, map_smul, hA', sub_self]
      exact sub_eq_zero.1 (eq_zero_of_range_adjoint _ hm h0)
    rw [← LinearMap.adjoint_inner_left, key, inner_smul_left, hI j t x y, Complex.conj_ofReal]
    push_cast
    ring

end CxData

end Formalism.IndefR.Cx
