import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned
  Formalism.L2.SG.EvalTOntoRep MeasureTheory
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowMult

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def contSub : Submodule ℂ (L2X X) where
  carrier := {f | ∃ φ, IsContRep X f φ}
  add_mem' := fun ⟨φ, hφ⟩ ⟨ψ, hψ⟩ => ⟨φ + ψ, contRep_add X hφ hψ⟩
  zero_mem' := ⟨0, contRep_zero X⟩
  smul_mem' := fun a _ ⟨φ, hφ⟩ => ⟨a • φ, contRep_smul X a hφ⟩

def repOn : contSub X →ₗ[ℂ] (X.B.I.GA → ℂ) where
  toFun f := f.2.choose
  map_add' f g := contRep_unique X (f + g).2.choose_spec (contRep_add X f.2.choose_spec g.2.choose_spec)
  map_smul' a f := contRep_unique X (a • f).2.choose_spec (contRep_smul X a f.2.choose_spec)

def contRepL : L2X X →ₗ[ℂ] (X.B.I.GA → ℂ) := (LinearMap.exists_extend (repOn X)).choose

theorem contRepL_spec {f : L2X X} {φ : X.B.I.GA → ℂ} (hf : IsContRep X f φ) : contRepL X f = φ := by
  have e := LinearMap.congr_fun (LinearMap.exists_extend (repOn X)).choose_spec ⟨f, φ, hf⟩
  have e' : contRepL X f = repOn X ⟨f, φ, hf⟩ := e
  rw [e']
  exact contRep_unique X (Exists.choose_spec (p := fun φ => IsContRep X f φ) _) hf

theorem eq_of_inner_tens {p q : X.B.Hs} (h : ∀ y, ⟪p, X.B.tens y⟫_ℂ = ⟪q, X.B.tens y⟫_ℂ) : p = q := by
  let f : X.B.Hs →L[ℂ] ℂ := innerSL ℂ (p - q)
  have hsp : (Submodule.span ℂ (Set.range X.B.tens) : Set X.B.Hs) ⊆ {z | f z = 0} := by
    refine (Submodule.span_le (p := LinearMap.ker (f : X.B.Hs →ₗ[ℂ] ℂ))).2 ?_
    rintro _ ⟨y, rfl⟩
    show ⟪p - q, X.B.tens y⟫_ℂ = 0
    rw [inner_sub_left, h y, sub_self]
  have hcl : closure (Submodule.span ℂ (Set.range X.B.tens) : Set X.B.Hs) ⊆ {z | f z = 0} :=
    closure_minimal hsp (isClosed_eq f.continuous continuous_const)
  rw [X.B.tens_spec.2.2.closure_eq] at hcl
  have h0 : f (p - q) = 0 := hcl (Set.mem_univ _)
  have : ⟪p - q, p - q⟫_ℂ = 0 := h0
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

theorem prod_update {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℂ (H i)] (x y : ∀ i, H i) (v : ι) (z : H v) :
    ∏ w, ⟪Function.update x v z w, y w⟫_ℂ = ⟪z, y v⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪x w, y w⟫_ℂ := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]

theorem tens_update_add [DecidableEq (NumberField.InfinitePlace X.B.I.F)] (x : ∀ v, X.B.H v)
    (v : NumberField.InfinitePlace X.B.I.F) (a b : X.B.H v) :
    X.B.tens (Function.update x v (a + b)) =
      X.B.tens (Function.update x v a) + X.B.tens (Function.update x v b) := by
  refine eq_of_inner_tens X fun y => ?_
  rw [inner_add_left, X.B.tens_spec.1, X.B.tens_spec.1, X.B.tens_spec.1, prod_update, prod_update, prod_update,
    inner_add_left, add_mul]

theorem tens_update_smul [DecidableEq (NumberField.InfinitePlace X.B.I.F)] (x : ∀ v, X.B.H v)
    (v : NumberField.InfinitePlace X.B.I.F) (a : ℂ) (b : X.B.H v) :
    X.B.tens (Function.update x v (a • b)) = a • X.B.tens (Function.update x v b) := by
  refine eq_of_inner_tens X fun y => ?_
  rw [inner_smul_left, X.B.tens_spec.1, X.B.tens_spec.1, prod_update, prod_update, inner_smul_left, mul_assoc]

variable {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S)

def vecC (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) : ∀ v, X.B.H v :=
  Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (u τ : M.H τ))

theorem piCongrLeft_update {α β : Type} [DecidableEq α] [DecidableEq β] (P : β → Type) (e : α ≃ β)
    (f : ∀ a, P (e a)) (a : α) (x : P (e a)) :
    Equiv.piCongrLeft P e (Function.update f a x) = Function.update (Equiv.piCongrLeft P e f) (e a) x := by
  apply (Equiv.piCongrLeft P e).symm.injective
  rw [Equiv.symm_apply_apply]
  funext a'
  rw [Equiv.piCongrLeft_symm_apply]
  by_cases ha : a' = a
  · subst ha
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne ha, Function.update_of_ne (e.injective.ne ha), Equiv.piCongrLeft_apply_apply]

theorem vecC_update [DecidableEq D.what₂.Tau] [DecidableEq (NumberField.InfinitePlace X.B.I.F)]
    (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) (τ : D.what₂.Tau) (w : M.sm τ) :
    vecC X M c (Function.update u τ w) = Function.update (vecC X M c u) (X.pl.symm τ) (c τ (w : M.H τ)) := by
  unfold vecC
  rw [← piCongrLeft_update]
  congr 1
  funext τ'
  exact Function.apply_update (fun i (s : M.sm i) => c i (s : M.H i)) u τ w τ'

theorem vecC_eq (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) (g : ∀ v, X.B.H v)
    (hg : ∀ τ, c τ (u τ : M.H τ) = g (X.pl.symm τ)) : vecC X M c u = g := by
  unfold vecC
  have : (fun τ => c τ (u τ : M.H τ)) = (Equiv.piCongrLeft X.B.H X.pl.symm).symm g := by
    funext τ
    rw [Equiv.piCongrLeft_symm_apply, hg τ]
  rw [this, Equiv.apply_symm_apply]

def conjMap (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (A : X.B.Hs →L[ℂ] L2X X)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) : MMap M where
  toFun u := fun y => star (contRepL X (A (X.B.tens (vecC X M c u))) (iotaX X h (y * t⁻¹)))
  map_update_add' u τ a b := by
    classical
    funext y
    simp only [vecC_update, Submodule.coe_add, map_add, tens_update_add, Pi.add_apply, star_add]
  map_update_smul' u τ a b := by
    classical
    funext y
    simp only [vecC_update, Submodule.coe_smul, LinearIsometryEquiv.map_smulₛₗ, tens_update_smul, map_smul,
      Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply, star_star]

theorem conjMap_apply (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (A : X.B.Hs →L[ℂ] L2X X)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (u : M.Vec) (y : GA D (D.sp.Y 0)) :
    conjMap X M c A h t u y = star (contRepL X (A (X.B.tens (vecC X M c u))) (iotaX X h (y * t⁻¹))) := rfl

end GlobalTheory.ConjRowMult

end
