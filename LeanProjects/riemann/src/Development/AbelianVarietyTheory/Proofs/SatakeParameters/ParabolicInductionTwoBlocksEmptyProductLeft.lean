import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.ProdReorder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ind₂_line_left {r : ℕ} (h : 0 + r = r) {M V : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin 0) k) M) (κ : M ≃ₗ[ℂ] ℂ)
    (π : Representation ℂ (GL (Fin r) k) V) (hπ : IsSmooth π) :
    Nonempty ((ind₂ (stdSum h) (extTensor σ π)).Equiv π) := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  have hE : ∀ g w, σ g w = w := fun g w => by rw [Subsingleton.elim g 1, map_one]; rfl
  let L : V ≃ₗ[ℂ] M ⊗[ℂ] V :=
    (TensorProduct.lid ℂ V).symm ≪≫ₗ TensorProduct.congr κ.symm (LinearEquiv.refl ℂ V)
  let u := κ.symm 1
  have hL : ∀ v, L v = u ⊗ₜ[ℂ] v := fun v => by simp [L, u]
  have hs : ∀ i : Fin r, stdSum h (Sum.inr i) = i := fun i => Fin.ext (by simp)
  have hl : ∀ p : parab k (two (stdSum h)), (leviProj k (two (stdSum h)) p true : GL (Fin r) k) = p :=
    fun p => by
      ext i j
      rw [leviProj_apply, two_true, two_true, hs, hs]
  have hd : ∀ p : parab k (two (stdSum h)),
      deltaHalf k (Two (Fin 0) (Fin r)) (leviProj k (two (stdSum h)) p) = 1 := fun p => by
    have : leviProj k (two (stdSum h)) p =
        leviTwo k _ _ ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k (two (stdSum h)) p)) :=
      ((leviTwo k _ _).apply_symm_apply _).symm
    rw [this, deltaHalf_two,
      Subsingleton.elim ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k (two (stdSum h)) p)).1 1]
    simp
  have hP : ∀ g : GL (Fin r) k, g ∈ parab k (two (stdSum h)) := fun g =>
    (mem_parab_two k).2 fun j i => i.elim0
  have law : ∀ (p : parab k (two (stdSum h))) v,
      (deltaHalf k (Two (Fin 0) (Fin r)) (leviProj k (two (stdSum h)) p) : ℂ) •
        (extTensor σ π) ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k (two (stdSum h)) p)) (L v) =
          L (π p v) := fun p v => by
    rw [hd, Units.val_one, one_smul, hL, hL, extTensor_tmul, hE]
    congr 1
    exact congrArg (fun g => π g v) (hl p)
  let f : π.IntertwiningMap (ind₂ (stdSum h) (extTensor σ π)) :=
    { toFun := fun v => ⟨⟨fun x => L (π x v), fun p x => by
          show L (π (↑p * x) v) = (deltaHalf k _ (leviProj k _ p) : ℂ) •
            (extTensor σ π) ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k _ p)) (L (π x v))
          rw [law, map_mul, Module.End.mul_apply]⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg => by
          have hg' : π g v = v := hg
          refine Subtype.ext (funext fun x => ?_)
          show L (π (x * g) v) = L (π x v)
          rw [map_mul, Module.End.mul_apply, hg'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x (v + w)) = L (π x v) + L (π x w)
        rw [map_add, map_add]))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x ((c : ℂ) • v)) = (c : ℂ) • L (π x v)
        rw [map_smul, map_smul]))
      isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x (π g v)) = L (π (x * g) v)
        rw [map_mul, Module.End.mul_apply])) }
  have hb : Function.Bijective f := by
    refine ⟨fun v w hvw => ?_, fun φ => ⟨L.symm (φ.1.1 1), ?_⟩⟩
    · have h1 : L (π 1 v) = L (π 1 w) := congrArg (fun φ => φ.1.1 1) hvw
      rw [map_one, Module.End.one_apply, Module.End.one_apply] at h1
      exact L.injective h1
    · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
      have h1 := φ.1.2 ⟨x, hP x⟩ 1
      rw [mul_one] at h1
      refine (law ⟨x, hP x⟩ _).symm.trans ?_
      rw [L.apply_symm_apply]
      exact h1.symm
  exact ⟨(GlobalTheory.LocGL.equivOfBijective f hb).symm⟩

variable (k) in

theorem ind₂_unit_left (r t : ℕ) (h : t + r = r) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin r) k) V) (hπ : IsSmooth π) (d : Fin 0 → ℕ) (X : Fin 0 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (e : (Σ a, Fin (d a)) ≃ Fin t) :
    Nonempty ((ind₂ (stdSum h) (extTensor (multiProd e τ) π)).Equiv π) := by
  have ht : t = 0 := by omega
  subst ht
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  let ev1 : IndSp e (piTensor τ) →ₗ[ℂ] ⨂[ℂ] i, X i :=
    { toFun := fun f => f.1.1 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let κ : IndSp e (piTensor τ) ≃ₗ[ℂ] ℂ := (LinearEquiv.ofBijective ev1 ⟨fun f g hfg =>
    Subtype.ext (Subtype.ext (funext fun x => by rw [Subsingleton.elim x 1]; exact hfg)), fun v =>
    ⟨⟨⟨fun _ => v, fun p _ => by rw [Subsingleton.elim p 1, map_one]; rfl⟩,
      GlobalTheory.SmGL.MultiIrr.mem_smooth_of_eventually _ (.of_forall fun _ _ => rfl)⟩, rfl⟩⟩).trans
    (PiTensorProduct.isEmptyEquiv _)
  exact ind₂_line_left h (multiProd e τ) κ π hπ

end GlobalTheory.ProdReorder
