import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

noncomputable section

open PiTensorProduct Module
open scoped TensorProduct

namespace GlobalTheory.JacStages

section SigmaCurry

variable {α : Type} [DecidableEq α] {β : α → Type} [∀ a, DecidableEq (β a)]
  (M : (Σ a, β a) → Type) [∀ p, AddCommGroup (M p)] [∀ p, Module ℂ (M p)]

theorem tprod_tprod_update_sigma [DecidableEq (Σ a, β a)] (x : ∀ p, M p) (a₀ : α) (b₀ : β a₀)
    (v : M ⟨a₀, b₀⟩) :
    (fun a => tprod ℂ fun b => Function.update x ⟨a₀, b₀⟩ v ⟨a, b⟩) =
      Function.update (fun a => tprod ℂ fun b => x ⟨a, b⟩) a₀
        (tprod ℂ (Function.update (fun b => x ⟨a₀, b⟩) b₀ v)) := by
  funext a
  by_cases h : a = a₀
  · subst h
    rw [Function.update_self]
    congr 1
    funext b
    by_cases hb : b = b₀
    · subst hb
      simp
    · rw [Function.update_of_ne hb, Function.update_of_ne]
      intro h'
      exact hb (eq_of_heq (Sigma.mk.inj h').2)
  · rw [Function.update_of_ne h]
    congr 1
    funext b
    rw [Function.update_of_ne]
    intro h'
    exact h (congrArg Sigma.fst h')

def curryML : MultilinearMap ℂ M (⨂[ℂ] a, ⨂[ℂ] b, M ⟨a, b⟩) where
  toFun x := tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩
  map_update_add' x p v w := by
    obtain ⟨a₀, b₀⟩ := p
    simp only [tprod_tprod_update_sigma]
    rw [MultilinearMap.map_update_add, MultilinearMap.map_update_add]
  map_update_smul' x p c v := by
    obtain ⟨a₀, b₀⟩ := p
    simp only [tprod_tprod_update_sigma]
    rw [MultilinearMap.map_update_smul, MultilinearMap.map_update_smul]

theorem curryML_apply (x : ∀ p, M p) : curryML M x = tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := rfl

variable [Finite α] [∀ a, Finite (β a)]

def sigBasis : Basis (∀ p, Free.ChooseBasisIndex ℂ (M p)) ℂ (⨂[ℂ] p, M p) :=
  Basis.piTensorProduct fun p => Free.chooseBasis ℂ (M p)

def nestBasis : Basis (∀ a b, Free.ChooseBasisIndex ℂ (M ⟨a, b⟩)) ℂ (⨂[ℂ] a, ⨂[ℂ] b, M ⟨a, b⟩) :=
  Basis.piTensorProduct fun a => Basis.piTensorProduct fun b => Free.chooseBasis ℂ (M ⟨a, b⟩)

def sigmaCurry : (⨂[ℂ] p, M p) ≃ₗ[ℂ] ⨂[ℂ] a, ⨂[ℂ] b, M ⟨a, b⟩ :=
  (sigBasis M).equiv (nestBasis M) (Equiv.piCurry fun a b => Free.ChooseBasisIndex ℂ (M ⟨a, b⟩))

theorem sigmaCurry_eq_lift : (sigmaCurry M : (⨂[ℂ] p, M p) →ₗ[ℂ] _) = lift (curryML M) := by
  apply (sigBasis M).ext
  intro q
  rw [LinearEquiv.coe_coe, sigmaCurry, Basis.equiv_apply]
  simp only [sigBasis, nestBasis, Basis.piTensorProduct_apply, lift.tprod, curryML_apply]
  rfl

@[simp] theorem sigmaCurry_tprod (x : ∀ p, M p) :
    sigmaCurry M (tprod ℂ x) = tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by
  have h := LinearMap.congr_fun (sigmaCurry_eq_lift M) (tprod ℂ x)
  simpa [curryML_apply] using h

end SigmaCurry

section Flat

variable {s : ℕ} {t : Fin s → ℕ}

def flatTensorEquiv (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)] :
    (⨂[ℂ] c : Fin (∑ a, t a), Y (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) ≃ₗ[ℂ]
      ⨂[ℂ] a, ⨂[ℂ] b, Y a b :=
  (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv).symm.trans
    (sigmaCurry fun p : Σ a, Fin (t a) => Y p.1 p.2)

theorem flatTensorEquiv_reindex_tprod (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)]
    [∀ a b, Module ℂ (Y a b)] (x : ∀ p : Σ a, Fin (t a), Y p.1 p.2) :
    flatTensorEquiv Y (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv (tprod ℂ x)) =
      tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by
  rw [flatTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, sigmaCurry_tprod]

theorem flatTensorEquiv_tprod (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)]
    [∀ a b, Module ℂ (Y a b)] (x : ∀ p : Σ a, Fin (t a), Y p.1 p.2) :
    flatTensorEquiv Y (tprod ℂ fun c => x (finSigmaFinEquiv.symm c)) =
      tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by
  rw [← flatTensorEquiv_reindex_tprod, reindex_tprod]

theorem piTensor_flatHom_equiv : ∀ (s : ℕ) (t : Fin s → ℕ) (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)]
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ : ∀ a b, Representation ℂ (Γ a b) (Y a b)),
    Nonempty (Representation.Equiv ((piTensor fun c : Fin (∑ a, t a) =>
        ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).comp (flatHom Γ))
      (piTensor fun a => piTensor (ρ a))) := by
  intro s t Γ _ Y _ _ ρ
  refine ⟨Representation.Equiv.mk (flatTensorEquiv Y) fun g => ?_⟩
  have key : ∀ w : ⨂[ℂ] p : Σ a, Fin (t a), Y p.1 p.2,
      flatTensorEquiv Y (((piTensor fun c : Fin (∑ a, t a) =>
        ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).comp (flatHom Γ)) g
          (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv w)) =
        piTensor (fun a => piTensor (ρ a)) g
          (flatTensorEquiv Y (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv w)) := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      simp only [map_smul]
      congr 1
      rw [flatTensorEquiv_reindex_tprod, piTensor_tprod]
      simp only [piTensor_tprod]
      rw [reindex_tprod, MonoidHom.comp_apply, piTensor_tprod]
      exact flatTensorEquiv_tprod Y fun p => ρ p.1 p.2 (g p.1 p.2) (x p)
    | add w w' hw hw' =>
      simp only [map_add]
      rw [hw, hw']
  refine LinearMap.ext fun v => ?_
  obtain ⟨w, rfl⟩ := (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv).surjective v
  exact key w

end Flat

end GlobalTheory.JacStages
