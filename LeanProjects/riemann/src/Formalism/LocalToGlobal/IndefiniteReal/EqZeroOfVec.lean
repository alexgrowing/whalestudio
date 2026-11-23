import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.SchurOrthogonalityAlt
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def SobOrbitDense (M : DSModel V S) : Prop :=
  ∀ τ (v : M.H τ), v ∈ M.sm τ → v ≠ 0 → ∀ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ →
    (∀ g : Gt V τ, ℓ (M.rep τ (gm g) v) = 0) → ∀ w ∈ M.sm τ, ℓ w = 0

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

open Classical in

structure EqCont (M : DSModel V S) (T : MMap M) : Prop where
  equiv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)
  cont : ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

variable {θ}

open Classical in

theorem eqCont_of_mem {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (hT : T ∈ Mult θ M J χ) : EqCont θ M T := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact ⟨hT.equiv, hT.cont⟩
  | zero =>
    refine ⟨fun τ g _ v w _ => ?_, fun τ v x => ⟨0, sobCont_zero, fun w => ?_⟩⟩
    · rw [MultilinearMap.zero_apply, MultilinearMap.zero_apply]; rfl
    · simp
  | add T T' _ _ h h' =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.add_apply, MultilinearMap.add_apply, h.equiv τ g hg v w hw, h'.equiv τ g hg v w hw]; rfl
    · obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
      obtain ⟨ℓ', hℓ', e'⟩ := h'.cont τ v x
      exact ⟨ℓ + ℓ', sobCont_add hℓ hℓ', fun w => by
        rw [LinearMap.add_apply, e, e', MultilinearMap.add_apply, Pi.add_apply]⟩
  | smul a T _ h =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.smul_apply, MultilinearMap.smul_apply, h.equiv τ g hg v w hw]; rfl
    · obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
      exact ⟨a • ℓ, sobCont_smul a hℓ, fun w => by
        rw [LinearMap.smul_apply, e, MultilinearMap.smul_apply, Pi.smul_apply]⟩

open Classical in

theorem place_zero {M : DSModel V S} (hS : SobOrbitDense M) {T : MMap M} (hT : EqCont θ M T) (τ : D.what₂.Tau)
    (v : M.Vec) (hv : (v τ : M.H τ) ≠ 0) (h0 : T v = 0) (w : M.sm τ) : T (Function.update v τ w) = 0 := by
  funext x
  obtain ⟨ℓ, hℓ, e⟩ := hT.cont τ v x
  have horb : ∀ g : Gt V τ, ℓ (M.rep τ (gm g) (v τ : M.H τ)) = 0 := by
    intro g
    have hm : M.rep τ (gm g) (v τ : M.H τ) ∈ M.sm τ := sm_stable M τ g (v τ).2
    have e1 := e ⟨M.rep τ (gm g) (v τ : M.H τ), hm⟩
    rw [hT.equiv τ (gm g) (gm_mem g) v ⟨M.rep τ (gm g) (v τ : M.H τ), hm⟩ rfl, h0] at e1
    exact e1
  have := hS τ (v τ : M.H τ) (v τ).2 hv ℓ hℓ horb (w : M.H τ) w.2
  rw [← e w, this]
  rfl

open Classical in

theorem eq_zero_of_vec {M : DSModel V S} (hS : SobOrbitDense M) {T : MMap M} (hT : EqCont θ M T) (v : M.Vec)
    (hv : ∀ τ, (v τ : M.H τ) ≠ 0) (h0 : T v = 0) : T = 0 := by
  have key : ∀ s : Finset D.what₂.Tau, ∀ u : M.Vec, T (s.piecewise u v) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro u; simpa using h0
    | insert a s ha ih =>
      intro u
      have hva : ((s.piecewise u v) a : M.H a) ≠ 0 := by
        rw [Finset.piecewise_eq_of_notMem _ _ _ ha]; exact hv a
      have := place_zero hS hT a (s.piecewise u v) hva (ih u) (u a)
      rw [Finset.piecewise_insert]
      exact this
  ext u
  have := key Finset.univ u
  rw [Finset.piecewise_univ] at this
  rw [this]
  rfl

variable (θ) in
open Classical in

theorem resInjVec (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (hS : SobOrbitDense M) :
    ResInjVec M (Mult θ M J χ) := by
  intro T hT v hv h0
  exact eq_zero_of_vec hS (eqCont_of_mem hT) v hv h0

end Formalism.IndefR.AutomorphicEvaluation

end
