import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

section
variable {K G V W : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def transportRep (ρ : Representation K G V) (e : V ≃ₗ[K] W) : Representation K G W where
  toFun g := e.conj (ρ g)
  map_one' := by ext w; simp
  map_mul' a b := by ext w; simp

theorem transportRep_apply (ρ : Representation K G V) (e : V ≃ₗ[K] W) (g : G) (w : W) :
    transportRep ρ e g w = e (ρ g (e.symm w)) := rfl

theorem character_transportRep [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K G V) (e : V ≃ₗ[K] W) (g : G) :
    (transportRep ρ e).character g = ρ.character g :=
  LinearMap.trace_conj' (ρ g) e

def transportSubOrderIso (ρ : Representation K G V) (e : V ≃ₗ[K] W) :
    Subrepresentation (transportRep ρ e) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule.comap e.toLinearMap, fun g v hv => by
    have := S.apply_mem_toSubmodule g (v := e v) hv
    simpa [transportRep_apply] using this⟩
  invFun S := ⟨S.toSubmodule.comap e.symm.toLinearMap, fun g w hw => by
    have := S.apply_mem_toSubmodule g (v := e.symm w) hw
    simpa [transportRep_apply] using this⟩
  left_inv S := by ext w; simp
  right_inv S := by ext v; simp
  map_rel_iff' {S T} := by
    constructor
    · intro h w hw
      have h1 : e.symm w ∈ S.toSubmodule.comap e.toLinearMap := by
        show e (e.symm w) ∈ S.toSubmodule
        rw [e.apply_symm_apply]; exact hw
      have h2 : e (e.symm w) ∈ T.toSubmodule := h h1
      rw [e.apply_symm_apply] at h2
      exact h2
    · intro h v hv
      exact h (show e v ∈ S from hv)

theorem isIrreducible_transportRep (ρ : Representation K G V) (e : V ≃ₗ[K] W)
    (h : ρ.IsIrreducible) : (transportRep ρ e).IsIrreducible := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact (transportSubOrderIso ρ e).isSimpleOrder
end

theorem _root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type)
      [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V),
      _root_.GlobalTheory.BI.IsChar K L (fun g => algebraMap K L (ρ.character g)) ∧
        (ρ.IsIrreducible →
          _root_.GlobalTheory.BI.IsIrrChar K L (fun g => algebraMap K L (ρ.character g))) := by
  intro K L _ _ _ G _ V _ _ _ ρ
  set e : V ≃ₗ[K] (Fin (Module.finrank K V) → K) := (Module.finBasis K V).equivFun
  have hchar : ∀ g, (_root_.GlobalTheory.BI.transportRep ρ e).character g = ρ.character g := by
    intro g
    exact LinearMap.trace_conj' (ρ g) e
  refine ⟨⟨Module.finrank K V, _root_.GlobalTheory.BI.transportRep ρ e, fun g => ?_⟩, fun hρ => ?_⟩
  · rw [hchar]
  · refine ⟨Module.finrank K V, _root_.GlobalTheory.BI.transportRep ρ e, ?_, fun g => ?_⟩
    · have hs : IsSimpleOrder (Subrepresentation ρ) := hρ
      exact (_root_.GlobalTheory.BI.transportSubOrderIso ρ e).isSimpleOrder_iff.mpr hs
    · rw [hchar]

end GlobalTheory.BI
