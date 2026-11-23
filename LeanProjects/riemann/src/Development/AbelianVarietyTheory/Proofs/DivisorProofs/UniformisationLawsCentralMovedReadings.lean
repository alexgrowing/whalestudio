import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullHeckeRealDatMovedReadings

set_option autoImplicit false

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

namespace GlobalTheory.Unframe

theorem lUnif_moveR {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G) (hw : ∀ i σ, w i σ ∈ Subgroup.center G) (hU : R.LUnif) :
    (moveR R w).LUnif := by
  intro i σ
  obtain ⟨h1, h2, h3⟩ := hU i σ
  have hl : ∀ x, (R.FW i).ρ (w i σ)⁻¹ ((R.FW i).ρ (w i σ) x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hr : ∀ x, (R.FW i).ρ (w i σ) ((R.FW i).ρ (w i σ)⁻¹ x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hc : ∀ g x, (R.FW i).ρ (w i σ) ((R.FW i).ρ g x) = (R.FW i).ρ g ((R.FW i).ρ (w i σ) x) := fun g x => by
    rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.mem_center_iff.1 (hw i σ) g, map_mul, Module.End.mul_apply]
  refine ⟨fun n b hb => ?_, ?_, fun g x => ?_⟩
  · have hinj : Function.Injective ((R.FW i).ρ (w i σ)) := Function.LeftInverse.injective hl
    exact h1 n (fun k => (R.FW i).ρ (w i σ) (b k)) (hb.map' _ (LinearMap.ker_eq_bot.2 hinj))
  · refine top_le_iff.1 (h2 ▸ Submodule.span_mono ?_)
    rintro _ ⟨x, rfl⟩
    exact ⟨(R.FW i).ρ (w i σ)⁻¹ x, congrArg ((R.FW i).j σ) (hr x)⟩
  · have h := h3 g ((R.FW i).ρ (w i σ) x)
    rw [← hc] at h
    exact h

end GlobalTheory.Unframe
