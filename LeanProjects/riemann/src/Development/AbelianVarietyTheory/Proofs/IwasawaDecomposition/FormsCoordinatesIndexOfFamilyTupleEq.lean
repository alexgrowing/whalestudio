import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL))
  (tr : TrI X.B px)

set_option maxHeartbeats 2000000 in

theorem rMat_famR_eq (U U' : Set I.ι) (P : Subgroup (Gc X.B px)) (ψ : P →* X.toD7.what₂.LLˣ) (t : TupU I U) (t' : TupU I U')
    (h : t.1 = t'.1) :
    rMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ t = rMat (D := X.toD7) (famR X I hX U' Xg tr).A P ψ t' := by
  obtain ⟨τ, hτ⟩ := t
  obtain ⟨τ', hτ'⟩ := t'
  obtain rfl : τ = τ' := h
  exact (by with_unfolding_all exact ((Eq.refl (rMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ ⟨τ, hτ⟩)) :))

set_option maxHeartbeats 2000000 in

theorem lMat_famR_eq (U U' : Set I.ι) (P : Subgroup (Gc X.B px)) (ψ : P →* X.toD7.what₂.LLˣ) (i : Fin X.toD7.R.m)
    (t : TupU I U) (t' : TupU I U') (h : t.1 = t'.1) :
    lMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ i t = lMat (D := X.toD7) (famR X I hX U' Xg tr).A P ψ i t' := by
  obtain ⟨τ, hτ⟩ := t
  obtain ⟨τ', hτ'⟩ := t'
  obtain rfl : τ = τ' := h
  exact (by with_unfolding_all exact ((Eq.refl (lMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ i ⟨τ, hτ⟩)) :))

set_option maxHeartbeats 2000000 in

theorem mAU_mLU_ixOf : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U), (∀ b, mAU X I hX Xg tr b (ixOf I U t) = rMat (D := X.toD7) (famR X I hX U Xg tr).A (levP (face0 X I hX U Xg tr).lv2 b).1 (levP (face0 X I hX U Xg tr).lv2 b).2 t) ∧ ∀ i : Fin X.toD7.R.m, mLU X I hX Xg tr (ixOf I U t) ((i : ℕ) + 1) = lMat (D := X.toD7) (famR X I hX U Xg tr).A (face0 X I hX U Xg tr).lv2.P0 (face0 X I hX U Xg tr).lv2.ψ0 i t := by
  intro X px I hX U Xg tr t
  refine ⟨fun b => ?_, fun i => ?_⟩
  · cases b
    · exact rMat_famR_eq X I hX Xg tr Set.univ U (lev0 I) (chr0 I) (tAll I (ixOf I U t)) t (tup_ixOf I t)
    · exact rMat_famR_eq X I hX Xg tr Set.univ U (lev1 I) (chr1 I) (tAll I (ixOf I U t)) t (tup_ixOf I t)
  · have hi : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ X.toD7.R.m := ⟨by omega, i.2⟩
    unfold mLU
    rw [dif_pos hi]
    exact lMat_famR_eq X I hX Xg tr Set.univ U (lev0 I) (chr0 I) i (tAll I (ixOf I U t)) t (tup_ixOf I t)

end GlobalTheory.Mem.R3.Rw

end
