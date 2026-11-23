import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.exists_finset_reps_of_cls {T Γ C : Type} [Finite C] (P : T → Prop) (sm : Γ → T → T) (cls : T → C)
    (h : ∀ L L', P L → P L' → cls L = cls L' → ∃ γ, L' = sm γ L) :
    ∃ R : Finset T, (∀ L ∈ R, P L) ∧ ∀ L, P L → ∃ L₀ ∈ R, ∃ γ : Γ, L = sm γ L₀ := by
  classical
  let S : Set C := {x | ∃ L, P L ∧ cls L = x}
  have hS : ∀ x : S, ∃ L, P L ∧ cls L = x.1 := fun x => x.2
  choose f hf using hS
  haveI : Fintype S := Fintype.ofFinite S
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · intro L hL
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hL
    exact (hf x).1
  · intro L hL
    let x : S := ⟨cls L, L, hL, rfl⟩
    exact ⟨f x, Finset.mem_image_of_mem f (Finset.mem_univ x), h (f x) L (hf x).1 hL (hf x).2⟩

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.TwV.finClasses_sysS : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j c, ((sysS H X std).Lv.lev j c).FinClasses := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j c
  change (Lv.lev j c).FinClasses
  by_cases hj : j ≤ D.R.m
  · exact GlobalTheory.TwV.exists_finset_reps_of_cls (C := (D.chTw u μ).cls j) _ (Lv.lev j c).smul ((labAt X H).cls j c)
      (fun L L' hL hL' e => (((labAt X H).cls_iff j hj c c L L' hL hL').1 e).2)
  · exact (J.empty j (by omega)).elim c
