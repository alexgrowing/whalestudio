import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

namespace GlobalTheory.FrameOf

theorem finite_classes_of_pres {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) :
    ∃ T : Finset G, ∀ g, ∃ γ ∈ ι.range, ∃ s ∈ T, ∃ κ ∈ presJ P, g = γ * s * κ := by
  classical
  have hf : (Set.range P.y).Finite := Set.finite_range _
  refine ⟨hf.toFinset, fun g => ?_⟩
  obtain ⟨c, ⟨γ, k, e⟩, -⟩ := P.reps g
  exact ⟨ι γ, ⟨γ, rfl⟩, P.y c, hf.mem_toFinset.2 ⟨c, rfl⟩, k, k.2, e⟩

theorem classesAt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T),
    ClassesAt p j t := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t
  exact finite_classes_of_pres (p.R.B.L j t).pres

end GlobalTheory.FrameOf
