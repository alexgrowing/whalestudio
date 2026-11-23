import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.RankCover

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.BadRep

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.BadCount
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed typeEmb grpHR grpGHR transl levelGU)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU unitri superDiag)
open GlobalTheory.LevPull (CongMod)
open Formalism.MainNotions.ArithmeticCylinders
open scoped TensorProduct

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

set_option maxHeartbeats 2000000 in

theorem badRep_at (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i) (hY : GoodCov p i Y) :
    ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g D.nd) (s : G0g D.nd →* (LevelAut (dat p i) Y.d.l₂)) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g D.nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g D.nd)), IsSplit π s ∧ IsWhit D Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf D k (H k)) ∧ Pb.comap π = grpHR fr ∧ (∀ k, (H k).comap π = grpGHR fr k) ∧ (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g D.nd) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) D.ntypes.e0) : Submodule ℂ (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) := by
  refine (frame_data p i Y hY.1).elim fun fr h => h.elim fun ε h => h.elim fun iso' h => h.elim fun t h => ?_
  refine p.grpRecPin.elim fun plg h' => h'.elim fun iso h' => ?_
  have hl₂ := h.1
  have hpin := h'.2.2.2
  let c : p.P.Gp ≃* G0g D.nd := p.R.eG.trans p.cG
  let θ : LevelAut (dat p i) Y.d.l₂ →* p.P.Gp := t.toMonoidHom.comp (typeRed fr)
  let π : LevelAut (dat p i) Y.d.l₂ →* G0g D.nd := c.toMonoidHom.comp θ
  let s : G0g D.nd →* LevelAut (dat p i) Y.d.l₂ := (typeEmb hl₂ fr).comp (t.symm.toMonoidHom.comp c.symm.toMonoidHom)
  have hs : ∀ g, θ (s (c g)) = g := fun g => by
    show t (typeRed fr (typeEmb hl₂ fr (t.symm (c.symm (c g))))) = g
    rw [GlobalTheory.LevDesc.typeRed_typeEmb, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  have hsp : IsSplit π s := by
    refine ⟨fun g => ?_, fun g γ hγ => ?_⟩
    · show c (t (typeRed fr (typeEmb hl₂ fr (t.symm (c.symm g))))) = g
      rw [GlobalTheory.LevDesc.typeRed_typeEmb, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    · have h0 : c (t (typeRed fr γ)) = 1 := hγ
      rw [EmbeddingLike.map_eq_one_iff, EmbeddingLike.map_eq_one_iff, GlobalTheory.LevDesc.typeRed_eq_one] at h0
      exact hl₂.commute (GlobalTheory.LevDesc.typeEmb_mem hl₂ fr _) h0
  refine (whit_data p.R.toRealDat p.F.lv2 p.charW.base.grp.levels c plg iso hpin).elim fun Pb w => w.elim fun lam w =>
    w.elim fun ψ w => ?_
  have hH := fun k => half_data p.R.toRealDat c plg iso hpin ε iso' t h.2.2.2.1 k
  have hQ : ∀ γ, γ ∈ Pb.comap π ↔ θ γ ∈ (p.F.lv2.lvl false).P := fun γ => w.2.1 (θ γ)
  refine (rank_data p i Y hY.1 θ h.2.1 (fun γ hγ => (congrArg t (h.2.2.1 γ hγ)).trans (map_one t)) c s hs (Pb.comap π) hQ
    (lam.comp (π.subgroupComap Pb)) (fun γ => w.2.2 (θ γ) γ.2 _) D.ntypes.e0 h'.2.1).elim fun ρ r => r.elim fun χ r => ?_
  exact ⟨fr, π, s, ρ, χ, Pb, lam, ψ, lam.comp (π.subgroupComap Pb), fun k => (hH k).choose, hsp, w.1, fun _ => rfl,
    fun k => (hH k).choose_spec.1, Subgroup.ext fun γ => (hQ γ).trans (h.2.2.2.2 _),
    fun k => Subgroup.ext fun γ => (hH k).choose_spec.2 _, r⟩

end Point

end GlobalTheory.CovTop.BadRep
