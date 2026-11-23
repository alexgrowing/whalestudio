import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormFamiliesComplexCombinationOfReadings
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.CoefFnEqZeroOfNotPos
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GramXiEqOfLawsFull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSTypP
import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.StrLeStrAddTwo
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ParabolicAtStandardWeylElement

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
namespace GlobalTheory.ShareOn.Reading
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ReadingSec
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem castFrame_mem_GG {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)}
    (hΨ : Ψ = Ψ') (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ) (x : Frame Ψ r) :
    castFrame hΨ x ∈ GG Ψ' G p0 ↔ x ∈ GG Ψ G p0 := by
  subst hΨ; rfl

variable {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type}
  [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
  {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}

theorem psi_eq (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (c : C) :
    M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ := by
  rw [← ha c]; exact (M.comp_Ψ c).symm

def rdFun (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) : C → Frame M.Ψ D.R.r → ℂ :=
  fun c x => rdR (h.laws v).p ((i : ℕ) + 1) F (e c) (castFrame (psi_eq ha c) x)

theorem mem_dom_iff (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (c : C) (x : Frame M.Ψ D.R.r) :
    castFrame (psi_eq ha c) x ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).dom ↔ x ∈ M.dom := by
  have hG : (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Gm = M.Gm := by
    rw [← ha c]; exact M.comp_Gm c
  have hp : (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).p0 = M.p0 := by
    rw [← ha c]; exact M.comp_basePoint c
  show castFrame (psi_eq ha c) x ∈ GG _ _ _ ↔ x ∈ GG _ _ _
  rw [hG, hp, castFrame_mem_GG]

end ReadingSec

section ReadingSec2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
variable {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type}
  [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
  {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}

def rdLin (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) :
    (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i) →ₛₗ[(r.used v).full.σ₀] (C → M.dom → ℂ) where
  toFun F := M.res (rdFun h ha F)
  map_add' F G := by
    funext c x
    simp only [TwoLevels.res, rdFun, rdR, Pi.add_apply, Submodule.coe_add, map_add]
  map_smul' a F := by
    funext c x
    simp only [TwoLevels.res, rdFun, rdR, Pi.smul_apply, Submodule.coe_smul, map_smulₛₗ, smul_eq_mul]

theorem rdLin_apply (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (c : C) (x : M.dom) :
    rdLin h ha F c x = rdFun h ha F c x.1 := rfl

end ReadingSec2

section LP
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem lastPos_kappa (p : PtAt ex Csz) (i : Fin D.R.m) : (p.κ i).LastPos := by
  intro τ k hk
  rw [(p.fw.kap i τ).1 k, Formalism.IndefR.Fock.KV.sig_Wc i τ]
  have e1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by
    show D.R.k + ((i : ℕ) + 1) - 1 = D.R.k + (i : ℕ); omega
  have e2 : D.R.k + (i : ℕ) - 1 = (k : ℕ) := by omega
  have h0 := GlobalTheory.PtStringTest.aPl_last_pos i τ
  rw [e2, ← e1] at h0
  exact h0
end LP

theorem exists_ext_embedding {K LL : Type} [Field K] [NumberField K] [Field LL] [NumberField LL] [Algebra K LL]
    (σ₀ : K →+* ℂ) : ∃ σ : LL →+* ℂ, ∀ a, σ (algebraMap K LL a) = σ₀ a := by
  letI : Algebra K ℂ := σ₀.toAlgebra
  haveI : Algebra.IsAlgebraic K LL := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  exact ⟨(IsAlgClosed.lift : LL →ₐ[K] ℂ).toRingHom, fun a => (IsAlgClosed.lift : LL →ₐ[K] ℂ).commutes a⟩

section Card
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem card_of_runModel {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} {h : RunsOk (fw2 p) r} {i : Fin D.R.m} {C : Type}
    [Finite C] [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r}
    (hM : RunModel p r h i M ka) : M.Ψ.card = D.R.f := by
  obtain ⟨v, e, -⟩ := hM
  obtain ⟨k⟩ : Nonempty ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp :=
    ⟨((r.used v).full.dict ((i : ℕ) + 1) (r.used v).full.σ₀ 1).1⟩
  have h2 := Formalism.L2.Pj.DatLin.two_card (M.comp (e.symm k)).cmType
  rw [M.comp_Ψ, Formalism.L2.S.Pv.MSTypP.finrank_hostE' D] at h2
  omega

end Card

end GlobalTheory.ShareOn.Reading
