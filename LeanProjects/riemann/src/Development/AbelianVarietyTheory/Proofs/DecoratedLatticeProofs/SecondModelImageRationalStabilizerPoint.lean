import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointInfiniteMatricesEqOneOfFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem toH_rat : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (a : GA D (D.sp.X 0)), a ∈ GQ (D.sp.X 0) → ∃ γ : Gam X u, iotaI X u γ = (B.toH a).1 ∧ iotaF X u γ = (B.toH a).2 := by
  intro D X h u ψ B a ha
  have hrat : embA B.d B.o a ∈ GQ (D.sp.Y 0) := by
    have e : embA B.d B.o a = B.d.emb0 (B.o.emb (a, 1)) := rfl
    rw [e]
    exact B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ ha (one_mem _))
  have k : ∀ {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA), x ∈ I.GFset → castGA e x ∈ I'.GFset := by
    intro I I' e x hx
    subst e
    exact hx
  have hr : iotaX X h (embA B.d B.o a) ∈ X.B.I.GFset :=
    k h.symm _ ((Formalism.IndefR.RationalEmbedding.iota_rat D _).1 hrat)
  have hH := (B.tieH (embA B.d B.o a)).1 ⟨a, rfl⟩
  exact ⟨⟨iotaX X h (embA B.d B.o a), Subgroup.mem_inf.2 ⟨hr, Subgroup.mem_prod.2 hH⟩⟩, rfl, rfl⟩

end GlobalTheory.Core.Mi
