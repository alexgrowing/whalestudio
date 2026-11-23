import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipVac

theorem exists_gauss_vac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M.IsGauss Bs.ψ Bs.emb f₀ ∧
      IsDatumA (t := t) W e Γ (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) := by
  intro D T L sc G μ₀ hL W ρ t i j M _ e Bs Γ X om om' h hT hti
  have h₁ := ρ.vX_is i (j + 1) i.2 j.2
  have h₂ := ρ.vT_is t (i + 1) j i.2 j.2
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨f, hf⟩ := GlobalTheory.BigDat.exists_vac hL h hT hti h₁ h₂
  refine ⟨f, fun h0 => ?_, GlobalTheory.BigDat.isGauss (c := 1) h hT h₁ h₂ (by rw [hf, one_smul]),
    (isFinPart_vac hG ∅).fam.mem hG f, fun u => ?_⟩
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 (GlobalTheory.BigDat.vac_ne_zero h₁)
    obtain ⟨y, hy⟩ := Function.ne_iff.1 (GlobalTheory.BigDat.vac_ne_zero h₂)
    have := congrFun hf (GlobalTheory.BigDat.ofMaps e (x, y))
    rw [h0, show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : SInf D.host.F (GlobalTheory.BigDat.Ix G i j)) Γ.M.vac =
        (0 : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure 0 Γ.M.vac from funext fun _ => (zero_mul _).trans (zero_mul _).symm,
      GlobalTheory.BigDat.thetaPt_smul, zero_mul, GlobalTheory.BigDat.box, GlobalTheory.BigDat.mapV_ofMaps, GlobalTheory.BigDat.mapW_ofMaps] at this
    exact mul_ne_zero hx hy this.symm
  · refine (congrFun hf u).trans ?_
    first
    | exact (one_mul _).symm.trans (Finsupp.sum_single_index (h := fun d (c : ℂ) => c * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e d u) (zero_mul _)).symm
    | (erw [Finsupp.sum_single_index (by exact zero_mul _), one_mul]; rfl)
    | (simp only [Finsupp.sum_single_index, zero_mul, one_mul]; rfl)

end GlobalTheory.FlipVac

end
