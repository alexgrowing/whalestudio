import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section

namespace GlobalTheory.PureMatch

open GlobalTheory.LFun

theorem chrW_triple_split_nu : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil)
    (M : Vol G) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : Chars D.host.F D.host.E), IsTripleOf W M t i j e Bs Γ X →
    ∀ (w : Pl D.host.E) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
    splitPrime τ = w →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν τ = ((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom) ∧
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.α τ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν τ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β τ := by
  intro D T L sc G μ₀ hL W M t i j e Bs Γ X hX w v hv τ hw
  subst hw
  have e1 : X.ν = G.nu t i (j + 1) := by
    show X.α / X.β = _
    rw [hX.α, hX.β]
    exact mul_div_mul_right_eq_div _ _ _
  refine ⟨?_, ?_⟩
  · ext x
    show (locChar X.ν (splitPrime τ) (Units.map (complMap hv).toMonoidHom x) : ℂ) = _
    rw [e1, locChar_eq_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL)]
    have hj : (j : ℕ) < D.R.m := j.2
    simp only [GlobalTheory.FunObj.SqNum.nuH, Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply,
      Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, div_eq_mul_inv]
    rfl
  · ext x
    show (locChar X.α (splitPrime τ) _ : ℂ) =
      (locChar (X.α / X.β) (splitPrime τ) _ * locChar X.β (splitPrime τ) _ : ℂˣ)
    simp [locChar]

end GlobalTheory.PureMatch
