import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.PolMatchConst

def finProd {F : Type} [Field F] [NumberField F] {κ : Type} (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)

theorem match_of_polMatch : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' → Φ' ∈ G.M'.So B.ψ B.τ₁ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Match B G X R Rf Φ Φ' := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hT Φ Φ' hP hSo
  have hP0 := hP
  obtain ⟨T, hXT, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', _⟩ := hP
  have hstd : ∀ (κ : Type) (ψ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ),
      (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      (∀ v ∉ T, ψ v = vac v) →
      ∀ᶠ v in Filter.cofinite, ψ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    intro κ ψ vac hvac hψ
    filter_upwards [hvac, T.finite_toSet.compl_mem_cofinite] with v hv hvT
    rw [hψ v hvT, hv]
  have hg : ∀ i, finProd (φ i) ∈ GlobalTheory.WeilM.SB _ := fun i =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV (φ i) (hf i).2.1 (hstd _ _ _ hT.geo.hM.std (hf i).2.2),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod (φ i) (hf i).2.1 (hstd _ _ _ hT.geo.hM.std (hf i).2.2)⟩
  have hg' : ∀ j, finProd (φ' j) ∈ GlobalTheory.WeilM.SB _ := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV (φ' j) (hf' j).2.1 (hstd _ _ _ hT.geo.hM'.std (hf' j).2.2),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod (φ' j) (hf' j).2.1 (hstd _ _ _ hT.geo.hM'.std (hf' j).2.2)⟩
  have e : Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (finProd (φ i)) := hΦ
  have e' : Φ' = ∑ j, GlobalTheory.WeilM.pureA F (f' j) (finProd (φ' j)) := hΦ'
  refine ⟨hSo, m, m', fun i => finProd (φ i), f, fun _ => f, fun j => finProd (φ' j), f', fun _ => f',
    fun i => ⟨hg i, tendsto_const_nhds⟩, fun j => ⟨hg' j, tendsto_const_nhds⟩, e, e', fun _ => ?_⟩
  rw [← e, ← e']
  exact ⟨hSo, hP0⟩

end GlobalTheory.SquareAgree.PolMatchConst
