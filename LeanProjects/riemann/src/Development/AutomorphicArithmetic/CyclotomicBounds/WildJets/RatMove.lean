import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OneLeAPlLast
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem lin_rat {ι κ V W : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Subfield ℂ) (b : Module.Basis ι ℂ V) (c : Module.Basis κ ℂ W) (f : V →ₗ[ℂ] W)
    (hf : ∀ i j, c.repr (f (b j)) i ∈ A) (v : V) (hv : ∀ j, b.repr v j ∈ A) (i : κ) : c.repr (f v) i ∈ A := by
  rw [← b.sum_repr v]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact sum_mem fun j _ => mul_mem (hv j) (hf i j)

private theorem rho_rat {ι E : Type} [Fintype ι] [Field E] {n : ℕ} (A : Subfield ℂ) (emb : ι → E →+* ℂ)
    (hA : ∀ τ x, emb τ x ∈ A) (lam : ι → DomWeight n) (g : GL (Fin n) E) (i j : VVIdx lam) :
    (bVV ℂ lam).repr (rhoVr emb lam g (bVV ℂ lam j)) i ∈ A := by
  refine actionRational_holds ℂ ι n lam A (invTrK (embGL emb g)) (fun τ a b => ?_) i j
  show ((((Formalism.UG.bc (emb τ) g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
  rw [← map_inv]
  exact hA τ _

theorem UpperTheory.WildA.ratMove :
    ∀ (D : D7) {n n' : ℕ} (lam : D.what₂.Tau → DomWeight n) (lam' : D.what₂.Tau → DomWeight n') (f f' : VV ℂ lam →ₗ[ℂ] VV ℂ lam')
      (g : GL (Fin n) D.host.E) (g' : GL (Fin n') D.host.E), f' ∘ₗ rhoVr (tauE D) lam g = rhoVr (tauE D) lam' g' ∘ₗ f →
      (∀ i j, (bVV ℂ lam').repr (f (bVV ℂ lam j)) i ∈ Set.range D.what₂.embLL) →
      ∀ i j, (bVV ℂ lam').repr (f' (bVV ℂ lam j)) i ∈ Set.range D.what₂.embLL := by
  intro D n n' lam lam' f f' g g' h hf i j
  have hlab : ∀ τ x, tauE D τ x ∈ D.what₂.embLL.fieldRange := fun τ x =>
    ⟨labLL D τ x, DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x⟩
  have e : f' (bVV ℂ lam j) = rhoVr (tauE D) lam' g' (f (rhoVr (tauE D) lam g⁻¹ (bVV ℂ lam j))) := by
    have h1 := LinearMap.congr_fun h (rhoVr (tauE D) lam g⁻¹ (bVV ℂ lam j))
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at h1
    exact h1
  rw [e]
  exact lin_rat D.what₂.embLL.fieldRange _ _ _ (rho_rat _ _ hlab lam' g') _
    (lin_rat D.what₂.embLL.fieldRange _ _ f hf _ fun k => rho_rat _ _ hlab lam g⁻¹ k j) i
