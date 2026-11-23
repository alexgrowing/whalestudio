import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Formalism.LocalToGlobal.IndefiniteReal.TopMult

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.CentreRight

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom
open Formalism.MainNotions.StandardLattice (infMat)

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem foldr_map_eq {M α : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (f : α → M → M)
    (a : α → Module.End ℂ S) (h : ∀ i (x : S), f i x.1 = (a i x).1) (l : List α) (x : S) :
    (l.map f).foldr (fun f acc => f acc) x.1 = ((l.map a).prod x).1 := by
  induction l with
  | nil => simp
  | cons i l ih => rw [List.map_cons, List.map_cons, List.foldr_cons, List.prod_cons, Module.End.mul_apply, ih, h]

theorem gelfT_eq (hθ : IsInfFam θ) (τ : D.what₂.Tau) (k : ℕ) (φ : SmFun θ V) :
    gelfT θ V τ k φ.1 = (-1 : ℂ) ^ (k + 1) • (MulOpposite.unop (GlobalTheory.SmoothForms.gelfA
      (fun a b => MulOpposite.op (derEnd hθ τ (Matrix.single a b 1))) k) φ).1 := by
  rw [gelfT, GlobalTheory.SmoothForms.gelfA, Finset.unop_sum, LinearMap.sum_apply, Submodule.coe_sum]
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [MulOpposite.unop_list_prod, List.map_ofFn, List.ofFn_eq_map, List.ofFn_eq_map, ← List.map_reverse,
    ← List.map_reverse]
  exact foldr_map_eq _ _ _ (fun _ _ => rfl) _ φ

theorem gelfT_rTr_real (hθ : IsInfFam θ) {h : GA D V} (hh : IsRealPt θ h) (τ : D.what₂.Tau) (k : ℕ) {φ : GA D V → ℂ}
    (hφ : φ ∈ SmFun θ V) : gelfT θ V τ k (rTr V h φ) = rTr V h (gelfT θ V τ k φ) := by
  let T : Module.End ℂ (SmFun θ V) := (rTrLin h).restrict fun _ hx => rTr_mem hθ hh hx
  have h1 := infMat_mul_inv θ V τ h
  have h2 := mul_eq_one_comm.1 h1
  have hQP : (infMat D.sp.cm.sig V.gram (θ τ) h⁻¹)ᵀ * (infMat D.sp.cm.sig V.gram (θ τ) h)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have key := GlobalTheory.Dec.GelfAd.trace_pow_comm
    (fun a b => MulOpposite.op (derEnd (V := V) hθ τ (Matrix.single a b 1))) (MulOpposite.op T) _ _ hQP
    (fun a b => by
      simp only [← MulOpposite.op_smul, ← Finset.op_sum, ← MulOpposite.op_mul, ← map_smul, ← map_sum]
      have e : ∑ c, ∑ d, ((infMat D.sp.cm.sig V.gram (θ τ) h)ᵀ a c * (infMat D.sp.cm.sig V.gram (θ τ) h⁻¹)ᵀ d b) •
          (Matrix.single c d 1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) =
          infMat D.sp.cm.sig V.gram (θ τ) h * Matrix.single a b 1 * infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ := by
        rw [Matrix.matrix_eq_sum_single (_ * Matrix.single a b 1 * _)]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
        congr 1
        simp [Matrix.mul_apply, Matrix.single, ite_and]
      rw [e]
      congr 1
      refine LinearMap.ext fun ψ => Subtype.ext ?_
      have := RderC_rTr hθ hh τ
        (infMat D.sp.cm.sig V.gram (θ τ) h * Matrix.single a b 1 * infMat D.sp.cm.sig V.gram (θ τ) h⁻¹) ψ.1
      rw [adAt, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul,
        Matrix.mul_assoc (Matrix.single a b 1), h2,
        Matrix.mul_one] at this
      exact this.symm) (k + 1)
  rw [← GlobalTheory.SmoothForms.gelfA_eq_sum_pow] at key
  have := congrArg (fun S : (Module.End ℂ (SmFun θ V))ᵐᵒᵖ => (S.unop ⟨φ, hφ⟩).1) key
  rw [gelfT_eq hθ τ k ⟨φ, hφ⟩, gelfT_eq hθ τ k ⟨_, rTr_mem hθ hh hφ⟩]
  exact congrArg (fun F => (-1 : ℂ) ^ (k + 1) • F) this.symm

theorem gelfT_rTr_fin {u : GA D V} (hu : u ∈ GfC V) (τ : D.what₂.Tau) (n : ℕ) (φ : GA D V → ℂ) :
    gelfT θ V τ n (rTr V u φ) = rTr V u (gelfT θ V τ n φ) := by
  unfold gelfT
  rw [Finset.sum_congr rfl fun idx _ => GlobalTheory.Mem.FinTranslate.foldr_rTr u _ _ (fun a ha ψ => ?_) φ]
  · funext g
    simp only [rTr, Finset.sum_apply, Pi.smul_apply]
  · obtain ⟨b, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 ha)
    unfold RderC
    rw [GlobalTheory.Mem.FinTranslate.Rder_rTr hu, GlobalTheory.Mem.FinTranslate.Rder_rTr hu]
    rfl

theorem rTr_mem_fin {u : GA D V} (hu : u ∈ GfC V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : rTr V u φ ∈ SmFun θ V := by
  intro n τs Xs hX g
  have := hφ n τs Xs hX (g * u)
  convert this using 2 with t
  unfold rTr
  rw [mul_assoc, mul_assoc, comm_of_mem V (list_prod_mem fun a ha => ?_) hu]
  obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
  exact atTau_mem V _ _

theorem rTr_mul (u a : GA D V) (φ : GA D V → ℂ) : rTr V (u * a) φ = rTr V u (rTr V a φ) := by
  funext g
  simp only [rTr, mul_assoc]

theorem decomp (hθ : IsInfFam θ) (x : GA D V) : ∃ u ∈ GfC V, ∃ a, IsRealPt θ a ∧ x = u * a := by
  obtain ⟨u, hu, a, ha, e⟩ := Formalism.IndefR.TopMult.ga_decomp x
  exact ⟨u, hu, a, ⟨ha, GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a⟩, e⟩

theorem rTr_mem_all (hθ : IsInfFam θ) (x : GA D V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : rTr V x φ ∈ SmFun θ V := by
  obtain ⟨u, hu, a, ha, rfl⟩ := decomp hθ x
  rw [rTr_mul]
  exact rTr_mem_fin hu (rTr_mem hθ ha hφ)

theorem gelf_rTr_all (hθ : IsInfFam θ) (x : GA D V) (τ : D.what₂.Tau) (k : ℕ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    gelf θ V τ k (rTr V x φ) = rTr V x (gelf θ V τ k φ) := by
  obtain ⟨u, hu, a, ha, rfl⟩ := decomp hθ x
  rw [rTr_mul, rTr_mul, GlobalTheory.Mem.FinTranslate.gelf_rTr hu, gelf_rTr hθ ha τ k hφ]

theorem gelfT_rTr_all (hθ : IsInfFam θ) (x : GA D V) (τ : D.what₂.Tau) (k : ℕ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    gelfT θ V τ k (rTr V x φ) = rTr V x (gelfT θ V τ k φ) := by
  obtain ⟨u, hu, a, ha, rfl⟩ := decomp hθ x
  rw [rTr_mul, rTr_mul, gelfT_rTr_fin hu, gelfT_rTr_real hθ ha τ k hφ]

theorem foldr_gelf_rTr (hθ : IsInfFam θ) (x : GA D V) (τ : D.what₂.Tau) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V)
    (l : List ℕ) : l.foldr (fun i g => gelf θ V τ i g) (rTr V x φ) = rTr V x (l.foldr (fun i g => gelf θ V τ i g) φ) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, gelf_rTr_all hθ x τ i
      ((linOnSm_foldr (fun i => gelf θ V τ i) l fun j _ => linOnSm_gelf τ j).mem φ hφ)]

theorem centreAct_rTr (hθ : IsInfFam θ) (x : GA D V) (τ : D.what₂.Tau) (p : MvPolynomial ℕ ℂ) {φ : GA D V → ℂ}
    (hφ : φ ∈ SmFun θ V) : centreAct θ τ V p (rTr V x φ) = rTr V x (centreAct θ τ V p φ) := by
  unfold centreAct polyAct opPow
  simp only [foldr_gelf_rTr hθ x τ hφ]
  funext g
  simp only [rTr, Finset.sum_apply, Pi.smul_apply]

theorem centre_comm_right : ∀ (D : D7) (V : HSp D), ∀ θ : InfFam D, IsInfFam θ → ∀ (τ : D.what₂.Tau) (f : GA D V → ℂ), f ∈ SmFun θ V → ∀ x : GA D V, (fun h => f (h * x)) ∈ SmFun θ V ∧ (∀ p, centreAct θ τ V p (fun h => f (h * x)) = fun h => centreAct θ τ V p f (h * x)) ∧ ∀ k, gelf θ V τ k (fun h => f (h * x)) = (fun h => gelf θ V τ k f (h * x)) ∧ gelfT θ V τ k (fun h => f (h * x)) = fun h => gelfT θ V τ k f (h * x) :=
  fun _ _ _ hθ τ _ hf x => ⟨rTr_mem_all hθ x hf, fun p => centreAct_rTr hθ x τ p hf,
    fun k => ⟨gelf_rTr_all hθ x τ k hf, gelfT_rTr_all hθ x τ k hf⟩⟩

end GlobalTheory.RegSch.CentreRight

end
