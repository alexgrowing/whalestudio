import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColTypeLift

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

def FinCoef (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (φ : GA D V → ℂ) : Prop :=
  ∀ x, ∃ (n : ℕ) (L : Fin n → (M.H τ →L[ℂ] ℂ)) (v : Fin n → M.H τ),
    (∀ i, SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v i)) ∧
    ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), φ (x * atTau θ V τ g) = ∑ i, L i (M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (v i))

theorem FinCoef.zero (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    FinCoef θ M τ 0 := fun _ => ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun g _ => by simp⟩

theorem FinCoef.add {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {φ ψ : GA D V → ℂ} (h₁ : FinCoef θ M τ φ) (h₂ : FinCoef θ M τ ψ) : FinCoef θ M τ (φ + ψ) := fun x => by
  obtain ⟨n₁, L₁, v₁, hv₁, e₁⟩ := h₁ x
  obtain ⟨n₂, L₂, v₂, hv₂, e₂⟩ := h₂ x
  refine ⟨n₁ + n₂, Fin.append L₁ L₂, Fin.append v₁ v₂, fun i => ?_, fun g hg => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using hv₁ i
    · simpa using hv₂ i
  · rw [Fin.sum_univ_add, Pi.add_apply, e₁ g hg, e₂ g hg]
    simp

theorem FinCoef.smul {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {φ : GA D V → ℂ} (c : ℂ) (h : FinCoef θ M τ φ) : FinCoef θ M τ (c • φ) := fun x => by
  obtain ⟨n, L, v, hv, e⟩ := h x
  refine ⟨n, fun i => c • L i, v, hv, fun g hg => ?_⟩
  rw [Pi.smul_apply, e g hg, Finset.smul_sum]
  simp

theorem FinCoef.sum {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {n : ℕ} {φ : Fin n → GA D V → ℂ} (h : ∀ i, FinCoef θ M τ (φ i)) : FinCoef θ M τ (∑ i, φ i) := by
  classical
  have : ∀ s : Finset (Fin n), FinCoef θ M τ (∑ i ∈ s, φ i) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using FinCoef.zero θ M τ
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih
  exact this Finset.univ

theorem finCoef_lift {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    (z : SmT M) : FinCoef θ M τ (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    intro x
    obtain ⟨ℓ, -, hℓ⟩ := GlobalTheory.DefiniteEnd.exists_sobCont M τ T f x
    have hsv : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (f τ : M.H τ) := by
      have hw : ∀ w ∈ M.sm τ, SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) w := by
        intro w hw
        rw [GlobalTheory.SmVec.sm_eq M τ] at hw
        exact hw
      exact hw _ (f τ).2
    refine ⟨1, fun _ => r • LinearMap.toContinuousLinearMap ℓ, fun _ => (f τ : M.H τ), fun _ => hsv, fun g hg => ?_⟩
    have e1 := congrFun (hT.equiv τ g hg f ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩ rfl) x
    have e3 : T f (x * atTau θ V τ g) = ℓ (M.rep τ g (f τ)) := by
      rw [hℓ ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩]
      exact e1.symm
    rw [Fin.sum_univ_one, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul, e3, LinearMap.coe_toContinuousLinearMap']
    rfl
  | add a b ha hb =>
    rw [map_add]
    exact ha.add hb

end GlobalTheory.ColTypeLift

namespace GlobalTheory.ColTypeLift

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem finCoef_multT {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] (F : MultT θ M ∅ 1) (z : SmT M) : FinCoef θ M τ (F.1 z) := by
  have hm : PiTensorProduct.lift.symm F.1 ∈ Mult θ M ∅ 1 := (mem_multT θ M ∅ 1 F.1).1 F.2
  have key : ∀ T ∈ Mult θ M ∅ 1, FinCoef θ M τ (PiTensorProduct.lift T z) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem x hx => exact finCoef_lift M τ hx z
    | zero => simpa using FinCoef.zero θ M τ
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact hx.add hy
    | smul c x _ hx => rw [map_smul, LinearMap.smul_apply]; exact hx.smul c
  have := key _ hm
  rwa [LinearEquiv.apply_symm_apply] at this

theorem isTypeAt_sum (θ : InfFam D) (N : Node D) (hs : N.V.SigOK) (hd : N.V.IsDefinite) (τ : D.what₂.Tau) {n : ℕ}
    (F : Fin n → N.Cusp θ) (z : Fin n → SmT N.M) : IsTypeAt θ N.V τ (N.S τ) (∑ i, (F i).1 (z i)) := by
  haveI := GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  exact GlobalTheory.EndCusp.isTypeAt_of_finSum θ N.V τ (N.M.enum τ) (N.M.ds τ) (N.M.fr_unit τ) (N.M.fr_gram τ) _
    (FinCoef.sum fun i => finCoef_multT N.M τ (F i) (z i))

theorem xp_definite {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R} (hG : G.Is)
    (k : ℕ) (hk : k ≤ D.R.m) : (G.Xp k).V.SigOK ∧ (G.Xp k).V.IsDefinite := by
  cases k with
  | zero =>
    have h := hG.spaces.P D.R.m le_rfl
    refine ⟨h.sigOK, fun τ => Or.inl ?_⟩
    rw [h.sig, h.rank]
    simp
  | succ k =>
    have h := hG.spaces.X k hk
    refine ⟨h.sigOK, fun τ => Or.inl ?_⟩
    rw [h.sig, h.rank]
    simp

end GlobalTheory.ColTypeLift
