import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspValueType

section Model

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem dRep_conj (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (X : Mx n) (w : H) :
    dRep (fun g => σ (P * g * P⁻¹)) X w = dRep σ (P * X * P⁻¹) w := by
  unfold dRep
  simp only [GlobalTheory.SmVecModel.exp_smul_conj hP]

theorem foldr_conj (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (l : List (Mx n)) (w : H) :
    l.foldr (dRep fun g => σ (P * g * P⁻¹)) w = (l.map fun X => P * X * P⁻¹).foldr (dRep σ) w := by
  induction l with
  | nil => rfl
  | cons X l ih => rw [List.foldr_cons, List.map_cons, List.foldr_cons, ih, dRep_conj σ hP]

theorem sobNorm_conj (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (S : List (List (Mx n))) (w : H) :
    sobNorm (fun g => σ (P * g * P⁻¹)) S w = sobNorm σ (S.map fun l => l.map fun X => P * X * P⁻¹) w := by
  unfold sobNorm
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply, foldr_conj σ hP]

theorem sobNorm_conj_back (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (S : List (List (Mx n))) (w : H) :
    sobNorm (fun g => σ (P * g * P⁻¹)) (S.map fun l => l.map fun X => P⁻¹ * X * P) w = sobNorm σ S w := by
  rw [sobNorm_conj σ hP, List.map_map]
  congr 1
  refine (List.map_congr_left fun l _ => ?_).trans (List.map_id S)
  show List.map (fun X => P * X * P⁻¹) (List.map (fun X => P⁻¹ * X * P) l) = l
  rw [List.map_map]
  refine (List.map_congr_left fun X _ => ?_).trans (List.map_id l)
  exact GlobalTheory.SmVecModel.conj_cancel hP X

theorem exists_ctrl_conj [CompleteSpace H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} (hσ : Std ε σ) {P G : Mx n}
    (hP : IsUnit P) (hG : Pᴴ * Jm ε * P = G) (S₀ : List (List (Mx n))) (hS₀ : Words (lieOf G) S₀) :
    ∃ S, Words (lieOf G) S ∧ Ctrl (lieOf G) (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) S ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ w, SmoothVec (lieOf G) (fun g => σ (P * g * P⁻¹)) w →
        sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w ≤ A * sobNorm (fun g => σ (P * g * P⁻¹)) S w := by
  obtain ⟨S₁, hS₁, -, ⟨B, hB, hc⟩, A, hA, hd⟩ := GlobalTheory.TypeSumCtrl.exists_ctrl n ε H σ hσ
    (S₀.map fun l => l.map fun X => P * X * P⁻¹) (by
      intro l hl X hX
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact GlobalTheory.SmVecModel.lie_conj hP hG (hS₀ l' hl' Y hY))
  refine ⟨S₁.map fun l => l.map fun X => P⁻¹ * X * P, ?_,
    ⟨fun g => B (P * g * P⁻¹), hB.comp (by fun_prop), fun g hg w hw => ?_⟩, A, hA, fun w hw => ?_⟩
  · intro l hl X hX
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact GlobalTheory.SmVecModel.lie_conj_inv hP hG (hS₁ l' hl' Y hY)
  · rw [sobNorm_conj_back σ hP, sobNorm_conj_back σ hP]
    exact hc _ (GlobalTheory.TypeAtCompare.conj_mem hP hG hg) w (GlobalTheory.SmVecModel.smoothVec_of_conj hP hG hw)
  · rw [sobNorm_conj_back σ hP, sobNorm_conj σ hP]
    exact hd w (GlobalTheory.SmVecModel.smoothVec_of_conj hP hG hw)

theorem smoothVec_zero (Lie : Set (Mx n)) (σ : Mx n → (H →L[ℂ] H)) : SmoothVec Lie σ (0 : H) := by
  intro k Xs _
  simp only [map_zero]
  exact contDiff_const

theorem hasTypeAll_single [CompleteSpace H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} (hσ : Std ε σ) {P G : Mx n}
    (hP : IsUnit P) (hG : Pᴴ * Jm ε * P = G) {u : H} (hu : SmoothVec (lieOf G) (fun g => σ (P * g * P⁻¹)) u)
    {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieOf G) (fun g => σ (P * g * P⁻¹)) ℓ) {f : Mx n → ℂ}
    (hf : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ℓ (σ (P * g * P⁻¹) u) = f g) :
    HasTypeAll (lieOf G) (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) f := by
  obtain ⟨S₀, C₀, hS₀, hb⟩ := hℓ
  obtain ⟨S, hS, hc, A, hA, hd⟩ := exists_ctrl_conj hσ hP hG S₀ hS₀
  have hv : ∀ i, SmoothVec (lieOf G) (fun g => σ (P * g * P⁻¹)) ((Pi.single 0 u : ℕ → H) i) := fun i => by
    by_cases hi : i = 0
    · subst hi; simpa using hu
    · rw [Pi.single_eq_of_ne hi]; exact smoothVec_zero _ _
  refine ⟨S, hS, hc, Pi.single 0 u, fun i => if i = 0 then ℓ else 0, Pi.single 0 (|C₀| * A),
    ⟨⟨hv, fun i => ?_, fun i w hw => ?_, ?_, fun g hg => ?_⟩, fun S' _ => ?_⟩⟩
  · by_cases hi : i = 0
    · subst hi; simp only [Pi.single_eq_same]; positivity
    · rw [Pi.single_eq_of_ne hi]
  · by_cases hi : i = 0
    · subst hi
      simp only [if_true, Pi.single_eq_same]
      have h1 := hb w hw
      have h2 := hd w hw
      have h3 : 0 ≤ sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w := sobNorm_nonneg _ _ _
      have h4 : C₀ * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w ≤ |C₀| * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w :=
        mul_le_mul_of_nonneg_right (le_abs_self _) h3
      calc ‖ℓ w‖ ≤ C₀ * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w := h1
        _ ≤ |C₀| * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w := h4
        _ ≤ |C₀| * (A * sobNorm (fun g => σ (P * g * P⁻¹)) S w) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = |C₀| * A * sobNorm (fun g => σ (P * g * P⁻¹)) S w := by ring
    · simp [hi, Pi.single_eq_of_ne hi]
  · refine (hasSum_single 0 fun i hi => ?_).summable
    simp [Pi.single_eq_of_ne hi]
  · rw [← hf g hg]
    have := hasSum_single (f := fun i : ℕ => (if i = 0 then ℓ else 0) (σ (P * g * P⁻¹) ((Pi.single 0 u : ℕ → H) i))) 0
      fun i hi => by simp [hi]
    simpa using this
  · refine (hasSum_single 0 fun i hi => ?_).summable
    simp [Pi.single_eq_of_ne hi]

end Model

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

theorem isTypeAt_value {D : D7} (θ : InfFam D)
    (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {Sp : D.what₂.Tau → SPar} (M : DSModel V Sp)
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (v : M.Vec) (τ : D.what₂.Tau) :
    IsTypeAt θ V τ (Sp τ) (T v) := by
  have hD := M.ds τ
  haveI : CompleteSpace (M.H τ) := hD.1
  have hσ : Std (M.ε τ) (M.σ τ) := std_of_isDS hHC hD
  refine ⟨M.H τ, _, _, M.σ τ, M.lam τ, M.ε τ, M.fr τ, M.enum τ, hD, M.fr_unit τ, M.fr_gram τ, fun x => ?_⟩
  obtain ⟨ℓ, hℓ, hℓv⟩ := hT.cont τ v x
  have hu : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v τ : M.H τ) :=
    GlobalTheory.SmVecModel.smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) ((GlobalTheory.SmVecModel.mem_sm_iff M τ _).1 (v τ).2)
  have hall : HasTypeAll (lieOf (gramAt D V τ)) (Formalism.QuantumDeterminants.UH (gramAt D V τ))
      (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (fun g => T v (x * atTau θ V τ g)) := by
    refine hasTypeAll_single hσ (M.fr_unit τ) (M.fr_gram τ) hu hℓ fun g hg => ?_
    have h1 := hT.equiv τ g hg v ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩ rfl
    have h2 := hℓv ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩
    show ℓ (M.rep τ g (v τ)) = _
    rw [h2, h1]
    rfl
  exact hasTypeAll_iff.1 hall

end GlobalTheory.CuspValueType

theorem GlobalTheory.CuspValueType.hasTypeAt_cusp : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : InfFam D), IsInfFam (D := D) θ → ∀ (N : GlobalTheory.Grid.Node D), N.V.SigOK → ∀ F ∈ N.Cusp θ, ∀ (w : SmT N.M) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ N.V τ (N.S τ) (F w) := by
  intro hP D θ hθ N hN F hF w τ
  have hgood : GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) :=
    ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ, GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ),
      GlobalTheory.TypeAtCompare.card_eq_of_congr (N.M.fr_unit τ) (N.M.fr_gram τ) (hN (tauE D τ))⟩
  have key : ∀ T, Mult.IsMultMap θ N.M ∅ 1 T → ∀ v, T v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub θ N.V τ (N.S τ) := fun T hT v =>
    GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ N.V τ (N.S τ) (T v) hP.discreteSeriesUpqExists
      (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
      hP.casselmanWallach hθ hN hgood (hT.aut v)
      (GlobalTheory.CuspValueType.isTypeAt_value θ hP.harishChandraModules N.M hT v τ)
  have main : ∀ T ∈ Mult.Mult θ N.M ∅ 1, ∀ w, PiTensorProduct.lift T w ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub θ N.V τ (N.S τ) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      intro w
      induction w using PiTensorProduct.induction_on with
      | smul_tprod r v =>
        rw [map_smul, PiTensorProduct.lift.tprod]
        exact Submodule.smul_mem _ r (key T hT v)
      | add a b ha hb =>
        rw [map_add]
        exact Submodule.add_mem _ ha hb
    | zero =>
      intro w
      simp only [map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      intro w
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ (ha w) (hb w)
    | smul c a _ ha =>
      intro w
      rw [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ c (ha w)
  have hF' := (Mult.mem_multT θ N.M ∅ 1 F).1 hF
  have eF : F = PiTensorProduct.lift (PiTensorProduct.lift.symm F) := (LinearEquiv.apply_symm_apply _ F).symm
  rw [eF]
  exact main _ hF' w

end
