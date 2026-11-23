import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldSphericalVectorTheta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrInertOfUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnramifiedCharCompUnitsMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulIntInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionEquationGlobal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedMaxCompactVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldInducedMaxCompactVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilMaxCompactFixedVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldWeilMaxCompactFixedVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedUnramifiedHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitRepresentationHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilModulusHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open GroundTheory.Global.AdicLiesOver
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.StdSphVal

theorem degreeOneEmbedding_mem_integers_iff {K : Type} [Field K] [NumberField K] (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] (h1 : Module.finrank (Qv v) (Kv K w) = 1) (ξ : K) :
    dg1 v w ξ ∈ 𝒪[Qv v] ↔ algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w] := by
  have hb := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.algebraMap_bijective v w h1
  have e : algebraMap (Qv v) (Kv K w) (dg1 v w ξ) = algebraMap K (Kv K w) ξ :=
    Function.rightInverse_invFun hb.2 _
  rw [← e]
  exact (algebraMap_mem_integer_iff (Qv v) (Kv K w) (dg1 v w ξ)).symm

theorem val_std : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
    L.ok → L.std → Unr c v → ∀ k ∈ integralGL (Qv v) 2, ∀ ξ : K,
    ((∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]) → L.val k ξ = 1) ∧
    (¬ (∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]) → L.val k ξ = 0) := by
  intro K _ _ h2 c v L hok hstd hU k hk ξ
  have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  obtain ⟨hχc, hχ1, hχ0⟩ :=
    (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
  cases L with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    haveI := i₁
    haveI := i₂
    obtain ⟨hne, -, -⟩ := hok
    have hΦ : Φ = Set.indicator {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} 1 := hstd
    subst hΦ
    obtain ⟨hall, d₁, d₂⟩ := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.places_split h2 v w₁ w₂ hne
    have r₁ : IsUnramifiedChar (cAt c v w₁) :=
      GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hU w₁).1
    have hfix := GlobalTheory.CompanionTheory.SphTheta.SplitPiK.piks
      (GlobalTheory.CompanionTheory.SphTheta.SplitRWK.rwks GlobalTheory.CompanionTheory.SplitRep.sRep) (Qv v) _ hχc hχ1 hχ0 _ r₁ k hk
    have hval : LM.val (LM.sp w₁ w₂ (Set.indicator {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} 1)) k ξ =
        Set.indicator {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} (1 : Qv v × Qv v → ℂ)
          (dg1 v w₁ ξ, dg1 v w₂ ξ) := congrFun hfix _
    rw [hval]
    have hiff : (dg1 v w₁ ξ, dg1 v w₂ ξ) ∈ {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} ↔
        ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w] := by
      simp only [Set.mem_setOf_eq, degreeOneEmbedding_mem_integers_iff v w₁ d₁, degreeOneEmbedding_mem_integers_iff v w₂ d₂]
      refine ⟨fun h w hw => ?_, fun h => ⟨h w₁ i₁, h w₂ i₂⟩⟩
      rcases hall w hw with rfl | rfl
      · exact h.1
      · exact h.2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [Set.indicator_of_mem (hiff.2 h)]; rfl
    · rw [Set.indicator_of_notMem (fun h' => h (hiff.1 h'))]
  | @ns w i σ η Φ =>
    haveI := i
    obtain ⟨hu, hσ, hη, -⟩ := hok
    have hΦ : Φ = Set.indicator {x : Kv K w | x ∈ 𝒪[Kv K w]} 1 := hstd
    subst hΦ
    rcases GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K h2 v (fun w _ => (hU w).2) with
      ⟨a, b, ha, hb, hab⟩ | ⟨w', hw', -, hf, hord⟩
    · exact absurd ((hu a ha).trans (hu b hb).symm) hab
    obtain rfl : w' = w := hu w' hw'
    have hres : residueCard (Kv K w') = residueCard (Qv v) ^ 2 := GlobalTheory.CompanionTheory.NormGauss.card_E hf hord
    have hcont : Continuous (algebraMap (Qv v) (Kv K w')) := continuous_adicCompletionMap v w'
    have hfix := GlobalTheory.CompanionTheory.PiKFUnr.pikf GlobalTheory.CompanionTheory.RwKF.rwkf GlobalTheory.CompanionTheory.NormModulus.wMod
      GlobalTheory.CompanionTheory.UnitNormUnr.normU (Qv v) _ hχc hχ1 (Kv K w') hf hcont σ hσ η hη hχ0 hres
      (localChar c w') (hU w').1 k hk
    have hval : LM.val (LM.ns w' σ η (Set.indicator {x : Kv K w' | x ∈ 𝒪[Kv K w']} 1)) k ξ =
        Set.indicator {x : Kv K w' | x ∈ 𝒪[Kv K w']} (1 : Kv K w' → ℂ) (algebraMap K (Kv K w') ξ) :=
      congrFun hfix _
    rw [hval]
    have hiff : algebraMap K (Kv K w') ξ ∈ {x : Kv K w' | x ∈ 𝒪[Kv K w']} ↔
        ∀ u : PlK K, u.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K u) ξ ∈ 𝒪[Kv K u] := by
      refine ⟨fun h u hv => ?_, fun h => h w' i⟩
      obtain rfl := hu u hv
      exact h
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [Set.indicator_of_mem (hiff.2 h)]; rfl
    · rw [Set.indicator_of_notMem (fun h' => h (hiff.1 h'))]

end GlobalTheory.CompanionTheory.StdSphVal
