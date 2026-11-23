import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoDefs
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AutomorphicArithmetic.DivisorFrames.StdAStdBMemSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFrameBlocksDetAndNegTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement

namespace UpperTheory.StandardPairNonvanishing
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdPairLoc GlobalTheory.StdPairCone MeasureTheory
open scoped Matrix

section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

private theorem std_key (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (hϖ : IsUnif ϖ) (hν : ν = α / β) (h : GL (Fin (a + a')) k) :
    bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') h =
      smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α (stdB ν ϖ c a a') h := by
  rw [bigZetaIntegral_eq, smallP]
  obtain ⟨hdet, hrel⟩ := standardPair_frameBlocks_det_and_neg_transpose a a' h
  obtain ⟨hA0, hA⟩ := bigF_stdA ν ϖ c a a' hϖ
  obtain ⟨hB0, hB⟩ := smallF_stdB (k := k) ν ϖ c a a'
  by_cases h0 : (blk₁ (X0 k (finSumFinEquiv (m := a) (n := a')) * (invT h).val)).det = 0
  · have h0' : (blk₂ (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val)).det = 0 := by rw [← hdet, h0, zero_mul]
    rw [hA0 _ h0, hB0 _ h0']; simp
  · have h0' : (blk₂ (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val)).det ≠ 0 := by
      rw [← hdet]; exact mul_ne_zero h0 h.det_ne_zero
    set g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h0 with hg₁
    set g₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h0' with hg₂
    rw [hA _ g₁ rfl, hB _ g₂ rfl, hrel g₁ g₂ rfl rfl, cball_neg_transpose]
    have hd : gdet g₂ = gdet g₁ * gdet h := Units.ext (by
      simp only [gdet, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, g₁, g₂,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact hdet.symm)
    have hαν : α = ν * β := by rw [hν, div_mul_cancel]
    have e : apow (gdet h) ((Fintype.card (Fin a') : ℂ) / 2) * apow (gdet h) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) =
        apow (gdet h) (-(a : ℂ) / 2) := by
      rw [← apow_add]; congr 1; simp only [Fintype.card_fin]; push_cast; ring
    have e1 : (((ν (gdet g₁ * gdet h))⁻¹ : ℂˣ) : ℂ) = (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * (((ν (gdet h))⁻¹ : ℂˣ) : ℂ) := by
      rw [map_mul, _root_.mul_inv, Units.val_mul]
    have e2 : (α (gdet h) : ℂ) = (ν (gdet h) : ℂ) * (β (gdet h) : ℂ) := by
      rw [hαν, MonoidHom.mul_apply, Units.val_mul]
    have e3 : (ν (gdet h) : ℂ) * (((ν (gdet h))⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hd, e1, apow_mul, e2]
    have key2 : ∀ B V Vi Vhi P1 Pa' PN I : ℂ, V * Vhi = 1 →
        B * (Pa' * PN) * (Vi * P1 * I) = V * B * Pa' * (Vi * Vhi * (P1 * PN) * I) := by
      intro B V Vi Vhi P1 Pa' PN I hV; linear_combination (-(B * Pa' * PN * Vi * P1 * I)) * hV
    rw [← e]
    exact key2 _ _ _ _ _ _ _ _ e3

private theorem stdA_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : stdA ν ϖ c a a' ≠ 0 := by
  intro h
  let X : Matrix (Fin a) (Fin (a + a')) k :=
    Matrix.of fun i j => Fin.addCases (motive := fun _ => k) (fun j => (1 : Matrix (Fin a) (Fin a) k) i j) (fun _ => 0) j
  have e1 : blk₁ X = 1 := by ext i j; simp [X, blk₁]
  have e2 : blk₂ X = 0 := by ext i j; simp [X, blk₂]
  have hX := congrFun h X
  rw [stdA, dif_pos] at hX
  · exact Units.ne_zero _ hX
  · rw [e1, e2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

private theorem stdB_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : stdB ν ϖ c a a' ≠ 0 := by
  intro h
  let X : Matrix (Fin a') (Fin (a + a')) k :=
    Matrix.of fun i j => Fin.addCases (motive := fun _ => k) (fun _ => 0) (fun j => (1 : Matrix (Fin a') (Fin a') k) i j) j
  have e1 : blk₁ X = 0 := by ext i j; simp [X, blk₁]
  have e2 : blk₂ X = 1 := by ext i j; simp [X, blk₂]
  have hX := congrFun h X
  rw [stdB, dif_pos] at hX
  · exact Units.ne_zero _ hX
  · rw [e1, e2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

end

end UpperTheory.StandardPairNonvanishing

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_local_zeta_data_realizing_standard_pair :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
        (Γ : Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a') (v : B.P),
        GlobalTheory.LFun.IsHecke F E X.α → GlobalTheory.LFun.IsHecke F E X.β → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsZetaAt B Γ X Rf v → Γ.M.IsGood B.ψ → Γ.M'.IsGood B.ψ → ∀ c : ℕ,
        ∃ ι ι' φ φ', Γ.M.IsLinW B.ψ (B.τ v) (Γ.V.bas v) (Γ.W.bas v) ι ∧ Γ.M'.IsLinBar B.ψ (B.τ v) (Γ.V'.bas v) (Γ.W.bas v) ι' ∧
          ι (Γ.M.vac v) 0 = 1 ∧ ι' (Γ.M'.vac v) 0 = 1 ∧ φ ∈ GlobalTheory.WeilM.SB _ ∧ φ' ∈ GlobalTheory.WeilM.SB _ ∧
          ι φ = GlobalTheory.StdPairCone.stdA (chrW X.ν (B.τ v)) (unifAt v.1) c a a' ∧
          ι' φ' = GlobalTheory.StdPairCone.stdB (chrW X.ν (B.τ v)) (unifAt v.1) c a a' ∧ Rf.p v φ = Rf.p' v φ' ∧ φ ≠ 0 ∧ φ' ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' Γ X Rf v hα hβ hZ _ _ c
  obtain ⟨ι, ι', hι, hι', hv, hv', hz⟩ := hZ
  letI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv v.1
  haveI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv v.1
  have hν : GlobalTheory.LFun.IsHecke F E X.ν := ⟨hα.1.div' hβ.1, fun x => by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars.ν, MonoidHom.div_apply, hα.2, hβ.2, div_one]⟩
  have h1 := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.ν hν v (B.τ v)).2.1
  have hdiv : chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) := by
    ext x
    simp [chrW, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars.ν, GlobalTheory.LFun.locChar]
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v.1) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v.1)).choose_spec
  obtain ⟨sA, sB⟩ := UpperTheory.stdA_stdB_mem_schwartzBruhat (Fv F v) (chrW X.ν (B.τ v)) (unifAt v.1) hϖ h1 c a a'
  obtain ⟨φ, hφ, eφ⟩ := hι.bij.surjOn sA
  obtain ⟨φ', hφ', eφ'⟩ := hι'.bij.surjOn sB
  refine ⟨ι, ι', φ, φ', hι, hι', ?_, ?_, hφ, hφ', eφ, eφ', (hz φ hφ φ' hφ').2 ?_, ?_, ?_⟩
  · rw [hv, Set.indicator_of_mem (by intro i j; exact zero_mem _)]; rfl
  · rw [hv', Set.indicator_of_mem (by intro i j; exact zero_mem _)]; rfl
  · rw [eφ, eφ']
    funext h
    exact UpperTheory.StandardPairNonvanishing.std_key _ _ _ _ c a a' hϖ hdiv h
  · rintro rfl
    exact UpperTheory.StandardPairNonvanishing.stdA_ne _ _ c a a' (by rw [← eφ, map_zero])
  · rintro rfl
    exact UpperTheory.StandardPairNonvanishing.stdB_ne _ _ c a a' (by rw [← eφ', map_zero])
