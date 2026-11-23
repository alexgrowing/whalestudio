import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatCorrSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeCorrespondingLatticesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrespondingLatticesBlockLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveFrameMatrixTransportIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaFunctionTransportLocalFieldIsoStatement

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

namespace GlobalTheory.PureMatch.Transport
open GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport
open scoped Pointwise

section General
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
  [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem corr_smul_of (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) (c : kˣ) (c₂ : k'ˣ) (hc : valuation k' (j c) = valuation k' (c₂ : k')) :
    LatCorr j cD (c • Λ) (c₂ • Λ₂) := latCorr_smul hj cD h c c₂ hc

theorem corr_dual_of (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) : LatCorr j cD (dualLat Λ) (dualLat Λ₂) := GlobalTheory.T.dualLattice_correspondingLattices hj cD h

theorem primFrame_corr (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) :
    IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := GlobalTheory.T.isPrimitiveFrame_matrixTransport_iff hj rA cD h Z

theorem corr_blockLat_of (hj : IsLocIso j) (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂)
    (e : ℕ) (P : Finset D) (P₂ : Finset D₂) (hP : ∀ c, c ∈ P₂ ↔ cD c ∈ P) :
    LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := GlobalTheory.T.correspondingLattices_blockLattice hj cD hϖ hϖ₂ e P P₂ hP

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

theorem fFun_corr (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D)
    (μ₂ : MeasureTheory.Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D)
    (hσ : ∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ)
    (hν : ∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k) :
    fFun μ₂ σ₂ ν₂ Ψ (trM j rA cD Z) = fFun (pullMeas hj rA' μ₂) σ ν (fun Y => Ψ (trM j rA' cD Y)) Z :=
  GlobalTheory.T.zetaFunction_transport_localFieldIso hj rA rA' cD μ₂ σ₂ σ hσ ν₂ ν hν Ψ Z

end General
end GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch.Transport
open GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport
open scoped Pointwise

section General
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
  [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem latCorr_latA (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂) (e : ℕ) :
    LatCorr j cD (latA ϖ e Λ) (latA ϖ₂ e Λ₂) := by
  refine corr_smul_of hj cD (corr_dual_of hj cD h) _ _ ?_
  have h1 : valuation k' (j ϖ) = valuation k' (ϖ₂ : k') := (isUnif_map hj hϖ).trans hϖ₂.symm
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow, h1]

theorem trM_mem_matLat (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) : trM j rA cD Z ∈ matLat A₂ Λ₂ ↔ Z ∈ matLat A Λ := by
  rw [mem_matLat, mem_matLat]
  refine ⟨fun H a => ?_, fun H r => (h (Z.row (rA r))).2 (H _)⟩
  obtain ⟨r, rfl⟩ := rA.surjective a
  exact (h (Z.row (rA r))).1 (H r)

theorem hasDepth_trM (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ)
    (hϖ₂ : IsUnif ϖ₂) (e : ℕ) (Ξ : Matrix A D k → ℂ) (hΞ : HasDepth ϖ e Λ Ξ) :
    HasDepth ϖ₂ e Λ₂ (fun Y => Ξ (trM j.symm rA.symm cD.symm Y)) := by
  have h1 : valuation k' (j ϖ) = valuation k' (ϖ₂ : k') := (isUnif_map hj hϖ).trans hϖ₂.symm
  have hs : LatCorr j cD (ϖ ^ e • Λ) (ϖ₂ ^ e • Λ₂) := corr_smul_of hj cD h _ _ (by
    simp only [Units.val_pow_eq_pow_val, map_pow]; rw [h1])
  refine ⟨fun Y hY => hΞ.1 _ fun hZ => hY ?_, fun Y W hW => ?_⟩
  · rw [← trM_trM_symm j rA cD Y]; exact (trM_mem_matLat rA cD h _).2 hZ
  · have hW' : trM j.symm rA.symm cD.symm W ∈ matLat A (ϖ ^ e • Λ) := by
      rw [← trM_mem_matLat rA cD hs, trM_trM_symm]; exact hW
    show Ξ (trM j.symm rA.symm cD.symm (Y + W)) = Ξ (trM j.symm rA.symm cD.symm Y)
    rw [show trM j.symm rA.symm cD.symm (Y + W) = trM j.symm rA.symm cD.symm Y + trM j.symm rA.symm cD.symm W by
      ext r c; simp]
    exact hΞ.2 _ _ hW'

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

theorem phiA_trM (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D)
    (μ₂ : MeasureTheory.Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D)
    (hσ : ∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ)
    (hν : ∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂) (e : ℕ)
    {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂)
    (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k) :
    phiA μ₂ σ₂ ν₂ ϖ₂ e Λ₂ Ψ (trM j rA cD Z) =
      phiA (pullMeas hj rA' μ₂) σ ν ϖ e Λ (fun Y => Ψ (trM j rA' cD Y)) Z := by
  classical
  unfold phiA
  rw [primFrame_corr hj rA cD (latCorr_latA hj cD h hϖ hϖ₂ e), fFun_corr hj rA rA' cD μ₂ σ₂ σ hσ ν₂ ν hν]

end General
end GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch
open GlobalTheory.PureMatch.Transport GlobalTheory.FlipMatch

theorem mem_one_block_iff {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T)
    (w : Pl D.host.E) {i j : Fin D.R.m} (e : Num G i j) (c : (locGrid G t w).Cols i j) :
    c ∈ Assignment.one.block _ _ ↔ GlobalTheory.SquareFlipReach.colE t w e c ∈ blockV e := by
  rcases c with c | c
  · simp [Assignment.block, blockV, GlobalTheory.SquareFlipReach.colE]
  · simp [Assignment.block, blockV, GlobalTheory.SquareFlipReach.colE]

theorem phiA_transport_split_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E) (hw : w ∈ locPl G t) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ = w → ∀ n : ℕ,
    ∃ (μ : @Measure (GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)) Units.instMeasurableSpace)
      (_ : @Measure.IsHaarMeasure _ _ _ Units.instMeasurableSpace μ)
      (σ' : Fin (spW G i j).rank ⊕ Fin (spW₁ G i j).rank ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank)),
      (∀ (Ψ : Matrix (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) Z,
        phiA (haarVol ((givenLevel G t w ((i : ℕ), (j : ℕ))).map invT)) (stdSplit ((locGrid G t w).rank_square i j))
          ((locGrid G t w).nu i j) (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ψ (trA t hv e Z) =
        phiA μ σ' (((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n
          (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) (fun Y => Ψ (trB t hv e Y)) Z) ∧
      ∀ Ξ, HasDepth (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) Ξ →
        ∃ Ξ', HasDepth (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ξ' ∧ ∀ Y, Ξ' (trB t hv e Y) = Ξ Y := by
  intro D T L sc G μ₀ hL t i j e w hw v hv τ hτ n
  subst hτ
  have hjj := isLocIso_complEquiv τ hv
  have hO := GivenAdm.givenLevel_open (G := G) hL hw ((i : ℕ), (j : ℕ))
  have hO' := isOpen_map_invT hO.1 hO.2
  haveI := isHaarMeasure_haarVol hO'.1 hO'.2
  have hϖv : IsUnif (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec
  have hc := corr_blockLat_of hjj (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) hϖv (isUnif_unifAt _) n (blockV e)
      (Assignment.one.block _ _) (mem_one_block_iff t _ e)
  refine ⟨pullMeas hjj (rowB t (splitPrime τ) i j)
      (haarVol ((givenLevel G t (splitPrime τ) ((i : ℕ), (j : ℕ))).map invT)), inferInstance,
    (Equiv.sumCongr (GlobalTheory.SquareFlipReach.rowE t (splitPrime τ) i j).symm (rowB t (splitPrime τ) i j).symm).trans
      ((stdSplit ((locGrid G t (splitPrime τ)).rank_square i j)).trans (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e)),
    fun Ψ Z => ?_, fun Ξ hΞ => ?_⟩
  · exact phiA_trM hjj (GlobalTheory.SquareFlipReach.rowE t (splitPrime τ) i j) (rowB t (splitPrime τ) i j)
      (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) _ _ _ (fun s => by simp) _ _ (fun x => rfl) hϖv
      (isUnif_unifAt _) n hc Ψ Z
  · exact ⟨_, hasDepth_trM hjj (rowB t (splitPrime τ) i j) (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) hc hϖv
      (isUnif_unifAt _) n Ξ hΞ, fun Y => by
        show Ξ (trM _ _ _ (trM (GlobalTheory.LFun.SplitTie.complEquiv τ hv) (rowB t (splitPrime τ) i j)
          (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) Y)) = Ξ Y
        rw [trM_symm_trM]⟩

end GlobalTheory.PureMatch
