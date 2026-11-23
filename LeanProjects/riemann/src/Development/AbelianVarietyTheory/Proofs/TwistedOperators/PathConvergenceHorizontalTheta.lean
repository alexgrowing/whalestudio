import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalFlipOnVolumes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKOContinuousAndRatInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowSchwartzDataIsThetaFunctionLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowCosetVectorsIsLocalThetaVectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftedCuspFormsListedStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowStart

theorem setIntegral_fd_eq {D : D7} (V : HSp D) (μ : Measure (GA D V)) (hμ : μ.IsHaarMeasure) (𝓕 𝓕' : Set (GA D V))
    (h1 : IsFundamentalDomain (GQ V) 𝓕 μ) (h2 : IsFundamentalDomain (GQ V) 𝓕' μ) (f : GA D V → ℂ)
    (hf : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : ∫ g in 𝓕, f g ∂μ = ∫ g in 𝓕', f g ∂μ := by
  haveI := hμ
  exact h1.setIntegral_eq h2 fun γ g => by
    simp only [Subgroup.smul_def, smul_eq_mul]
    exact hf γ γ.2 g

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem IsCuspListed.left {θ : InfFam D} {X : Node} {F : Fn G X} (h : IsCuspListed θ X F) :
    ∀ γ ∈ GQ (G.V X), ∀ g, F (γ * g) = F g := h.1.toIsAutFun.left

theorem measEq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (M M' : Vol G) (X : Node) (K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))), M.IsAt X K → M'.IsAt X K → M.ν X = M'.ν X := GlobalTheory.T.gridVertexMeasure_eq_of_same_normalisation

theorem kerA_right_rat (W : G.Weil) {i : ℕ} (hi : i < D.R.m) {f : Sch G (.right i 0)}
    (hf : IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) f) :
    ∀ γ ∈ GQ (G.V (.grid i 0)), ∀ g h, W.kerA (.right i 0) f (γ * g) h = W.kerA (.right i 0) f g h := by
  intro γ hγ g h
  have H := (GlobalTheory.thetaKO_continuous_and_rat_invariant W.ψ _ _ _ _ (W.om (.chi i 0))
    (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩) f hf).2 1 (Subgroup.one_mem _) γ hγ (negGA _ h) g
  rw [one_mul] at H
  exact H

theorem liftA_right_eq (W : G.Weil) (M M' : Vol G) {i : ℕ} {K : Subgroup (GL (Fin (G.V (.grid i 0)).rank) (Lev.EAf D))}
    (h : M.IsAt (.grid i 0) K) (h' : M'.IsAt (.grid i 0) K) (f : Sch G (.right i 0)) (F : Fn G (.grid i 0))
    (hinv : ∀ γ ∈ GQ (G.V (.grid i 0)), ∀ g x, W.kerA (.right i 0) f (γ * g) x * F (γ * g) = W.kerA (.right i 0) f g x * F g) :
    liftA W M (.right i 0) f F = liftA W M' (.right i 0) f F := by
  funext x
  have e := measEq M M' _ _ h h'
  rw [liftA_apply, liftA_apply]
  have h1 := h.haar_fund
  have h2 := h'.haar_fund
  simp only [Arrow.src] at h1 h2 e ⊢
  rw [e] at h1 ⊢
  exact setIntegral_fd_eq _ _ h2.1 _ _ h1.2 h2.2 _ fun γ hγ g => hinv γ hγ g x

end GlobalTheory.RowStart

namespace GlobalTheory.RowStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem rowCore (W : G.Weil) (M₀ M : Vol G) (ρm : RealMatch W) (t : T) (ρ : G.RealVec) (Φ : G.Datum)
    (hstep : CuspStep W M ρm t)
    (hloc : ∀ (i : Fin D.R.m) (κ : G.CosAt i), ∃ e, IsIdemSum e (locPl G t) ∧
      ∃ φ, IsLocVec W (.chi (i : ℕ) 0) e (W.vac i) φ (W.cosVec i κ))
    (hth : ∀ i : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.datum ρ Φ i))
    (h₀ : M₀.IsRow) (h₁ : M.IsRow) (u : Fn G (.grid 0 0)) (hu : IsCuspListed W.θ (.grid 0 0) u) :
    ∀ n (hn : n ≤ D.R.m), PathConv W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u ∧
      IsCuspListed W.θ (.grid n 0) (liftP W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u) ∧
      liftP W M₀ (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u =
        liftP W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE hn i)) u
  | 0, _ => ⟨trivial, hu, rfl⟩
  | n + 1, hn => by
    obtain ⟨c, hc, e⟩ := rowCore W M₀ M ρm t ρ Φ hstep hloc hth h₀ h₁ u hu n (by omega)
    set F := liftP W M (rowPath T 0 n) (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE (by omega) i)) u with hF
    let k : Fin D.R.m := ⟨n, by omega⟩
    obtain ⟨e', he', φ, hφ⟩ := hloc k (Φ k)
    have hv : IsLocVec W (Arrow.right n 0 : Arrow T).pair e' (vacOf ρm (.right n 0)) φ (W.cosVec n (Φ k)) := by
      show IsLocVec W (.chi n 0) e' (ρm.vX n 0) φ (W.cosVec n (Φ k))
      rw [ρm.vX_row n]; exact hφ
    obtain ⟨hconv, hcusp⟩ := hstep (.right n 0) (Or.inl ⟨n, 0, by omega, Nat.zero_le _, rfl⟩) e' he' φ _ hv (ρ k) F hc
    refine ⟨⟨c, hconv⟩, hcusp, ?_⟩
    show liftA W M₀ (.right n 0) (W.datum ρ Φ k) (liftP W M₀ (rowPath T 0 n)
        (rowFam 0 n fun i : Fin n => W.datum ρ Φ (Fin.castLE (by omega) i)) u) = liftA W M (.right n 0) (W.datum ρ Φ k) F
    rw [e]
    refine liftA_right_eq W M₀ M (h₀.row n (by omega)) (h₁.row n (by omega)) _ F fun γ hγ g x => ?_
    rw [kerA_right_rat W (by omega) (hth k) γ hγ g x, IsCuspListed.left hc γ hγ g]

end GlobalTheory.RowStart

namespace GlobalTheory.RowStart

theorem rowStart : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (Φ : ch.G.Datum) (M : Vol ch.G), M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = liftP ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) := by
  intro hP hLC
  refine ((cuspStep_big hLC hP).and ((GlobalTheory.T.lifted_cusp_forms_listed hP hLC).and (GlobalTheory.T.firstRow_cosetVectors_isLocalThetaVector.and GlobalTheory.T.firstRowSchwartzData_isThetaFunction_largeDepth))).imp fun CF0 h ε CF hC => ?_
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc t Φ M hM y => ?_⟩
  obtain ⟨hstep, hcusp, hloc, hth⟩ := h D large₂ e hx Γ Pl0 T A Ks R F s ch hch hsc
  have H := rowCore ch.W ch.M M ch.rm t ch.ρ Φ (hstep t M hM) (hloc t) (fun i => hth Φ i) hch.vol hM.isRow
    (ch.cv.lift t y) (hcusp t y) D.R.m le_rfl
  exact ⟨H.1, H.2.2⟩

end GlobalTheory.RowStart
