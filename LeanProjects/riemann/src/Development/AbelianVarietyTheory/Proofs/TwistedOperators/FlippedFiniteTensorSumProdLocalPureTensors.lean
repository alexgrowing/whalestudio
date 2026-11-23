import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFlipStageIsTensorPlaceDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumPureTensorOfIsTensorDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMovedTensorFinsetSumLinearStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowColumnProductDataHaveVectorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedProductFunctionEqOfLocalIdentityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorLocalIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LocAsm

theorem continuous_psiAt_locPl : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T), ∀ w ∈ locPl ch.G t, Continuous (psiAt ch.W w) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t w hw
  have hL := s.core.lev
  have hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
    obtain ⟨⟨P, -, -⟩, -⟩ := s.size
    have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
      UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
    exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde (hch.guard t)).1 w hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  exact (hg.square 0 hm 0 hm).cond.continuous

theorem flipFin_productExpansion : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ConLin ch → ∀ (t : T) (Φ : ch.G.Datum) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ), IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (β : CosFam ch.G t) (e : AE D), IsIdemSum e (locPl ch.G t) → ∃ (α : Type) (SA : Finset α) (xA : α → ℂ) (φ : α → (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)) (fd : α → SchDown ch.G t) (fr : α → SchRow ch.G), (∀ a ∈ SA, ∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ a w b)) ∧ (∀ a ∈ SA, (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ a w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd a j)) ∧ (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ a w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr a i))) ∧ (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (u j)) → (∀ i, IsHalf e (y i)) → ∏ w, (ch.S.term t Φ β w).datum (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = ∑ a ∈ SA, xA a * ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φ a w))) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y)) ∧ ∀ (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (u : ColPt ch.G) (y : RowPt ch.G), (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) h) d.1 u y) = ∑ a ∈ SA, xA a * evT (conAt ch.W hM (fockD ch.W t (fd a) P) h) (fr a) u y := by
  have H := (isTensor_flips_take.and GlobalTheory.T.last_row_column_product_data_have_vectors).and (GlobalTheory.T.unfoldedProductFunction_eq_of_local_identity.and continuous_psiAt_locPl)
  refine big_mono ?_ H
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h
  obtain ⟨⟨hTen, hVec⟩, hCon, hψ⟩ := h
  intro hCL t Φ τ hFF β e he
  have hexp : ∀ w : locPl ch.G t, ∃ (n : ℕ) (x : Fin n → ℂ) (φ : Fin n → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ i, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ i b)) ∧ ∀ z, Tflip ch.W ch.S.B t Φ w.1 z = ∑ i, x i * (locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φ i) z := by
    intro w
    have h1 := hTen t Φ w.1 w.2 (D.R.m ^ 2) le_rfl
    rw [List.take_of_length_le (le_of_eq (canFlip_flipOrder D.R.m).2.1)] at h1
    have hp := (flipStage_path_level t w.1 ch.S.B ch.W Φ).1
    change (locGrid ch.G t w.1).IsTensor _ _ (flipStage t w.1 ch.S.B ch.W Φ).path (Tflip ch.W ch.S.B t Φ w.1) at h1
    rw [hp] at h1
    exact GlobalTheory.T.exists_sum_pureTensor_of_isTensor_depth _ _ (isUnif_unifAt w.1) _ _ _ h1
  choose n xw φw hnat hTeq using hexp
  have hv := fun a : (∀ w : locPl ch.G t, Fin (n w)) => hVec t e he (fun w => φw w (a w)) (fun w b hb => hnat w (a w) b hb)
  choose fd hfd using fun a j => (hv a).1 j
  choose fr hfr using fun a i => (hv a).2 i
  refine ⟨∀ w : locPl ch.G t, Fin (n w), Fintype.piFinset (fun w => Finset.univ), fun a => ∏ w, xw w (a w), fun a w => φw w (a w), fd, fr, ?_, ?_, ?_, ?_⟩
  · intro a _ w b hb
    exact hnat w (a w) b hb
  · intro a _
    exact ⟨hfd a, hfr a⟩
  · intro u y _ _
    have key : ∀ w : locPl ch.G t, (ch.S.term t Φ β w).datum (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = ∑ i, xw w i * flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φw w i))) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) := by
      intro w
      haveI := (isUnitVol_unitVol w.1).1
      have hT : Tflip ch.W ch.S.B t Φ w.1 = fun z => ∑ i ∈ Finset.univ, xw w i * (locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φw w i) z := funext (hTeq w)
      show flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) (Tflip ch.W ch.S.B t Φ w.1)) _ _ = _
      rw [hT]
      exact GlobalTheory.T.flatTensor_movedTensor_finset_sum_linear _ one_le_sLen _ _ (hψ t w.1 w.2) (unifAt w.1) (depthAt ch.G w.1) _ _ _ _ _ (fun i _ => (locGrid ch.G t w.1).isTensor_pureTensor _ _ _ _ (hnat w i)) _ _
    simp only [key]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.prod_mul_distrib]
  · obtain ⟨e', he', φ', hφ', hid⟩ := hFF
    obtain rfl := GlobalTheory.IdemSumUniq.idemSum_unique _ _ _ he he'
    intro M hM P h u y
    refine hCon hCL t e he τ φ' hφ' (∀ w : locPl ch.G t, Fin (n w)) (Fintype.piFinset fun w => Finset.univ) (fun a => ∏ w, xw w (a w)) (fun a i => (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0)) (fun a j => (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0)) fr fd ?_ ?_ M hM P h u y
    · intro a _
      exact ⟨hfr a, hfd a⟩
    · exact GlobalTheory.T.flippedFiniteTensor_local_identity ch t Φ e τ φ' hφ' hid n xw φw hTeq

end GlobalTheory.LocAsm

end
