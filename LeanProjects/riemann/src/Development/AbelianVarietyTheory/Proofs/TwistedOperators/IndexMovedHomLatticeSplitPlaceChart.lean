import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLatHatIffOfSupport
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMovedHomLatticeEqProdHalvesSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppAtUnitaryGroupLocalToAdelicEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemAtConjOfOtherPrimeOverSplitStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexHalfActionSplitPlaceFramesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesCartanDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceChartFramesConjMaximalCompactStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

namespace GlobalTheory.SplitIdx

theorem half_index : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → (halfLat S T ε).relIndex ((halfLat S T ε).map (actL S T (embV T v (e.symm (k₁ * t * k₂))))) = qV D.host.E w ^ (S.rank * (∑ i, max (-d i) 0).toNat) := by
  intro D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ ε hε
  obtain ⟨φ, hφ, ⟨BS, hBS⟩, BT, hBT, ψ, hψ, hq, κ, hκ, hco⟩ := GlobalTheory.T.splitPlace_chart_frames_conj_maximalCompact D S T v w h hs e he ε hε
  rw [GlobalTheory.T.relIndex_half_action_splitPlace_frames D S T v φ ε hφ BS BT hBS hBT, hco, ← hq]
  have hback : ∀ x : GL (Fin T.rank) (w.adicCompletion D.host.E),
      GlobalTheory.LFun.SplitTie.glEquiv T.rank ψ
        (Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x) = x := by
    intro x
    ext i j
    simp [GlobalTheory.LFun.SplitTie.glEquiv]
  have hK : ∀ x ∈ KGL w T.rank,
      Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x ∈ KGL v T.rank := by
    intro x hx
    rw [GlobalTheory.LFun.SplitTie.mem_KGL_iff hψ, hback]
    exact hx
  have hunif : IsUnifV D.host.F v (ψ.symm ϖ) := by
    have h1 := hψ (ψ.symm ϖ)
    rw [RingEquiv.apply_symm_apply] at h1
    show Valued.v _ = _
    rw [← h1]
    exact hϖ
  have hdiag : (Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) t).1 =
      Matrix.diagonal (fun i => ψ.symm ϖ ^ d i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [ht, map_zpow₀]
    · simp [ht, Matrix.diagonal_apply, hij]
  have hsplit : ∀ a b c : GL (Fin T.rank) (w.adicCompletion D.host.E),
      κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) (a * b * c) * κ =
        (κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) a) *
          Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) b *
          (Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) c * κ) := by
    intro a b c
    simp only [map_mul, mul_assoc]
  rw [hsplit]
  exact GlobalTheory.T.relIndex_integralMatrices_cartanDouble_coset v T.rank S.rank (ψ.symm ϖ) hunif d _ hdiag _ (mul_mem (inv_mem hκ) (hK k₁ hk₁)) _
    (mul_mem (hK k₂ hk₂) hκ)

theorem index_moved_split : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v (e.symm (k₁ * t * k₂))))) = qV D.host.E w ^ (S.rank * (∑ i, |d i|).toNat) := by
  intro D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  obtain ⟨τ, hτ⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.AdelicU.isCMExt_host D) hs h
  obtain ⟨ε, hε, -⟩ := GlobalTheory.EmbChart.exists_isIdemAt_chart (D := D) τ
  rw [hτ] at hε
  obtain ⟨w', hne, hunder, -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place (GlobalTheory.AdelicU.isCMExt_host D) h hs
  have h' : w'.under (𝓞 D.host.F) = v := (hunder w').2 (Or.inr rfl)
  obtain ⟨c, hc, hq', -, he'⟩ := GlobalTheory.LFun.ConjPlace.exists_conj_chart (GlobalTheory.AdelicU.isCMExt_host D)
    (GlobalTheory.Mem.VolExists.isHermND D.sp.cm T) (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D T v) hne h h' he
  have hε' := GlobalTheory.T.isIdemAt_conj_of_other_prime_over_split D v w w' hne h h' ε hε
  rw [GlobalTheory.T.relIndex_movedHomLattice_eq_prod_halves_splitPlace D S T ε hε.1 _ (GlobalTheory.T.suppAt_unitaryGroupLocalToAdelicEmbedding D T v w h ε hε (e.symm (k₁ * t * k₂))),
    half_index D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ ε hε]
  have hO := GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff c hc
  have hk : ∀ k ∈ KGL w T.rank, GlobalTheory.LFun.ConjPlace.invT c T.rank k ∈ KGL w' T.rank := fun k hk =>
    (GlobalTheory.LFun.ConjPlace.mem_iff_invT c hO k).1 hk
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    simp [IsUnifV] at hϖ
  have hmul : t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i)) = 1 := by
    rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
  have hinv : (t⁻¹).1 = Matrix.diagonal (fun i => ϖ ^ (-d i)) := Units.inv_eq_of_mul_eq_one_right hmul
  have hdiag : (GlobalTheory.LFun.ConjPlace.invT c T.rank t).1 = Matrix.diagonal (fun i => c ϖ ^ (-d i)) := by
    ext i j
    rw [GlobalTheory.LFun.ConjPlace.invT_val, hinv]
    by_cases hij : i = j
    · subst hij
      simp [map_zpow₀]
    · simp [Matrix.diagonal_apply, hij, Ne.symm hij]
  have hunif : IsUnifV D.host.E w' (c ϖ) := by
    show Valued.v (c ϖ) = _
    rw [hc]
    exact hϖ
  have hsym : e.symm (k₁ * t * k₂) = (e.trans (GlobalTheory.LFun.ConjPlace.invT c T.rank)).symm
      (GlobalTheory.LFun.ConjPlace.invT c T.rank k₁ * GlobalTheory.LFun.ConjPlace.invT c T.rank t *
        GlobalTheory.LFun.ConjPlace.invT c T.rank k₂) := by
    rw [MulEquiv.symm_trans_apply, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply]
  have hconj := half_index D S T v w' h' hs _ he' (c ϖ) hunif (fun i => -d i) _ hdiag _ (hk k₁ hk₁) _ (hk k₂ hk₂)
    (cA D ε) hε'
  rw [← hsym] at hconj
  rw [hconj, hq']
  simp only [neg_neg]
  rw [← pow_add, ← mul_add]
  have hA : 0 ≤ ∑ i, max (-d i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hB : 0 ≤ ∑ i, max (d i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
  rw [← Int.toNat_add hA hB, ← Finset.sum_add_distrib]
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm]
  exact max_zero_add_max_neg_zero_eq_abs_self (d i)

end GlobalTheory.SplitIdx

end
