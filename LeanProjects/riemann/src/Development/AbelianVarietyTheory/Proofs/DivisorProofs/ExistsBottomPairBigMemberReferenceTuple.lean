import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilOfVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongLevRelIndexLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBlockCongruenceLevelSubgroupIffStabilizerEntr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetLeftTransversalOfRelIndexNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransversalLeftTranslateInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilFixesCosetVectorCongruentOneModIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaDatumEigenvectorBlockLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaDatumPresentationLevelNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqUnderOfIdemAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeOfIsIdemAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeUNuInvEqOneOfCong
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

variable {D : D7}

theorem om_sum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (g : GA D a) (g' : GA D d) {ι : Type}
    (s : Finset ι) (F : ι → VC D a d → ℂ) (hF : ∀ i ∈ s, F i ∈ TT D (tor0 D ⊤ δ) a d) :
    W.Om g g' (∑ i ∈ s, F i) = ∑ i ∈ s, W.Om g g' (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : VC D a d → ℂ) ∈ TT D (tor0 D ⊤ δ) a d := (GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).zero_mem
    have := W.smul g g' 0 0 h0
    simpa using this
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      W.add g g' _ (hF x (Finset.mem_insert_self _ _)) _
        ((GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).sum_mem fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

theorem exists_bottom_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc), IsCoprime (condE G.pl) D.host.𝔟 → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χβ : HeckeU D (botBig D i j)), (∀ x, χβ.f x = (betaH G i j)⁻¹.1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl), P.a = botBig D i j ∧ P.d = botBig D i j + botSmall D i j ∧ HasChars P (betaH G i j)⁻¹ (nuH G μ₀ i j)⁻¹ ∧ IsStdDatum P (condE G.pl) 0 ∧ IsBlockLevel P (condE G.pl) (botBig D i j) := by
  intro D T L sc μ₀ hL G hb δ t0 hc ht i j χβ hβ χν hν hn
  have hd : Even (botBig D i j + botSmall D i j) := by
    obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
    exact ⟨halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  have had : botBig D i j ≤ botBig D i j + botSmall D i j := Nat.le_add_right _ _
  obtain ⟨e0, vac, h0⟩ := GlobalTheory.Vacuum.exists_vacuum D ⊤ δ hc t0 ht _ _ (hd.mul_left (botBig D i j))
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := GlobalTheory.FinWeil.exists_weil_of_vacuum D ⊤ δ hc _ _ e0 vac.1 h0 χβ χν
  have hm : condE G.pl ≠ ⊥ := condE_ne_bot _
  have hcop := GlobalTheory.FunObj.StdDatum.condE_isCoprime_conj G.pl
  have hnu : ∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) → W.chV'.f u = 1 := by
    rw [hW2]; exact GlobalTheory.FunObj.SqNum.heckeU_nuInv_eq_one_of_cong hL G i j χν hν
  obtain ⟨hi0, -⟩ := GlobalTheory.congLev_relIndex_le D (condE G.pl) hm (botBig D i j)
  obtain ⟨R, hR1, hR2'⟩ := GlobalTheory.exists_finset_leftTransversal_of_relIndex_ne_zero (intG D (botBig D i j)) (congLev D (condE G.pl) (botBig D i j)) (congLev_le _ _) hi0
  have hR2 : ∀ k ∈ intG D (botBig D i j), ∃! r, r ∈ R ∧ CongOne D (condE G.pl) (r⁻¹ * k) := by
    intro k hk
    obtain ⟨r, ⟨hr, hrk⟩, hu⟩ := hR2' k hk
    refine ⟨r, ⟨hr, ((GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hrk).2⟩, fun r' ⟨hr', h'⟩ => hu r' ⟨hr', (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).2
      ⟨mul_mem (inv_mem (hR1 r' hr')) hk, h'⟩⟩⟩
  have hcv := GlobalTheory.FunObj.CosetTT.cosetV_mem_TT D δ hc (condE G.pl) hm 0 _ _ e0 vac.1
  have hfix : ∀ k ∈ intG D (botBig D i j), W.Om k 1 (stdSum W (condE G.pl) 0 R) = stdSum W (condE G.pl) 0 R := by
    intro k hk
    unfold stdSum
    rw [om_sum W k 1 R _ fun r _ => W.maps _ _ _ hcv]
    have e1 : ∀ r, W.Om k 1 (W.Om r 1 (cosetV D δ (condE G.pl) 0 _ _ e0)) = W.Om (k * r) 1 (cosetV D δ (condE G.pl) 0 _ _ e0) := by
      intro r
      have := W.mul k r 1 1 _ hcv
      rw [mul_one] at this
      exact this.symm
    simp_rw [e1]
    refine GlobalTheory.sum_transversal_left_translate_invariant (intG D (botBig D i j)) (congLev D (condE G.pl) (botBig D i j)) R
      (fun g => W.Om g 1 (cosetV D δ (condE G.pl) 0 _ _ e0)) hR1 hR2' (fun r _ c hc' => ?_) k hk
    have := W.mul r c 1 1 _ hcv
    rw [mul_one] at this
    obtain ⟨hc1, hc2⟩ := (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hc'
    rw [this, GlobalTheory.T.weil_fixes_cosetVector_congruent_one_mod_ideal D δ t0 hc e0 vac W (condE G.pl) hm hcop hnu 0 (by omega) c hc1 hc2]
  have hle : congLev D (condE G.pl) (botBig D i j + botSmall D i j) ≤
      blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hk
    refine (GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff _ _ _ _ _).2 ⟨hk1, fun a b hb ha => ?_⟩
    have hab : a ≠ b := fun e => by rw [e] at ha; omega
    have := hk2 a b
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hab, sub_zero] at this
  obtain ⟨hj0, hj1⟩ := GlobalTheory.congLev_relIndex_le D (condE G.pl) hm (botBig D i j + botSmall D i j)
  have hQ : 0 < levQ G.pl := by
    rw [← GlobalTheory.FunObj.NormLevel.absNorm_condE]; exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hm)
  let n : D.what₂.Tau → ℕ := fun τ => ((χν.n τ - (botBig D i j + botSmall D i j : ℕ)) / 2).toNat
  have hwt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by
    intro τ
    rw [hW4, hW2, one_mul]
    obtain ⟨r, hr⟩ := χν.par τ
    have h1 := hn τ
    have h2 : ((χν.n τ - (botBig D i j + botSmall D i j : ℕ)) / 2) = r := by omega
    simp only [n, h2]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hpres : Pres D ⊤ δ (levQ G.pl) e0 (stdSum W (condE G.pl) 0 R) := by
    rw [← GlobalTheory.FunObj.NormLevel.absNorm_condE]
    exact GlobalTheory.T.standardTheta_datum_presentation_level_norm D δ t0 hc e0 vac had W _ hm hcop hb hnu R hR1 hR2 hfix
  have hidx_ne : (blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)).relIndex
      (intG D (botBig D i j + botSmall D i j)) ≠ 0 := fun h =>
    hj0 (Subgroup.relIndex_eq_zero_of_le_left hle h)
  have hidx_le : (blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)).relIndex
      (intG D (botBig D i j + botSmall D i j)) ≤ levQ G.pl ^ ((botBig D i j + botSmall D i j) ^ 2 + 4) := by
    refine (Subgroup.relIndex_le_of_le_left hle hj0).trans (hj1.trans ?_)
    rw [GlobalTheory.FunObj.NormLevel.absNorm_condE]
    exact Nat.pow_le_pow_right hQ (by omega)
  have heig := GlobalTheory.T.standardThetaDatum_eigenvector_blockLevel D δ t0 hc e0 vac had W _ hm hcop hnu R hR1 hR2 hfix
  let P : Pair D ⊤ δ t0 (levQ G.pl) :=
    { crv := hc
      pt0 := ht
      a := botBig D i j
      d := botBig D i j + botSmall D i j
      a_le := had
      d_even := hd
      e0 := e0
      vac := vac
      W := W
      n := n
      wt := hwt
      F := stdSum W (condE G.pl) 0 R
      pres := hpres
      fix := hfix
      J := blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)
      J_le := blockLev_le _ _ _
      idx_ne := hidx_ne
      idx_le := hidx_le
      eig := heig }
  refine ⟨P, rfl, rfl, ⟨fun x => ?_, fun x => ?_⟩, ⟨R, hR1, hR2, rfl⟩, fun h => GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff _ _ _ _ h⟩
  · show W.chV.f x ^ W.ep = _
    rw [hW1, hW3, zpow_one, hβ]
  · show W.chV'.f x ^ W.ep' = _
    rw [hW2, hW4, zpow_one, hν]

end GlobalTheory.FunObj.StdDatum

end
