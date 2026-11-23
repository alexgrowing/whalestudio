import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilOfVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongOneInvMulIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMulMemHatId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqOfTwoOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondESupConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdSumFixEig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorConjIsThetaSomeLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorFixedPrincipalCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorBlockLevelUnimodularEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModulusStandardThetaPresentationStatement

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BotPairSmall

open GlobalTheory.BotPairSmall in

theorem smallPair_exists : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc), IsCoprime (D.host.conj • condE G.pl) D.host.𝔟 → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χα : HeckeU D (botSmall D i j)), (∀ x, χα.f x = (alphaH L μ₀ i j).1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl), P'.a = botSmall D i j ∧ P'.d = botBig D i j + botSmall D i j ∧ HasChars P' (alphaH L μ₀ i j) (nuH G μ₀ i j)⁻¹ ∧ IsStdDatum P' (D.host.conj • condE G.pl) (botBig D i j) ∧ IsBlockLevel P' (condE G.pl) (botBig D i j) := by
  intro D T L sc μ₀ hL G hb δ t0 hc ht i j χα hα χν hν hn
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  have hd : Even (botBig D i j + botSmall D i j) :=
    ⟨halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  obtain ⟨e0, hv, h0⟩ := GlobalTheory.Vacuum.exists_vacuum D ⊤ δ hc t0 ht (botSmall D i j) (botBig D i j + botSmall D i j)
    (hd.mul_left _)
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := GlobalTheory.FinWeil.exists_weil_of_vacuum D ⊤ δ hc _ _ e0 hv.1 h0 χα χν
  have hm := condE_ne_bot G.pl
  have hcop := GlobalTheory.FunObj.SqNum.condE_sup_conj G.pl
  have hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) →
      W.chV'.f u = 1 := by
    intro u hu h
    rw [hW2, hν, GlobalTheory.BotPairSmall.CondNu.nuH_inv_eq_one_of_cong hL G i j u hu h]
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.CongReps.exists_reps D (botSmall D i j) _ (conj_smul_ne_bot D hm)
  have hTT := GlobalTheory.BotPairSmall.cvec_conj_mem_TT D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl
  have hK := GlobalTheory.T.weilAction_cosetVector_fixed_principalCongruence D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl
  have hS := GlobalTheory.StdSumFix.stdSum_fix_eig D δ _ _ e0 W _ _ hTT hK R hR1 hR2
  have hN := GlobalTheory.ModulusNorm.absNorm_condE G.pl
  have hidx := GlobalTheory.BotPairSmall.blockJ_relIndex D (condE G.pl) hm (botBig D i j) (botBig D i j + botSmall D i j)
  have hQ : 1 ≤ levQ G.pl := by
    rw [← hN]; exact Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 hm)
  have heig : ∀ h ∈ blockJ D (condE G.pl) (botBig D i j) (botBig D i j + botSmall D i j), ∃ c : ℂ, ‖c‖ = 1 ∧
      W.Om 1 h (∑ r ∈ R, W.Om r 1 (cvec D δ (D.host.conj • condE G.pl) (botBig D i j) (botSmall D i j)
        (botBig D i j + botSmall D i j) e0)) = c • ∑ r ∈ R, W.Om r 1 (cvec D δ (D.host.conj • condE G.pl) (botBig D i j)
          (botSmall D i j) (botBig D i j + botSmall D i j) e0) := by
    intro h hh
    obtain ⟨k, hk, c, hc1, e⟩ := GlobalTheory.T.cosetVector_blockLevel_unimodular_eigen D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl h hh
    exact ⟨c, hc1, hS.2 h k c hk e⟩
  refine ⟨{
      crv := hc, pt0 := ht, a := botSmall D i j, d := botBig D i j + botSmall D i j, a_le := Nat.le_add_left _ _,
      d_even := hd, e0 := e0, vac := hv, W := W,
      n := fun τ => ((χν.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ)) / 2).toNat, wt := ?_,
      F := ∑ r ∈ R, W.Om r 1 (cvec D δ (D.host.conj • condE G.pl) (botBig D i j) (botSmall D i j)
      (botBig D i j + botSmall D i j) e0),
      pres := GlobalTheory.T.conjugateModulus_standardTheta_presentation D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hb hcond (botBig D i j) rfl _ hN R hR1 hR2,
      fix := hS.1,
      J := blockJ D (condE G.pl) (botBig D i j) (botBig D i j + botSmall D i j),
      J_le := blockJ_le _ _ _ _,
      idx_ne := hidx.1,
      idx_le := hidx.2.trans (by rw [hN]; exact Nat.pow_le_pow_right hQ (by omega)),
      eig := heig }, rfl, rfl, ⟨fun x => ?_, fun x => ?_⟩, ⟨R, hR1, hR2, rfl⟩,
    fun h => GlobalTheory.BotPairSmall.blockJ_mem_iff_blockSet _ _ _ _ h⟩
  · intro τ
    show 2 * (((χν.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ)) / 2).toNat : ℤ) = W.ep' * W.chV'.n τ - _
    rw [hW4, hW2]
    obtain ⟨r, hr⟩ := χν.par τ
    have := hn τ
    omega
  · show W.chV.f x ^ W.ep = _
    rw [hW3, zpow_one, hW1, hα]
  · show W.chV'.f x ^ W.ep' = _
    rw [hW4, zpow_one, hW2, hν]

end GlobalTheory.BotPairSmall
