import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeUNuInvEqOneOfCong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModTSupConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulLeOfIsConjPl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridConductorIdealCMIsCoprimeHalfDifferentStatement

noncomputable section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

namespace GlobalTheory.FunObj.StdDatum.TwBig

variable {D : D7}

theorem om_finset_sum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (g : GA D a) (g' : GA D d) {ι : Type}
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

theorem hatId_mono {𝔪 𝔫 : Ideal (𝓞 D.host.E)} (h : 𝔪 ≤ 𝔫) : hatId D 𝔪 ≤ hatId D 𝔫 :=
  AddSubgroup.closure_mono fun _ ⟨b, hb, s, hs, e⟩ => ⟨b, h hb, s, hs, e⟩

theorem conj_smul_mono {𝔪 𝔫 : Ideal (𝓞 D.host.E)} (h : 𝔪 ≤ 𝔫) : D.host.conj • 𝔪 ≤ D.host.conj • 𝔫 := by
  intro x hx
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hx ⊢
  exact h hx

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem modT_ne_bot (G : GridData L sc) (t : T) : modT G t ≠ ⊥ := by
  unfold modT
  exact mul_ne_zero (condE_ne_bot _) (Finset.prod_ne_zero_iff.2 fun w _ => w.ne_bot)

theorem modT_le_condE (G : GridData L sc) (t : T) : modT G t ≤ condE G.pl := Ideal.mul_le_left

theorem absNorm_modT (G : GridData L sc) (t : T) : Ideal.absNorm (modT G t) = levQ G.pl * Qn G t := by
  unfold modT Qn
  rw [map_mul, map_prod, GlobalTheory.FunObj.NormLevel.absNorm_condE]

end GlobalTheory.FunObj.StdDatum.TwBig

noncomputable section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

namespace GlobalTheory.FunObj.StdDatum.TwBig
open GlobalTheory.FunObj.SqNum.NuCond GlobalTheory.Mem.Col2.SplitChar

theorem nuInv_base_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m) (u : (AE D)ˣ), IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) → (nuH G μ₀ i j)⁻¹.1 (finIdl D u) = 1 := by
  classical
  intro D T L sc μ₀ hL G i j u hu hm
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  obtain ⟨n, hn⟩ : ∃ n : HeightOneSpectrum (𝓞 D.host.E) → ℕ, ∀ v, n v =
      if v.under (𝓞 D.host.F) ∈ G.pl.S0 then condExp G.pl (v.under (𝓞 D.host.F)) else 0 := ⟨_, fun _ => rfl⟩
  have hlev : ∀ v, (nuH G μ₀ i j).LevelLe v (n v) := by
    intro v
    have hμ := L.C.isMu0 j
    rw [show nuH G μ₀ i j = L.C.mu0 j * L.xiH μ₀ / G.ch.chiH (D.R.m - i) from rfl, hL.xi_base, mul_one, div_eq_mul_inv]
    refine Formalism.L2.Host.HChar.LevelLe.mul ?_ (Formalism.L2.Host.HChar.LevelLe.inv ?_)
    · by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · refine levelLe_mono (hμ.tame v) ?_
        rw [hn v, if_pos h, condExp]
        split_ifs <;> omega
      · refine Formalism.L2.Host.HChar.UnrAt.levelLe (hμ.unr v fun k hk => h ?_) _
        rw [G.pl.mem_S0_of_sum_eq]
        right
        rw [S1_mem_OmF]
        have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (v.under (𝓞 D.host.F)).asIdeal := by
          show _ ∈ v.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
          rw [Ideal.mem_comap, map_natCast]
          exact hk
        fin_cases k
        · exact Or.inl hk'
        · exact Or.inr (Or.inl hk')
    · by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · by_cases h0 : v.under (𝓞 D.host.F) = G.pl.v0
        · rw [hn v, if_pos h, condExp, if_pos h0]
          exact (G.ch.lev0 _ k1 k2 v h0).1
        · have h1 := (G.pl.mem_S0_of_sum_eq.1 h).resolve_left h0
          rw [hn v, if_pos h, condExp, if_neg h0]
          exact (G.ch.lev1 _ k1 k2 v h1).1
      · rw [hn v, if_neg h]
        exact Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ k1 k2 v h) 0
  have hval : ∀ v, vl D v ((u : AE D) - 1) ≤ WithZero.exp (-(n v : ℤ)) := by
    intro v
    by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
    · rw [hn v, if_pos h]
      refine vl_le_of_mem_hatId (fun b hb => ?_) hm
      have hw : (G.pl.w (v.under (𝓞 D.host.F))).under (𝓞 D.host.F) = v.under (𝓞 D.host.F) := G.pl.w_over _ h
      rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne (G.pl.w (v.under (𝓞 D.host.F))) v).1 hw.symm with e | e
      · have hb1 : b ∈ condE G.pl := Ideal.mul_le_left hb
        have hb2 := condE_le G.pl h hb1
        rw [← e] at hb2
        exact val_le_of_mem_pow hb2
      · have hb1 : b ∈ D.host.conj • condE G.pl := Ideal.mul_le_right hb
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb1
        have hb2 := val_le_of_mem_pow (condE_le G.pl h hb1)
        have e2 := e (((D.host.conj⁻¹ • b : 𝓞 D.host.E)) : D.host.E)
        have e3 : c.toRingEquiv (((D.host.conj⁻¹ • b : 𝓞 D.host.E)) : D.host.E) = (b : D.host.E) := by
          show c _ = _
          rw [hc]
          show D.host.conj (D.host.conj⁻¹ (b : D.host.E)) = _
          exact AlgEquiv.apply_symm_apply _ _
        rw [e3] at e2
        rw [e2]
        exact hb2
    · rw [hn v, if_neg h, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact vl_le (sub_mem hu.1 (one_mem _)) v
  have hU := finIdl_unit hu
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (nuH G μ₀ i j)⁻¹.2.1 (finIdl D u) hU
    (fun w => by rw [finIdl_fst]; rfl) (fun v x hx => ?_)
  have hxu : Formalism.L2.Host.IsUnitAt v x := by
    show Valued.v (x : v.adicCompletion D.host.E) = 1
    rw [hx]
    exact hU v
  refine (hlev v).inv x hxu ?_
  rw [hx, vl_sub_one]
  exact hval v

theorem nuInv_eq_one_of_cong : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (t : T) (i j : Fin D.R.m) {N : ℕ} (χν : HeckeU D N), (∀ x, χν.f x = (nuH G t i j)⁻¹.1 (finIdl D x)) → ∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (modT G t * D.host.conj • modT G t) → χν.f u = 1 := by
  intro D T L sc μ₀ hL G t i j N χν hχ u hu hm
  have hle : modT G t * D.host.conj • modT G t ≤ condE G.pl * D.host.conj • condE G.pl :=
    Ideal.mul_mono (modT_le_condE G t) (conj_smul_mono (modT_le_condE G t))
  have h1 := nuInv_base_eq_one hL G i j u hu (hatId_mono hle hm)
  have h2 := GlobalTheory.BotPairSmall.CondXi.xiH_eq_one_of_cong hL G t u hu hm
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    show L.C.mu0 j * L.xiH t / G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH μ₀ / G.ch.chiH (D.R.m - i) * L.xiH t
    rw [hL.xi_base, mul_one, mul_div_right_comm]
  rw [hχ, e, mul_inv]
  show ((nuH G μ₀ i j)⁻¹ * (L.xiH t)⁻¹).1 (finIdl D u) = 1
  have e1 : ((nuH G μ₀ i j)⁻¹ * (L.xiH t)⁻¹).1 (finIdl D u) = (nuH G μ₀ i j)⁻¹.1 (finIdl D u) * ((L.xiH t).1 (finIdl D u))⁻¹ := rfl
  rw [e1, h1, h2, inv_one, mul_one]

end GlobalTheory.FunObj.StdDatum.TwBig

noncomputable section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

namespace GlobalTheory.FunObj.StdDatum.TwBig

theorem twist_isCoprime_bb {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (PP : HeightOneSpectrum (𝓞 D.host.E)) (hP : PP ∈ L.Q t) : IsCoprime PP.asIdeal D.host.𝔟 := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  have heq := PP.isMaximal.eq_of_le hne le_sup_left
  have hle : D.host.𝔟 ≤ PP.asIdeal := le_sup_right.trans heq.symm.le
  have h2q := GlobalTheory.HalfCompare.two_q_mem (P := PP) (Ideal.dvd_iff_le.2 hle)
  refine (hL.Q_off t PP hP).1 ?_
  rw [show D.host.QS * D.host.q * D.host.d * D.sp.T = (D.host.QS * D.host.q) * (D.host.d * D.sp.T) by ring, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ h2q

theorem modT_isCoprime_bb {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T)
    (hb : IsCoprime (condE G.pl) D.host.𝔟) : IsCoprime (modT G t) D.host.𝔟 := by
  classical
  unfold modT
  refine IsCoprime.mul_left hb (IsCoprime.prod_left fun w hw => twist_isCoprime_bb hL t w ?_)
  simp only [twPl, locPl, Finset.mem_filter, Finset.mem_union] at hw
  exact hw.1.resolve_left hw.2

end GlobalTheory.FunObj.StdDatum.TwBig

noncomputable section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

namespace GlobalTheory.FunObj.StdDatum

theorem exists_bottom_big_modT : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, GlobalTheory.NormSum.Inp D → L.Is μ₀ → Nat.Coprime D.host.pde (D.host.QS * D.host.q) → Nat.Coprime D.host.pde' (D.host.QS * D.host.q) → ∀ (G : GridData L sc) (t : T) {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χβ : HeckeU D (botBig D i j)), (∀ x, χβ.f x = (betaH G i j)⁻¹.1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G t i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl * Qn G t), P.a = botBig D i j ∧ P.d = botBig D i j + botSmall D i j ∧ HasChars P (betaH G i j)⁻¹ (nuH G t i j)⁻¹ ∧ IsStdDatum P (modT G t) 0 ∧ IsBlockLevel P (modT G t) (botBig D i j) := by
  intro D T L sc μ₀ _hI hL hpq hpq' G t δ t0 hc ht i j χβ hβ χν hν hn
  have hd : Even (botBig D i j + botSmall D i j) := by
    obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
    exact ⟨halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  have had : botBig D i j ≤ botBig D i j + botSmall D i j := Nat.le_add_right _ _
  obtain ⟨e0, vac, h0⟩ := GlobalTheory.Vacuum.exists_vacuum D ⊤ δ hc t0 ht _ _ (hd.mul_left (botBig D i j))
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := GlobalTheory.FinWeil.exists_weil_of_vacuum D ⊤ δ hc _ _ e0 vac.1 h0 χβ χν
  have hm : modT G t ≠ ⊥ := TwBig.modT_ne_bot G t
  have hcop : IsCoprime (modT G t) (D.host.conj • modT G t) := Ideal.isCoprime_iff_sup_eq.2 (GlobalTheory.SqTop.modT_sup_conj hL G t)
  have hb : IsCoprime (modT G t) D.host.𝔟 := TwBig.modT_isCoprime_bb hL G t (GlobalTheory.T.gridConductorIdealCM_isCoprime_halfDifferent G.pl hpq hpq')
  have hnu : ∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (modT G t * D.host.conj • modT G t) → W.chV'.f u = 1 := by
    rw [hW2]; exact TwBig.nuInv_eq_one_of_cong hL G t i j χν hν
  have hN : Ideal.absNorm (modT G t) = levQ G.pl * Qn G t := TwBig.absNorm_modT G t
  obtain ⟨hi0, -⟩ := GlobalTheory.congLev_relIndex_le D (modT G t) hm (botBig D i j)
  obtain ⟨R, hR1, hR2'⟩ := GlobalTheory.exists_finset_leftTransversal_of_relIndex_ne_zero (intG D (botBig D i j)) (congLev D (modT G t) (botBig D i j)) (congLev_le _ _) hi0
  have hR2 : ∀ k ∈ intG D (botBig D i j), ∃! r, r ∈ R ∧ CongOne D (modT G t) (r⁻¹ * k) := by
    intro k hk
    obtain ⟨r, ⟨hr, hrk⟩, hu⟩ := hR2' k hk
    refine ⟨r, ⟨hr, ((GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hrk).2⟩, fun r' ⟨hr', h'⟩ => hu r' ⟨hr', (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).2
      ⟨mul_mem (inv_mem (hR1 r' hr')) hk, h'⟩⟩⟩
  have hcv := GlobalTheory.FunObj.CosetTT.cosetV_mem_TT D δ hc (modT G t) hm 0 _ _ e0 vac.1
  have hfix : ∀ k ∈ intG D (botBig D i j), W.Om k 1 (stdSum W (modT G t) 0 R) = stdSum W (modT G t) 0 R := by
    intro k hk
    unfold stdSum
    rw [TwBig.om_finset_sum W k 1 R _ fun r _ => W.maps _ _ _ hcv]
    have e1 : ∀ r, W.Om k 1 (W.Om r 1 (cosetV D δ (modT G t) 0 _ _ e0)) = W.Om (k * r) 1 (cosetV D δ (modT G t) 0 _ _ e0) := by
      intro r
      have := W.mul k r 1 1 _ hcv
      rw [mul_one] at this
      exact this.symm
    simp_rw [e1]
    refine GlobalTheory.sum_transversal_left_translate_invariant (intG D (botBig D i j)) (congLev D (modT G t) (botBig D i j)) R
      (fun g => W.Om g 1 (cosetV D δ (modT G t) 0 _ _ e0)) hR1 hR2' (fun r _ c hc' => ?_) k hk
    have := W.mul r c 1 1 _ hcv
    rw [mul_one] at this
    obtain ⟨hc1, hc2⟩ := (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hc'
    rw [this, GlobalTheory.T.weil_fixes_cosetVector_congruent_one_mod_ideal D δ t0 hc e0 vac W (modT G t) hm hcop hnu 0 (by omega) c hc1 hc2]
  have hle : congLev D (modT G t) (botBig D i j + botSmall D i j) ≤
      blockLev D (modT G t) (botBig D i j + botSmall D i j) (botBig D i j) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hk
    refine (GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff _ _ _ _ _).2 ⟨hk1, fun a b hb ha => ?_⟩
    have hab : a ≠ b := fun e => by rw [e] at ha; omega
    have := hk2 a b
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hab, sub_zero] at this
  obtain ⟨hj0, hj1⟩ := GlobalTheory.congLev_relIndex_le D (modT G t) hm (botBig D i j + botSmall D i j)
  have hQ : 0 < levQ G.pl * Qn G t := by
    rw [← hN]; exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hm)
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
  have hpres : Pres D ⊤ δ (levQ G.pl * Qn G t) e0 (stdSum W (modT G t) 0 R) := by
    rw [← hN]
    exact GlobalTheory.T.standardTheta_datum_presentation_level_norm D δ t0 hc e0 vac had W _ hm hcop hb hnu R hR1 hR2 hfix
  have hidx_ne : (blockLev D (modT G t) (botBig D i j + botSmall D i j) (botBig D i j)).relIndex
      (intG D (botBig D i j + botSmall D i j)) ≠ 0 := fun h =>
    hj0 (Subgroup.relIndex_eq_zero_of_le_left hle h)
  have hidx_le : (blockLev D (modT G t) (botBig D i j + botSmall D i j) (botBig D i j)).relIndex
      (intG D (botBig D i j + botSmall D i j)) ≤ (levQ G.pl * Qn G t) ^ ((botBig D i j + botSmall D i j) ^ 2 + 4) := by
    refine (Subgroup.relIndex_le_of_le_left hle hj0).trans (hj1.trans ?_)
    rw [hN]
    exact Nat.pow_le_pow_right hQ (by omega)
  have heig := GlobalTheory.T.standardThetaDatum_eigenvector_blockLevel D δ t0 hc e0 vac had W _ hm hcop hnu R hR1 hR2 hfix
  let P : Pair D ⊤ δ t0 (levQ G.pl * Qn G t) :=
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
      F := stdSum W (modT G t) 0 R
      pres := hpres
      fix := hfix
      J := blockLev D (modT G t) (botBig D i j + botSmall D i j) (botBig D i j)
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
