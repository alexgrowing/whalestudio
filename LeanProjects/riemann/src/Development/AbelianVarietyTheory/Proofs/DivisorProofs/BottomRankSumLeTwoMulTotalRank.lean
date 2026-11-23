import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvHasInfinityTypeCmType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeightEqAbsInfType
import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
import Formalism.LocalToGlobal.UnitaryNorms.CharShare

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum
open Formalism.L2.Host (HChar)

noncomputable section

namespace GlobalTheory.SqTop.BotSmallProof

theorem eq_of_dvd_absNorm {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {ℓ p : ℕ}
    (hℓ : ℓ.Prime) (hp : p.Prime) (hv : ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal) (h : p ∣ Ideal.absNorm v.asIdeal) : p = ℓ := by
  have hmax : (Ideal.span {((ℓ : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hℓ).irreducible
  haveI hl : v.asIdeal.LiesOver (Ideal.span {((ℓ : ℕ) : ℤ)}) := by
    refine ⟨hmax.eq_of_le ?_ ?_⟩
    · exact (v.isPrime.comap (algebraMap ℤ (𝓞 K))).ne_top
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 K) ((ℓ : ℕ) : ℤ) ∈ v.asIdeal
      rw [map_natCast]; exact hv
  rw [Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hℓ] at h
  exact (Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h)

theorem splitIn_of_cls {D : D7} {p : ℕ} (h : D.host.cls p = .splitK) : SplitIn D p := by
  right
  unfold Formalism.BasicNotions.Host.cls primeClass at h
  split_ifs at h with h1 h2 h3 h4 <;> first | exact h4 | cases h

theorem goodLevel {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (hsplit : ∀ p ∈ D.host.levelPrimes, D.host.cls p = .splitK) : GoodLevel D (levQ P) := by
  refine ⟨?_, fun p hp hdvd => ?_⟩
  · unfold levQ
    exact Finset.prod_pos fun v _ => pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
  · unfold levQ at hdvd
    obtain ⟨v, hv, hd⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    have hd' := hp.dvd_of_dvd_pow hd
    rcases P.mem_S0_of_sum_eq.1 hv with rfl | h1
    · rw [eq_of_dvd_absNorm _ (leastSplitAuxiliaryPrimeThetaChain_spec D).1 hp P.basePlace_over_qZero hd']
      exact Or.inr (Formalism.L2.Host.split_prime_jacobi_neg_d D)
    · rcases (S1_mem_OmF D).1 h1 with h | h | h | h
      · rw [eq_of_dvd_absNorm _ (D.host.g_prime 0) hp h hd']
        exact splitIn_of_cls (hsplit _ (D.host.g_level 0))
      · rw [eq_of_dvd_absNorm _ (D.host.g_prime 1) hp h hd']
        exact splitIn_of_cls (hsplit _ (D.host.g_level 1))
      · rw [eq_of_dvd_absNorm _ D.host.pde_prime hp h hd']
        exact splitIn_of_cls (hsplit _ D.host.pde_level.1)
      · rw [eq_of_dvd_absNorm _ D.host.pde'_prime hp h hd']
        exact splitIn_of_cls (hsplit _ D.host.pde_level.2)

theorem twPl_base {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) :
    twPl G μ₀ = ∅ := by
  have hQ : L.Q μ₀ = ∅ := by
    ext PP
    simp only [Finset.notMem_empty, iff_false]
    intro h
    refine ((hL.Q_ram μ₀ PP).2 (Or.inl h)) ?_
    rw [hL.xi_base]
    intro x _
    rfl
  ext w
  simp [twPl, locPl, hQ]

theorem nuH_inv_hasInf_all {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc)
    (t : T) (i j : Fin D.R.m) : (nuH G t i j)⁻¹.HasInf (Formalism.L2.Host.embTau D)
      (fun τ => 2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i))) := by
  intro k
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    simp only [nuH, hL.xi_base, mul_one]; exact mul_div_right_comm _ _ _
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  rw [e, mul_inv, HChar.inf_mul, Units.val_mul, HChar.inf_inv (L.xiH t), Formalism.L2.Host.HChar.inf_eq_one_of_order hn ho k, inv_one,
    Units.val_one, mul_one]
  exact nuH_inv_hasInf hL G i j k

theorem rankV_lt {D : D7} {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : rankV D i j + 1 ≤ bigN D := by
  have hm := D.R.two_le_m
  have e1 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have e2 : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have e3 : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
  simp only [rankV, bigN, Ranks.r]
  omega

theorem bottomRank_sum_le_two_mul_totalRank (D : D7) (i j : Fin D.R.m) : botBig D i j + botSmall D i j ≤ 2 * bigN D := by
  obtain ⟨h1, h2, -⟩ := ranks_exact D i j
  have a1 := rankV_lt (D := D) (i := i + 1) (j := j + 1) (by omega) (by omega)
  have a2 := rankV_lt (D := D) (i := i) (j := j) (by omega) (by omega)
  omega

theorem natAbs_le_maxWt (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) :
    max (wtA D C i j τ).natAbs (wtA' D C i j τ).natAbs ≤ maxWt D C := by
  unfold maxWt
  refine le_max_of_le_right ?_
  have := Finset.le_sup (f := fun x : Fin D.R.m × Fin D.R.m × D.what₂.Tau =>
      max (wtA D C x.1 x.2.1 x.2.2).natAbs (wtA' D C x.1 x.2.1 x.2.2).natAbs) (Finset.mem_univ (i, j, τ))
  exact this

theorem n_le_arith {n d ε c e A A' : ℤ} (hd : 0 ≤ d) (hε : ε = 1 ∨ ε = -1) (hc : c = e ∨ c = -e)
    (hw : 2 * n = ε * c - d) (hA : 2 * (A - A') = e - d) : n ≤ |A| + |A'| := by
  have l1 := le_abs_self A
  have l2 := neg_abs_le A
  have l3 := le_abs_self A'
  have l4 := neg_abs_le A'
  rcases hε with rfl | rfl <;> rcases hc with rfl | rfl <;> omega

theorem small_of {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc)
    (t : T) (i j : Fin D.R.m) {δ t0 : ℂ} {Q : ℕ} (X : Pair D ⊤ δ t0 Q) (hd : X.d = botBig D i j + botSmall D i j)
    {χ : HChar D.host.E} (hc : HasChars X χ (nuH G t i j)⁻¹) : X.Small (bigN D) (maxWt D sc.cGap) := by
  refine ⟨hd ▸ bottomRank_sum_le_two_mul_totalRank D i j, fun τ => ?_⟩
  have habs := GlobalTheory.SplitWeight.abs_weight_eq_abs_infType X.W.chV' X.W.ep' _ _ X.W.ep_pm.2 hc.2
    (nuH_inv_hasInf_all hL G t i j) τ
  have hw : 2 * (X.n τ : ℤ) = X.W.ep' * X.W.chV'.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by
    rw [← hd]; exact X.wt τ
  have hn := n_le_arith (Nat.cast_nonneg _) X.W.ep_pm.2 (abs_eq_abs.1 habs) hw (two_mul_wtA_sub D sc.cGap i j τ)
  have hB := natAbs_le_maxWt D sc.cGap i j τ
  have hB1 := (le_max_left _ _).trans hB
  have hB2 := (le_max_right _ _).trans hB
  have c1 : ((wtA D sc.cGap i j τ).natAbs : ℤ) = |wtA D sc.cGap i j τ| := Int.natCast_natAbs _
  have c2 : ((wtA' D sc.cGap i j τ).natAbs : ℤ) = |wtA' D sc.cGap i j τ| := Int.natCast_natAbs _
  have hB1' : ((wtA D sc.cGap i j τ).natAbs : ℤ) ≤ maxWt D sc.cGap := by exact_mod_cast hB1
  have hB2' : ((wtA' D sc.cGap i j τ).natAbs : ℤ) ≤ maxWt D sc.cGap := by exact_mod_cast hB2
  have n_le : (X.n τ : ℤ) ≤ 2 * maxWt D sc.cGap := by linarith
  exact_mod_cast n_le

theorem botSmall_holds : BotSmall := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ⟨?_, ?_, ?_⟩⟩⟩
  · obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
    exact goodLevel G.pl Pm.level_split
  · exact twPl_base G hL
  · intro δ t0 Q P P' t i j 𝔪 h
    exact ⟨small_of hL G t i j P h.rank.2.2.1 h.chars,
      small_of hL G t i j P' (h.rank.2.2.2.trans h.rank.2.2.1) h.chars'⟩

end GlobalTheory.SqTop.BotSmallProof
