import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallFundamentalSetRealUnipotent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConsecutiveRatioLeRpow
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HformSpanEqZero

open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN

noncomputable section

namespace GlobalTheory.DeepPoint

open Formalism.L2.SG.Pf.unitaryCongruence in

theorem kg_one (I : AutInst) (m : ℕ) : (1 : I.Gf) ∈ I.Kg m :=
  ⟨K_one I, fun y _ => ⟨0, zero_mem _, by rw [fmat_one, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩

open Formalism.L2.SG.Pf.unitaryCongruence in

theorem kg_mul (I : AutInst) (m : ℕ) {x y : I.Gf} (hx : x ∈ I.Kg m) (hy : y ∈ I.Kg m) : x * y ∈ I.Kg m := by
  refine ⟨K_mul I hx.1 hy.1, fun v hv => ?_⟩
  obtain ⟨z, hz, hyz⟩ := hy.2 v hv
  obtain ⟨z', hz', hxz⟩ := hx.2 v hv
  refine ⟨I.fmat x *ᵥ z + z', add_mem (K_mv I hx.1 hz) hz', ?_⟩
  have e : (I.fmat (x * y) - 1) *ᵥ v = I.fmat x *ᵥ ((I.fmat y - 1) *ᵥ v) + (I.fmat x - 1) *ᵥ v := by
    rw [fmat_mul, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.one_mulVec]
    abel
  rw [e, hyz, hxz, Matrix.mulVec_smul, smul_add]

open Formalism.L2.SG.Pf.unitaryCongruence in

theorem kg_inv (I : AutInst) (m : ℕ) {k : I.Gf} (hk : k ∈ I.Kg m) : k⁻¹ ∈ I.Kg m := by
  refine ⟨K_inv I hk.1, fun y hy => ?_⟩
  obtain ⟨z, hz, hkz⟩ := hk.2 y hy
  refine ⟨-(I.fmat k⁻¹ *ᵥ z), neg_mem (K_mv I (K_inv I hk.1) hz), ?_⟩
  have h1 : I.fmat k⁻¹ * I.fmat k = 1 := fmat_inv_mul I k
  have e : (I.fmat k⁻¹ - 1) *ᵥ y = -(I.fmat k⁻¹ *ᵥ ((I.fmat k - 1) *ᵥ y)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, h1, mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [e, hkz, Matrix.mulVec_smul, smul_neg]

theorem isIsot_span (I : AutInst) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (h0 : R ≠ ⊥)
    (hiso : ∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) :
    I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
  first
  | exact @_root_.GlobalTheory.HermitianFormLinearity.main
  | exact _root_.GlobalTheory.HermitianFormLinearity.main
  | (apply _root_.GlobalTheory.HermitianFormLinearity.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.HermitianFormLinearity.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HermitianFormLinearity.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HermitianFormLinearity.main ..)

theorem exists_step (I : AutInst) (x : I.GA) (q : ℕ) (hn : 1 ≤ I.n)
    (hrk : ∀ v, rkR (I.ε v) ≤ q) (hl : least I x < 1 / 2) :
    ∃ (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi : ℝ),
      IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R ∧ R ≠ ⊥ ∧ R ≤ stepLt I x (1 / 2) ∧
      R ≤ lamX I x ∧ 0 < hi ∧ largestSize (bas I) (frm I x) R ≤ hi ∧
      (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) ∧
      hi ≤ (2 * least I x) ^ ((1 : ℝ) / q) * lo ∧ hi ^ 2 ≤ (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  obtain ⟨⟨a, S, τ, hF⟩, -, hspec⟩ := GlobalTheory.PointFlag.flag_spec I x
  have hpiece := (hspec a S τ hF).1
  have ha0 := ((hspec a S τ hF).2 hn).1
  have hτ0 := ((hspec a S τ hF).2 hn).2
  obtain ⟨hS0, hSmono, hSlast, hτmono, hτ, -⟩ := hF
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact absurd (ha0.1 h) (not_le.2 hl)
    · exact h
  have hrkS : ∀ i : Fin (a + 1), (i : ℕ) ≤ rkK (S i) := by
    intro i
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have := (hpiece i).2.1
      simp only [Fin.coe_castSucc] at ih
      simp only [Fin.val_succ]
      omega
  have haq : a ≤ q := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    have h1 := hrkS (Fin.last a)
    rw [hSlast] at h1
    have h2 := (GlobalTheory.FlagIso.flag_isotropic I x).2.1 v
    simp only [Fin.val_last] at h1
    exact h1.trans (h2.trans (hrk v))
  set τ' : ℕ → ℝ := fun i => if h : i < a then τ ⟨i, h⟩ else 1 / 2 with hτ'
  have hτ'pos : ∀ i ≤ a, 0 < τ' i := by
    intro i _
    simp only [hτ']
    split_ifs with h
    · exact (hτ ⟨i, h⟩).1
    · norm_num
  have hτ'lt : ∀ i < a, τ' i < τ' (i + 1) := by
    intro i hi
    simp only [hτ', dif_pos hi]
    split_ifs with h
    · exact hτmono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
    · exact (hτ ⟨i, hi⟩).2.1
  have hτ'a : τ' a = 1 / 2 := by simp [hτ']
  have hτ'0 : τ' 0 = least I x := by
    simp only [hτ', dif_pos (show 0 < a by omega)]
    exact hτ0 (by omega)
  obtain ⟨b, hb, hratio, hsq⟩ := GlobalTheory.exists_consecutive_ratio_le_rpow a q τ' ha haq hτ'pos hτ'lt hτ'a
  rw [hτ'0] at hratio hsq
  set i : Fin a := ⟨b, hb⟩ with hi_def
  have hib : τ' b = τ i := by simp [hτ', hb, i]
  refine ⟨S i.succ, τ' (b + 1), τ i, ?_, ?_, ?_, ?_, (hτ i).1, ?_, ?_, ?_, ?_⟩
  · rw [(hτ i).2.2.1]; exact (GlobalTheory.CountSteps.steps I x _ (hτ i).1).1
  · intro h
    have := hSmono (Fin.succ_pos i)
    rw [hS0, h] at this
    exact lt_irrefl _ this
  · rw [← hSlast]; exact hSmono.monotone (Fin.le_last _)
  · rw [(hτ i).2.2.1]; exact sSup_le fun N hN => hN.1
  · exact (hpiece i).2.2.1.le
  · intro N hN hNL
    by_cases hb1 : b + 1 < a
    · have eS : S i.succ = S (Fin.castSucc (⟨b + 1, hb1⟩ : Fin a)) := congrArg S (Fin.ext (by simp [i]))
      have e : τ' (b + 1) = τ ⟨b + 1, hb1⟩ := by simp [hτ', hb1]
      rw [e, eS]
      rw [eS] at hN
      exact (hpiece ⟨b + 1, hb1⟩).2.2.2.1 N hN hNL
    · have hba : b + 1 = a := by omega
      have e : τ' (b + 1) = 1 / 2 := by rw [hba, hτ'a]
      have eS : S i.succ = stepLt I x (1 / 2) := by
        rw [← hSlast]; exact congrArg S (Fin.ext (by simp [i, hba]))
      rw [e, eS]
      rw [eS] at hN
      exact (GlobalTheory.CountSteps.steps I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.1 N hN hNL
  · rw [← hib]
    have hpos := hτ'pos (b + 1) (by omega)
    rwa [div_le_iff₀ hpos] at hratio
  · rw [← hib]; exact hsq

theorem deep_point : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ I.n →
    (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W, I.IsIsot W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset,
      ∃ k ∈ I.Kg g, ∃ (u : I.Ginf) (A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ),
        (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧
        (∀ v, uMat (u v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ m * x = γ * x * (u, k) ∧
        Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤
          (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  intro I x g q hg _ hn hrk hl
  obtain ⟨R, lo, hi, hsat, hR0, hRS, hRL, hhi, hlarge, hlo, hhl, hh2⟩ := exists_step I x q hn hrk hl
  have hisoR : ∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0 :=
    fun y hy z hz => (GlobalTheory.FlagIso.flag_isotropic I x).1 y (hRS hy) z (hRS hz)
  have hperp : R ≤ perpIn I x R := fun y hy =>
    Submodule.subset_span ⟨hRL hy, fun s hs => hisoR s hs y hy⟩
  have hWiso : I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := isIsot_span I R hR0 hisoR
  refine ⟨_, hWiso, fun m hm => ?_⟩
  obtain ⟨⟨N, hN⟩, -, hsplit, hdense, -⟩ := GlobalTheory.UnipApprox.strong_approximation I _ hWiso
  have hU : {c : I.Gf | x.2⁻¹ * c * x.2 ∈ I.Kg g} ∈ nhds (1 : I.Gf) := by
    have ho : IsOpen (I.Kg g) := I.topf_open g hg
    have hc : Continuous fun c : I.Gf => x.2⁻¹ * c * x.2 :=
      (continuous_const.mul continuous_id).mul continuous_const
    refine (ho.preimage hc).mem_nhds ?_
    show x.2⁻¹ * 1 * x.2 ∈ I.Kg g
    rw [mul_one, inv_mul_cancel]
    exact kg_one I g
  obtain ⟨γ, ⟨hγF, hγN⟩, hγU⟩ := hdense _ hU m hm
  have hm'N : γ⁻¹ * m ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
    rw [← hN] at hγN hm ⊢
    exact N.mul_mem (N.inv_mem hγN) hm
  have hν := (hsplit _ hm'N).1
  obtain ⟨γ', ⟨hγ'F, -⟩, hγ'K, A, Z, hAZ, heq, hbd, -⟩ :=
    GlobalTheory.SmallFund.small_fundamental_set I x g R lo hi _ hg hsat hR0 hperp hhi hlarge hlo hhl hh2 _ hν
  have hk : (x⁻¹ * γ' * x).2⁻¹ * (x.2⁻¹ * (γ⁻¹ * m).2 * x.2) ∈ I.Kg g :=
    kg_mul I g (kg_inv I g hγ'K) hγU
  refine ⟨γ * γ', Formalism.MainNotions.LeviCoordinates.rrg_mul_mem I hγF hγ'F, _, hk,
    (γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1, A, Z, hAZ, fun v => ?_, ?_, hbd⟩
  · have e : uMat (((γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1) v) =
        uMat ((γ'.1 v * x.1 v)⁻¹) * (uMat ((γ⁻¹ * m).1 v) * uMat (x.1 v)) := by
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [mul_assoc]
      rfl
    rw [e, heq v]
    have e2 : uMat (γ'.1 v) * uMat (x.1 v) = uMat (γ'.1 v * x.1 v) := rfl
    have e3 : uMat ((γ'.1 v * x.1 v)⁻¹) * uMat (γ'.1 v * x.1 v) = 1 := by
      show uMat ((γ'.1 v * x.1 v)⁻¹ * (γ'.1 v * x.1 v)) = 1
      rw [inv_mul_cancel]
      rfl
    rw [e2, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat ((γ'.1 v * x.1 v)⁻¹)), e3, Matrix.one_mul]
  · have h2 : γ' * x * ((γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1,
        (x⁻¹ * γ' * x).2⁻¹ * (x.2⁻¹ * (γ⁻¹ * m).2 * x.2)) = (γ⁻¹ * m) * x := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_mul]
        group
      · simp only [Prod.snd_mul, Prod.snd_inv]
        group
    calc m * x = γ * ((γ⁻¹ * m) * x) := by group
      _ = γ * γ' * x * _ := by rw [← h2]; simp only [mul_assoc]

end GlobalTheory.DeepPoint
