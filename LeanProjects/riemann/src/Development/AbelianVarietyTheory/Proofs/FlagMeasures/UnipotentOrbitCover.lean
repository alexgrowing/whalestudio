import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallFundamentalSetRealUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConsecutiveRatioLeRpow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallSizeCanonicalFlagPiecesPropertiesStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.DeepCover

theorem isIsot_span (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (h0 : R ≠ ⊥)
    (h : R ≤ perpIn I x R) : I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
  have hspan : Submodule.span I.E (R : Set (Fin I.n → I.E)) ≤
      Submodule.span I.E (perpIn I x R : Set (Fin I.n → I.E)) :=
    Submodule.span_mono h

  have h1 : ∀ s ∈ R, ∀ y ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)),
      Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 :=
    fun s hs y hy => GlobalTheory.FlagIso.hform_span I x R (hspan hy) hs

  have h2 : ∀ y ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)),
      ∀ z ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)),
        Formalism.UG.hform (starRingEnd I.E) I.J y z = 0 := by
    intro y hy z hz
    have hker : Submodule.span I.E (R : Set (Fin I.n → I.E)) ≤
        LinearMap.ker (GlobalTheory.FlagIso.hR I.J y) := by
      rw [Submodule.span_le]
      intro s hs
      rw [SetLike.mem_coe, LinearMap.mem_ker, GlobalTheory.FlagIso.hR_apply,
        ← GlobalTheory.FlagIso.hform_star I.J I.J_herm s y, h1 s hs y hy, star_zero]
    have hz' := hker hz
    rwa [LinearMap.mem_ker, GlobalTheory.FlagIso.hR_apply] at hz'
  refine ⟨?_, h2⟩
  intro hbot
  apply h0
  rw [eq_bot_iff]
  intro r hr
  have hr' : r ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)) := Submodule.subset_span hr
  rw [hbot] at hr'
  exact (Submodule.mem_bot _).2 ((Submodule.mem_bot _).1 hr')

theorem unipotent_orbit_cover : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ I.n → (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W : Submodule I.E (Fin I.n → I.E), I.IsIsot W ∧ ∀ ν : I.Ginf, ((ν, 1) : I.GA) ∈ I.NA W → ∃ γ ∈ I.GFset, ∃ k ∈ I.Kg g, ∃ y ∈ omega I x W ((I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4), ((ν, 1) : I.GA) * x = γ * y * (1, k) := by
  intro I x g q hg hn hq hlt

  obtain ⟨⟨a, S, τ, hF⟩, -, hspec⟩ := GlobalTheory.PointFlag.flag_spec I x
  obtain ⟨hpieces, hzero⟩ := hspec a S τ hF
  obtain ⟨ha0, hτ0⟩ := hzero hn
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact absurd (ha0.1 h) (not_le.2 hlt)
    · exact h
  obtain ⟨hall, -, -, hstep⟩ := GlobalTheory.T.smallSizeCanonicalFlag_pieces_properties I x a S τ hF
  obtain ⟨-, -, hSlast, hτmono, hτ, -⟩ := hF

  obtain ⟨τ', hτ'⟩ : ∃ f : ℕ → ℝ, f = fun i => if h : i < a then τ ⟨i, h⟩ else 1 / 2 := ⟨_, rfl⟩
  have hτ'lt : ∀ i (h : i < a), τ' i = τ ⟨i, h⟩ := by
    intro i h; rw [hτ']; exact dif_pos h
  have hτ'ge : ∀ i, a ≤ i → τ' i = 1 / 2 := by
    intro i h; rw [hτ']; exact dif_neg (not_lt.2 h)
  have hpos : ∀ i ≤ a, 0 < τ' i := by
    intro i _
    rcases lt_or_ge i a with h | h
    · rw [hτ'lt i h]; exact (hτ ⟨i, h⟩).1
    · rw [hτ'ge i h]; norm_num
  have hinc : ∀ i < a, τ' i < τ' (i + 1) := by
    intro i hi
    rw [hτ'lt i hi]
    rcases lt_or_ge (i + 1) a with h | h
    · rw [hτ'lt (i + 1) h]
      exact hτmono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
    · rw [hτ'ge (i + 1) h]; exact (hτ ⟨i, hi⟩).2.1
  have hlast : τ' a = 1 / 2 := hτ'ge a le_rfl

  have hrk : ∀ i (hi : i ≤ a), i ≤ rkK (S ⟨i, Nat.lt_succ_of_le hi⟩) := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have h1 := ih (Nat.le_of_succ_le hk)
      have h2 : rkK (S (Fin.castSucc ⟨k, hk⟩)) < rkK (S (Fin.succ ⟨k, hk⟩)) :=
        ((hpieces ⟨k, hk⟩).2.1)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt h1 h2)
  obtain ⟨-, hrkR, -⟩ := GlobalTheory.FlagIso.flag_isotropic I x
  have haq : a ≤ q := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    have h1 : a ≤ rkK (S (Fin.last a)) := hrk a le_rfl
    rw [hSlast] at h1
    exact h1.trans ((hrkR v).trans (hq v))

  obtain ⟨b, hb, hratio, hsq⟩ := GlobalTheory.exists_consecutive_ratio_le_rpow a q τ' ha haq hpos hinc hlast
  rw [hτ'lt 0 ha, hτ0 ha, hτ'lt b hb] at hratio hsq
  have hi_pos : 0 < τ ⟨b, hb⟩ := (hτ ⟨b, hb⟩).1
  have hlo_pos : 0 < τ' (b + 1) := hpos (b + 1) hb
  obtain ⟨-, -, -, hne, hlarge, hgeL⟩ := hstep ⟨b, hb⟩
  have hRperp : S (Fin.succ ⟨b, hb⟩) ≤ perpIn I x (S (Fin.succ ⟨b, hb⟩)) :=
    le_trans (hall _).2.2.1 (hall _).2.2.2.1
  have hsat : IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (S (Fin.succ ⟨b, hb⟩)) :=
    (hall _).1
  have hlo : ∀ N, S (Fin.succ ⟨b, hb⟩) < N → N ≤ lamX I x →
      τ' (b + 1) ≤ sizeQ (bas I) (frm I x) N (S (Fin.succ ⟨b, hb⟩)) := by
    rw [hτ']; exact hgeL
  refine ⟨Submodule.span I.E (S (Fin.succ ⟨b, hb⟩) : Set (Fin I.n → I.E)),
    isIsot_span I x _ hne hRperp, ?_⟩
  intro ν hν
  obtain ⟨γ, ⟨hγF, -⟩, hk, A, Z, hAZ, heq, hbound, hst⟩ :=
    GlobalTheory.T.small_fundamental_set_real_unipotent I x g (S (Fin.succ ⟨b, hb⟩)) (τ' (b + 1)) (τ ⟨b, hb⟩)
      ((2 * least I x) ^ ((1 : ℝ) / q)) hg hsat hne hRperp hi_pos hlarge hlo
      ((div_le_iff₀ hlo_pos).1 hratio) hsq ν hν

  obtain ⟨m, -, hm⟩ := hst 1 1
  have hm' : ∀ v, uMat (m v) * uMat (x.1 v) =
      uMat (x.1 v) * NormedSpace.exp (A v) * NormedSpace.exp (Z v) := by
    intro v; simpa only [Complex.ofReal_one, one_smul] using hm v

  obtain ⟨-, -, -, -, -, -, hKg⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨-, ⟨K, hK⟩, -⟩ := hKg g hg
  have hkinv : ((x⁻¹ * γ * x).2)⁻¹ ∈ I.Kg g := by
    rw [← hK] at hk ⊢
    exact K.inv_mem hk
  refine ⟨γ, hγF, ((x⁻¹ * γ * x).2)⁻¹, hkinv, ((m * x.1 : I.Ginf), x.2), ?_, ?_⟩
  · refine ⟨rfl, A, Z, hAZ, hbound, fun v => ?_, hst⟩
    show uMat (m v) * uMat (x.1 v) = _
    exact hm' v
  · have key : ∀ v, uMat (ν v) * uMat (x.1 v) = uMat (γ.1 v) * (uMat (m v) * uMat (x.1 v)) := by
      intro v
      rw [heq v, hm' v]
      simp only [mul_assoc]
    refine Prod.ext ?_ ?_
    · show ν * x.1 = γ.1 * (m * x.1) * 1
      rw [mul_one]
      funext v
      exact Subtype.ext (Units.ext (key v))
    · show 1 * x.2 = γ.2 * x.2 * ((x⁻¹ * γ * x).2)⁻¹
      simp only [Prod.snd_mul, Prod.snd_inv]
      group

end GlobalTheory.DeepCover
