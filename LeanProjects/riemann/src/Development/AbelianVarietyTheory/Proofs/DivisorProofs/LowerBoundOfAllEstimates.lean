import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HtMapLeOfPoints
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHalfRankSub

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.LowCover

theorem numeric {M E b K C1 muB mu0 : ℝ} (hb : 0 ≤ b) (hbE : b ≤ E) (hbK : b ≤ K) (hMK : |M| ≤ K) (hC1 : 0 ≤ C1)
    (h : (-M - C1 * E - 2 * b) - b / K * (|-M - C1 * E - 2 * b| + 2 * K) ≤ muB) (hR : muB - 2 * b ≤ mu0) :
    -M - (2 * C1 + 9) * E ≤ mu0 := by
  have hK : 0 < K ∨ b = 0 := by
    rcases eq_or_lt_of_le hb with h0 | h0
    · exact Or.inr h0.symm
    · exact Or.inl (h0.trans_le hbK)
  have hE : 0 ≤ E := hb.trans hbE
  have hC1E : 0 ≤ C1 * E := mul_nonneg hC1 hE
  have ht : |-M - C1 * E - 2 * b| ≤ |M| + C1 * E + 2 * b := by
    have := abs_sub (-M - C1 * E) (2 * b)
    have h2 := abs_sub (-M) (C1 * E)
    rw [abs_neg] at h2
    rw [abs_of_nonneg hC1E] at h2
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * b)] at this
    linarith
  rcases hK with hK | hb0
  · set ε := b / K with hε
    have hε0 : 0 ≤ ε := div_nonneg hb hK.le
    have hε1 : ε ≤ 1 := (div_le_one hK).2 hbK
    have hεK : ε * K = b := div_mul_cancel₀ b hK.ne'
    have h1 : ε * |-M - C1 * E - 2 * b| ≤ ε * |M| + ε * (C1 * E + 2 * b) := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hε0
    have h2 : ε * |M| ≤ b := hεK ▸ mul_le_mul_of_nonneg_left hMK hε0
    have h3 : ε * (C1 * E + 2 * b) ≤ C1 * E + 2 * b := by
      have : 0 ≤ C1 * E + 2 * b := by linarith
      nlinarith
    have h4 : ε * (|-M - C1 * E - 2 * b| + 2 * K) = ε * |-M - C1 * E - 2 * b| + 2 * b := by
      rw [mul_add, ← hεK]; ring
    rw [h4] at h
    nlinarith
  · subst hb0
    simp only [zero_div, zero_mul, sub_zero, mul_zero] at h hR
    nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem rkK_bot' {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] :
    Formalism.HN.rkK (⊥ : Submodule (𝓞 K) V) = 0 := by
  simp [Formalism.HN.rkK]

theorem lowAt_mono {p : PtAt ex Csz} {i : Fin D.R.m} {C C' : ℝ} (h : LowAt p i C) (hC : C ≤ C') (hE : 0 ≤ unitE p) :
    LowAt p i C' := by
  unfold LowAt at *
  nlinarith [mul_le_mul_of_nonneg_right hC hE]

theorem lowAt_of_cover (p : PtAt ex Csz) (i : Fin D.R.m) (PP CS CF CU : ℝ) (hCF : 0 ≤ CF) (hCU : 0 ≤ CU)
    (hS : SizeAt p i PP CS) (Y : Cov p i) (hG : DeepGoodAt p i Y) (hR : RingAt p i Y) (hM : MapsAt p i Y)
    (hK : RkAt p i Y PP) (hGm : GminAt p i Y PP) (hF : FlatAt p i Y CF) (hU : UAt p i Y CU) :
    LowAt p i (2 * (CF + CU) + 9) := by
  obtain ⟨hb1, hbE, -, -, hMK, hbK, -⟩ := hS
  obtain ⟨hGk, hGm', -, -, hrk0, -, -, -⟩ := hG
  obtain ⟨n, φ, hint, hinj, hnorm, hrk⟩ := hM
  have hTC : IsTotallyComplex Y.d.c₂.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := Y.d.c₂) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hKpos : 0 < PP * kap p i := by linarith
  have hBle : latDeep p i Y ≤ latW Y.U (Gk p i) := inf_le_left
  have hBfg : (latDeep p i Y).FG := GlobalTheory.HalfRankSub.fg_of_le_fg hGk.2.1 hBle
  have hA0 : latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1)))) ≠ ⊥ := by
    intro h
    change 0 < Formalism.HN.rkK (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) at hrk0
    rw [h] at hrk0
    rw [rkK_bot'] at hrk0
    exact lt_irrefl _ hrk0
  have hrkR : (n : ℝ) * Formalism.HN.rkK (latDeep p i Y) ≤
      (1 + L.sc.b / (PP * kap p i)) * Formalism.HN.rkK (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) := by
    have h1 : ((n * Formalism.HN.rkK (latDeep p i Y) : ℕ) : ℝ) ≤ (Y.rk (Gs p i (cZero D ((i : ℕ) + 1))) : ℝ) := by
      exact_mod_cast hrk
    push_cast at h1
    exact h1.trans hK
  have hmu : Y.mu (Gs p i (-(cZero D ((i : ℕ) + 1)))) =
      slope_sq (Y.nrm (Gs p i (-(cZero D ((i : ℕ) + 1))))) (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) := rfl
  have ht : -mainT p i - (CF + CU) * unitE p - 2 * L.sc.b ≤
      slope_sq (Y.nrm (Gs p i (-(cZero D ((i : ℕ) + 1))))) (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) -
        2 * L.sc.b := by
    unfold FlatAt at hF
    unfold UAt at hU
    rw [← hmu]
    nlinarith
  have hd := GlobalTheory.DescentFamily.descent Y.d.c₂.F _ _ (Y.nrm (Gs p i (-(cZero D ((i : ℕ) + 1))))) (Y.nrm (Gk p i))
    (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) (latDeep p i Y) n φ L.sc.b (PP * kap p i)
    (L.sc.b / (PP * kap p i)) (-mainT p i - (CF + CU) * unitE p - 2 * L.sc.b) hGm'.1 hGk.1 hGm'.2.1 hBfg hA0
    hint hinj hnorm hGm hKpos.le (div_nonneg (by linarith) hKpos.le) hrkR ht
  unfold LowAt
  unfold RingAt at hR
  exact numeric (by linarith) hbE hbK hMK (by linarith) hd hR

theorem low : Size → LowDef → DeepEx → DeepGood → Ring → Maps → Rk → Gmin → Flat → ULow → Low := by
  intro hS hD hE hG hR hM hK hGm hF hU
  refine Closed.imp (((((((((hS.and hD).and hE).and hG).and hR).and hM).and hK).and hGm).and hF).and hU) ?_
  intro eps Fm CH _ hh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨CS, -, aS⟩, CD, -, aD⟩, _, -, aE⟩, _, -, aG⟩, _, -, aR⟩, _, -, aM⟩, _, -, aK⟩, _, -, aGm⟩,
    CF, hCF, aF⟩, CU, hCU, aU⟩ := hh
  refine ⟨max CD (2 * (CF + CU) + 9), le_max_of_le_right (by linarith), ?_⟩
  obtain ⟨x0, h⟩ := ((((((((aS.and aD).and aE).and aG).and aR).and aM).and aK).and aGm).and aF).and aU
  refine ⟨x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨bS, bD⟩, bE⟩, bG⟩, bR⟩, bM⟩, bK⟩, bGm⟩, bF⟩, bU⟩ := h x hx hle ι p hp
  have hS' := bS i
  have hE0 : 0 ≤ unitE p := by obtain ⟨a, b, -⟩ := hS'; linarith
  rcases (Nat.succ_le_of_lt i.isLt).eq_or_lt with heq | hlt
  · exact lowAt_mono (bD i heq) (le_max_left _ _) hE0
  · obtain ⟨Y, hY⟩ := bE i hlt
    exact lowAt_mono (lowAt_of_cover p i _ CS CF CU hCF hCU hS' Y (bG i hlt Y hY) (bR i hlt Y hY) (bM i hlt Y hY)
      (bK i hlt Y hY) (bGm i hlt Y hY) (bF i hlt Y hY) (bU i hlt Y hY)) (le_max_right _ _) hE0

end GlobalTheory.CovTop.LowCover
