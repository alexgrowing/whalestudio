import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaBoundOnBoundary
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VandermondeRatioHarmonic
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

theorem capelliPoly_ofReal {n : ℕ} (lam : Fin n → ℝ) (Y : ℝ) :
    Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) (Y : ℂ) = ((∏ s, (Y + lam s) : ℝ) : ℂ) := by
  simp only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]

theorem qPoly_ofReal {k : ℕ} (T T' : ℝ) (u u' : Fin k → ℝ) (Y : ℝ) :
    Formalism.QuantumDeterminants.qPoly T T' u u' (Y : ℂ) =
      ((-(T * T') * ∏ i, ((Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)) : ℝ) : ℂ) := by
  simp only [Formalism.QuantumDeterminants.qPoly]
  push_cast <;> ring

private theorem prod_Icc_one_eq_prod_fin_succ {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∏ i ∈ Finset.Icc 1 n, f i = ∏ i : Fin n, f (i.1 + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc]
    rfl

theorem cfg_P (D : D7) (τ : D.what₂.Tau) (Y : ℝ) :
    (cfgOf D τ).P Y = ∏ s : Fin D.R.r, (Y + lamS D.R (D.hc τ) s) := by
  unfold Formalism.FourierDecayAlt.Sz.Cfg.P
  rw [prod_Icc_one_eq_prod_fin_succ]
  exact Finset.prod_congr rfl fun s _ => congrArg (Y + ·) (cfg_lam D τ s)

theorem cfg_q (D : D7) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (h5 : ∀ w : D.what₂.Word, ¬ IsTop D τ → uOne D w τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2) (T T' Y : ℝ) :
    (cfgOf D τ).q (deOf D u) (deOf D u') T T' Y =
      -(T * T') * ∏ i : Fin D.R.k, ((Y + 1 / 2 + uS D u τ i) * (Y + 1 / 2 + uS D u' τ i)) := by
  unfold Formalism.FourierDecayAlt.Sz.Cfg.q
  rw [prod_Icc_one_eq_prod_fin_succ]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : i.1 < D.R.k := i.2
  have hu : ∀ w : D.what₂.Word, (cfgOf D τ).u (deOf D w) (i.1 + 1) = uS D w τ i := by
    intro w
    rw [cfg_u D w τ (h5 w) (i.1 + 1) (by omega) (by omega)]
    unfold uOne
    rw [dif_pos (show 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ D.R.k by omega)]
    rfl
  rw [hu u, hu u']

theorem beUU_eq (D : D7) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (h5 : ∀ w : D.what₂.Word, ¬ IsTop D τ → uOne D w τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2) (κ Y : ℝ) :
    beUU D κ u u' τ Y = (cfgOf D τ).be κ (deOf D u) (deOf D u') (Tr D u) (Tr D u') Y := by
  have e1 : ((Y : ℂ) + 1) = ((Y + 1 : ℝ) : ℂ) := by push_cast; ring
  simp only [beUU, beS, Formalism.FourierDecayAlt.Sz.Cfg.be, Formalism.FourierDecayAlt.Sz.Cfg.core]
  rw [e1, capelliPoly_ofReal, capelliPoly_ofReal, qPoly_ofReal, ← cfg_P D τ Y, ← cfg_P D τ (Y + 1),
    ← cfg_q D u u' τ h5 (Tr D u) (Tr D u') Y, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.norm_real, Real.norm_eq_abs]
  congr 1
  have hm := D.R.two_le_m
  have hrS : 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨j, hj⟩ := D.R.m_even
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hz : 1 + 2 * (D.R.rS : ℤ) = ((D.R.m - 1 : ℕ) : ℤ) := by omega
  show κ ^ (-(1 + 2 * (D.R.rS : ℤ))) = (κ ^ (D.R.m - 1))⁻¹
  rw [hz, zpow_neg, zpow_natCast]

theorem cfg_aeff (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : (cfgOf D τ).aeff = aEff D u τ := by
  have hk := D.R.m_add_three_le_k
  have hv := cfg_v D τ 1 le_rfl (by omega)
  have hD : (cfgOf D τ).Del = (D.s.Del : ℝ) := rfl
  have ha : (cfgOf D τ).a = uOne D u τ 1 := (uOne_one D u τ).symm
  unfold Formalism.FourierDecayAlt.Sz.Cfg.aeff aEff
  rw [hv, hD, ha]
  by_cases h : IsTop D τ
  · have ht : (cfgOf D τ).top = true := (cfg_top_iff D τ).2 h
    rw [if_pos ht, if_pos h]
    rfl
  · have ht : (cfgOf D τ).top = false := (cfg_top_false_iff D τ).2 h
    rw [if_neg (by simp [ht]), if_neg h]

theorem cfg_prodb (D : D7) (τ : D.what₂.Tau) : (cfgOf D τ).prodb = ∏ j ∈ Finset.Icc 1 D.R.m, bOne D τ j := rfl

theorem deOf_ne (D : D7) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (h5 : ∀ w : D.what₂.Word, ¬ IsTop D τ → uOne D w τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2)
    (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ D.R.k - 2) (hne : uOne D u τ (l + 1) ≠ uOne D u' τ (l + 1)) :
    deOf D u l ≠ deOf D u' l := by
  intro heq
  apply hne
  have hk : (cfgOf D τ).k = D.R.k := rfl
  rw [← cfg_u D u τ (h5 u) (l + 1) (by omega) (by omega), ← cfg_u D u' τ (h5 u') (l + 1) (by omega) (by omega)]
  have a1 : l + 1 ≠ 1 := by omega
  have a2 : l + 1 ≠ (cfgOf D τ).k := by rw [hk]; omega
  simp only [Formalism.FourierDecayAlt.Sz.Cfg.u, a1, a2, if_false, Nat.add_sub_cancel, heq]

theorem beta_le_X (c : Sz.Cfg) (de de' : ℕ → ℝ) (ka g T T' Y : ℝ) (l : ℕ) (h : c.Ok)
    (hw : Sz.IsWord c.k de) (hw' : Sz.IsWord c.k de') (hka0 : 0 < ka) (hg0 : 0 < g) (hT : 0 < T) (hT' : 0 < T')
    (hl : 1 ≤ l) (hlk : l + 2 ≤ c.k) (hne : de l ≠ de' l) (hY : Y ∈ c.cutI l) :
    0 < c.aeff ∧ g ^ c.m * c.be ka de de' T T' Y ≤
      (g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff) *
        ((Real.sqrt (T * T'))⁻¹ * Real.exp c.vth * 8 * 3.3 * Real.sqrt c.k * Real.sqrt (14 / 5) *
          Real.sqrt ((c.v l + Y) / c.Del)) := by
  obtain ⟨_, _, _, hbe⟩ := P.betaFactorisation c de de' ka T T' Y l h hw hw' hT hT' hl hlk hne hY
  have hk4 : (4 : ℝ) ≤ c.k := by exact_mod_cast h.hk
  have hD := h.hDel
  have hD0 : 0 < c.Del := by linarith
  have hpb := P.Sz7.prodb_pos c h
  obtain ⟨hae, hUE⟩ := P.Sz7.edge_bound c de de' Y l h hw hw' hl hlk hY
  refine ⟨hae, ?_⟩
  have hNd := P.nodeBound c Y l h hl hlk hY
  have hNd0 : 0 ≤ c.Nd (-Y) := by
    simp only [Sz.Cfg.Nd]; exact prod_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hA := P.positionsBefore c de de' Y l h hw hw' hl hlk hY
  have hA0' : 0 ≤ ∏ i ∈ Ico 1 l, c.rho de de' (-Y) i :=
    prod_nonneg (fun i _ => P.Sz7.rho_nonneg c de de' Y l i h hlk hY)
  obtain ⟨-, hB⟩ := P.slotAt_true c de de' Y l h hw hw' hl hlk hne hY
  have hB0 := P.Sz7.rho_nonneg c de de' Y l l h hlk hY
  have hC : ∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i ≤ 1 := by
    apply prod_le_one
    · intro i _; exact P.Sz7.rho_nonneg c de de' Y l i h hlk hY
    · intro i hi
      rw [mem_Ico] at hi
      exact P.positionAfter c de de' Y l i h hw hw' hl (by omega) (by omega) (Or.inl (by omega)) hY
  have hC0 : 0 ≤ ∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i :=
    prod_nonneg (fun i _ => P.Sz7.rho_nonneg c de de' Y l i h hlk hY)
  have hE0 := P.Sz7.rho_nonneg c de de' Y l (c.k - 1) h hlk hY
  obtain ⟨hU0, -, -⟩ := P.edgeFactorBound c Y l h hl hlk hY
  have hd0 : 0 ≤ (c.v l + Y) / c.Del := by
    have := hY.1; apply div_nonneg <;> linarith
  have hsq : Real.sqrt (14 * (c.v l + Y) / (5 * c.Del)) =
      Real.sqrt (14 / 5) * Real.sqrt ((c.v l + Y) / c.Del) := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; field_simp
  rw [hsq] at hB
  have hsd0 := Real.sqrt_nonneg ((c.v l + Y) / c.Del)
  rw [hbe, P.Sz7.prod_split _ c.k l hl hlk]
  generalize (∏ i ∈ Ico 1 l, c.rho de de' (-Y) i) = A at *
  generalize (∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i) = Cc at *
  generalize c.rho de de' (-Y) l = B at *
  generalize c.rho de de' (-Y) (c.k - 1) = E at *
  generalize c.Nd (-Y) = Nd at *
  generalize c.U1 (-Y) = U at *
  generalize Real.sqrt ((c.v l + Y) / c.Del) = sd at *
  have hS : 0 < Real.sqrt (T * T') := Real.sqrt_pos.mpr (mul_pos hT hT')
  generalize Real.sqrt (T * T') = S at *
  have hsk : 0 ≤ Real.sqrt (c.k : ℝ) := Real.sqrt_nonneg _
  have hs145 : 0 ≤ Real.sqrt (14 / 5 : ℝ) := Real.sqrt_nonneg _
  have heth : 0 < Real.exp c.vth := Real.exp_pos _
  generalize Real.sqrt (c.k : ℝ) = sk at *
  generalize Real.sqrt (14 / 5 : ℝ) = s145 at *
  generalize Real.exp c.vth = eth at *
  have step : Nd * U * (A * (B * (Cc * E))) ≤
      (eth * c.prodb) * (8 / c.aeff) * (3.3 * sk) * (s145 * sd) := by
    have p1 : Nd * (U * E) ≤ (eth * c.prodb) * (8 / c.aeff) :=
      mul_le_mul hNd hUE (mul_nonneg hU0.le hE0) (by positivity)
    have p2 : Nd * (U * E) * A ≤ (eth * c.prodb) * (8 / c.aeff) * (3.3 * sk) :=
      mul_le_mul p1 hA hA0' (by positivity)
    have p3 : Nd * (U * E) * A * B ≤ (eth * c.prodb) * (8 / c.aeff) * (3.3 * sk) * (s145 * sd) :=
      mul_le_mul p2 hB hB0 (by positivity)
    have p4 : Nd * (U * E) * A * B * Cc ≤ Nd * (U * E) * A * B * 1 :=
      mul_le_mul_of_nonneg_left hC
        (mul_nonneg (mul_nonneg (mul_nonneg hNd0 (mul_nonneg hU0.le hE0)) hA0') hB0)
    calc Nd * U * (A * (B * (Cc * E))) = Nd * (U * E) * A * B * Cc := by ring
      _ ≤ _ := by linarith
  calc g ^ c.m * ((ka ^ (c.m - 1))⁻¹ * S⁻¹ * Nd * U * (A * (B * (Cc * E))))
      = g ^ c.m * (ka ^ (c.m - 1))⁻¹ * S⁻¹ * (Nd * U * (A * (B * (Cc * E)))) := by ring
    _ ≤ g ^ c.m * (ka ^ (c.m - 1))⁻¹ * S⁻¹ *
          ((eth * c.prodb) * (8 / c.aeff) * (3.3 * sk) * (s145 * sd)) :=
        mul_le_mul_of_nonneg_left step (by positivity)
    _ = _ := by ring

theorem Tr_pos (D : D7) (u : D.what₂.Word) : 0 < Tr D u := by
  unfold Tr
  exact_mod_cast (D.mem u).A.T_prime.pos

theorem Vand_lam_pos (c : Sz.Cfg) (h : c.Ok) : 0 < Sz.Vand (c.k + c.m - 1) c.lam := by
  cases h with
  | mk hk hm hDel hv0 hv1 hb1 hgap =>
    have hv : ∀ i : ℕ, c.v i = c.vlast + 4 * c.Del * ((c.k : ℝ) - 1 - i) := by
      intro i
      simp only [Formalism.FourierDecayAlt.Sz.Cfg.v]
    have hb : ∀ a d : ℕ, 1 ≤ a → a + d ≤ c.m → c.b a + d ≤ c.b (a + d) := by
      intro a d ha hd
      induction d with
      | zero => simp
      | succ d ih =>
        have h1 := ih (by omega)
        have h2 := hgap (a + d) (by omega) (by omega)
        have e : a + (d + 1) = a + d + 1 := by omega
        rw [e]
        push_cast
        linarith
    have hD : (0 : ℝ) < c.Del := by linarith
    have hlam : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ c.k + c.m - 1 → c.lam j < c.lam i := by
      intro i j hi hij hj
      unfold Formalism.FourierDecayAlt.Sz.Cfg.lam
      by_cases hjk : j < c.k
      · have hik : i < c.k := by omega
        rw [if_pos hjk, if_pos hik, hv, hv]
        have hij' : (i : ℝ) < j := by exact_mod_cast hij
        have h4 : 0 < 4 * c.Del * ((j : ℝ) - i) := by
          apply mul_pos
          · linarith
          · linarith
        linarith
      · rw [if_neg hjk]
        by_cases hik : i < c.k
        · rw [if_pos hik, hv]
          have h1 := hb 1 (j + 1 - c.k - 1) le_rfl (by omega)
          have e : 1 + (j + 1 - c.k - 1) = j + 1 - c.k := by omega
          rw [e] at h1
          have h2 : (i : ℝ) ≤ c.k - 1 := by
            have h5 : ((i + 1 : ℕ) : ℝ) ≤ c.k := by exact_mod_cast (show i + 1 ≤ c.k by omega)
            push_cast at h5
            linarith
          have h3 : (0 : ℝ) ≤ ((j + 1 - c.k - 1 : ℕ) : ℝ) := by positivity
          have h4 : 0 ≤ 4 * c.Del * ((c.k : ℝ) - 1 - i) := by
            apply mul_nonneg
            · linarith
            · linarith
          linarith
        · rw [if_neg hik]
          have h1 := hb (i + 1 - c.k) (j - i) (by omega) (by omega)
          have e : i + 1 - c.k + (j - i) = j + 1 - c.k := by omega
          rw [e] at h1
          have h3 : (1 : ℝ) ≤ ((j - i : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j - i by omega)
          linarith
    unfold Formalism.FourierDecayAlt.Sz.Vand
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_Ioc] at hj
    exact sub_pos.2 (hlam i j hi.1 hj.1 hj.2)

theorem sze_facts {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ}
    (hh : LocalBesselAndTopKernel.hyp D large₂ C0 C' Cl Cg cb Cu cT CT) :
    (∀ (τ : D.what₂.Tau) (w : D.what₂.Word), ¬ IsTop D τ → uOne D w τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2) ∧
      1 ≤ D.host.v ∧ 25 ≤ gg D := by
  obtain ⟨hD, hH, -⟩ := hh
  unfold StandingNumericalData at hD
  obtain ⟨-, -, -, -, d5, -⟩ := hD
  unfold StandingHypotheses at hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -, h14, -, -, -, -, h19, -⟩ := hH
  refine ⟨fun τ w => d5 w τ, h19, ?_⟩
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast five_le_k D
  have hb := (one_lt_b large₂).le
  have hkb : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have h5 : (5 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    calc (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := hkb
      _ = ((D.R.k : ℝ) * large₂.sc.b) ^ 1 := (pow_one _).symm
      _ ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  unfold gg
  have a1 : (5 : ℝ) ≤ D.host.g 0 := le_trans h5 h12
  have a2 : (5 : ℝ) ≤ D.host.g 1 := le_trans h5 h14
  nlinarith

theorem ka_pos_of {D : D7} (hv : 1 ≤ D.host.v) : 0 < D.host.ka := by
  exact div_pos Real.pi_pos (by linarith)

theorem two_le_sqrt_k (D : D7) : 2 ≤ Real.sqrt (D.R.k : ℝ) := by
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  have hk : (4 : ℝ) ≤ D.R.k := by exact_mod_cast (show 4 ≤ D.R.k by omega)
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← h4]
  exact Real.sqrt_le_sqrt hk

theorem mem_cutI (D : D7) (τ : D.what₂.Tau) (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ D.R.k - 2) (d : ℝ) (hd1 : 5 / 2 ≤ d)
    (hd2 : d ≤ (D.s.Del : ℝ) / 2) :
    (cfgOf D τ).v l + (d - vOne D τ l) = d ∧ (d - vOne D τ l) ∈ (cfgOf D τ).cutI l := by
  have hv := cfg_v D τ l h1 (by omega)
  have hD : (cfgOf D τ).Del = (D.s.Del : ℝ) := rfl
  refine ⟨by rw [hv]; ring, ?_⟩
  show 5 / 2 ≤ (cfgOf D τ).v l + (d - vOne D τ l) ∧ (cfgOf D τ).v l + (d - vOne D τ l) ≤ (cfgOf D τ).Del / 2
  rw [hv, hD]
  constructor <;> linarith

theorem level_exponent_of_lower_bound {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT C3' C4 : ℝ} (h40 : 40 ≤ Cl)
    (hC : C3' + 3 ≤ C4) : LocalBesselAndTopKernel.LowerVolumeImpliesUpper D large₂ C0 C' Cl Cg cb Cu cT CT C3' C4 := by
  intro hh h2d u u' τ l hl1 hl2 hne d hd1 hd2
  obtain ⟨h5, hv, hg⟩ := sze_facts hh
  have hk5 := five_le_k D
  have hok := cfg_ok hh.1 hh.2.1 τ
  have hka0 := ka_pos_of hv
  have hg0 : 0 < gg D := by linarith
  obtain ⟨ed, hY⟩ := mem_cutI D τ l hl1 hl2 d hd1 hd2
  obtain ⟨hae, key⟩ := beta_le_X (cfgOf D τ) (deOf D u) (deOf D u') D.host.ka (gg D) (Tr D u) (Tr D u')
    (d - vOne D τ l) l hok (isWord_deOf D u) (isWord_deOf D u') hka0 hg0 (Tr_pos D u) (Tr_pos D u') hl1
    (by show l + 2 ≤ D.R.k; omega) (deOf_ne D u u' τ (h5 τ) l hl1 hl2 hne) hY
  rw [← beUU_eq D u u' τ (h5 τ), ed] at key
  have hvth := (cfg_small hh.2.1 h40 τ).hvth
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hk0 : (0 : ℝ) < D.R.k := by linarith

  have hm1 : 1 ≤ D.R.m := le_trans (by norm_num) D.R.two_le_m
  have eka : D.host.ka ^ (-((D.R.m : ℝ) - 1)) = (D.host.ka ^ (D.R.m - 1))⁻¹ := by
    rw [Real.rpow_neg hka0.le, ← Real.rpow_natCast, Nat.cast_sub hm1]
    simp
  have low : ∀ w : D.what₂.Word,
      (gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ * (cfgOf D τ).prodb / (cfgOf D τ).aeff) *
        (D.R.k : ℝ) ^ (-C3') ≤ Tcrit D w τ := by
    intro w
    have := h2d w τ
    rw [eka, ← cfg_prodb, ← cfg_aeff D w τ] at this
    calc _ = gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ * (cfgOf D τ).prodb * (D.R.k : ℝ) ^ (-C3') /
          (cfgOf D τ).aeff := by ring
      _ ≤ _ := this
  have t1 := low u
  have t2 := low u'
  change gg D ^ D.R.m * beUU D D.host.ka u u' τ (d - vOne D τ l) ≤
    (gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ * (cfgOf D τ).prodb / (cfgOf D τ).aeff) *
      ((Real.sqrt (Tr D u * Tr D u'))⁻¹ * Real.exp (cfgOf D τ).vth * 8 * 3.3 * Real.sqrt (D.R.k : ℝ) *
        Real.sqrt (14 / 5) * Real.sqrt (d / (D.s.Del : ℝ))) at key
  have hX0 : 0 ≤ gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ * (cfgOf D τ).prodb / (cfgOf D τ).aeff := by
    have := P.Sz7.prodb_pos _ hok
    positivity
  generalize gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ * (cfgOf D τ).prodb / (cfgOf D τ).aeff = X at *
  refine le_trans key ?_
  unfold tV
  have hkn : 0 < (D.R.k : ℝ) ^ (-C3') := Real.rpow_pos_of_pos hk0 _
  have hXk : 0 ≤ X * (D.R.k : ℝ) ^ (-C3') := mul_nonneg hX0 hkn.le
  have hR : X * (D.R.k : ℝ) ^ (-C3') ≤ Real.sqrt (Tcrit D u τ * Tcrit D u' τ) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq]
    exact mul_le_mul t1 t2 hXk (hXk.trans t1)
  rw [Real.sqrt_div (mul_nonneg (hXk.trans t1) (hXk.trans t2))]
  have hS : 0 < Real.sqrt (Tr D u * Tr D u') := Real.sqrt_pos.mpr (mul_pos (Tr_pos D u) (Tr_pos D u'))
  have hX' : X ≤ Real.sqrt (Tcrit D u τ * Tcrit D u' τ) * (D.R.k : ℝ) ^ C3' := by
    have e : (D.R.k : ℝ) ^ (-C3') * (D.R.k : ℝ) ^ C3' = 1 := by
      rw [← Real.rpow_add hk0]; simp
    calc X = X * (D.R.k : ℝ) ^ (-C3') * (D.R.k : ℝ) ^ C3' := by rw [mul_assoc, e, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hR (Real.rpow_pos_of_pos hk0 _).le
  have hR0 := Real.sqrt_nonneg (Tcrit D u τ * Tcrit D u' τ)
  generalize Real.sqrt (Tcrit D u τ * Tcrit D u' τ) = R at *
  generalize Real.sqrt (Tr D u * Tr D u') = S at *
  have hsd := Real.sqrt_nonneg (d / (D.s.Del : ℝ))
  generalize Real.sqrt (d / (D.s.Del : ℝ)) = sd at *

  have hexp : Real.exp (cfgOf D τ).vth ≤ 10 / 9 := by
    calc Real.exp (cfgOf D τ).vth ≤ Real.exp (1 / 10) := Real.exp_le_exp.2 hvth
      _ ≤ 1 / (1 - 1 / 10) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = 10 / 9 := by norm_num
  have hexp0 := Real.exp_pos (cfgOf D τ).vth
  generalize Real.exp (cfgOf D τ).vth = eth at *
  have h145 : Real.sqrt (14 / 5 : ℝ) ≤ 1.7 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h1450 := Real.sqrt_nonneg (14 / 5 : ℝ)
  generalize Real.sqrt (14 / 5 : ℝ) = s145 at *
  have hs2 := two_le_sqrt_k D
  have hss : Real.sqrt (D.R.k : ℝ) * Real.sqrt (D.R.k : ℝ) = D.R.k := Real.mul_self_sqrt hk0.le
  have hk5' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
  have hpow : (D.R.k : ℝ) ^ C3' * (D.R.k : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ C4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hk0]
    exact Real.rpow_le_rpow_of_exponent_le hk1 (by push_cast; linarith)
  have hkC := Real.rpow_pos_of_pos hk0 C3'
  generalize (D.R.k : ℝ) ^ C3' = kC at *
  generalize (D.R.k : ℝ) ^ C4 = kC4 at *
  generalize Real.sqrt (D.R.k : ℝ) = sk at *
  generalize (D.R.k : ℝ) = kk at *
  have hconst : eth * 8 * 3.3 * s145 ≤ 50 := by
    have : eth * s145 ≤ 10 / 9 * 1.7 := mul_le_mul hexp h145 h1450 (by norm_num)
    nlinarith
  have hsk3 : 50 * sk ≤ kk ^ 3 := by
    have : kk ^ 3 = kk * kk * (sk * sk) := by rw [hss]; ring
    rw [this]
    have h25 : 25 ≤ kk * kk := by nlinarith
    have : 2 * sk ≤ sk * sk := by nlinarith
    nlinarith
  have hK : eth * 8 * 3.3 * sk * s145 ≤ kk ^ 3 := by
    calc eth * 8 * 3.3 * sk * s145 = (eth * 8 * 3.3 * s145) * sk := by ring
      _ ≤ 50 * sk := mul_le_mul_of_nonneg_right hconst (by linarith)
      _ ≤ kk ^ 3 := hsk3
  have hK0 : 0 ≤ eth * 8 * 3.3 * sk * s145 := by positivity
  calc X * (S⁻¹ * eth * 8 * 3.3 * sk * s145 * sd)
      = X * ((eth * 8 * 3.3 * sk * s145) * (S⁻¹ * sd)) := by ring
    _ ≤ (R * kC) * (kk ^ 3 * (S⁻¹ * sd)) :=
        mul_le_mul hX' (mul_le_mul_of_nonneg_right hK (by positivity)) (by positivity) (by positivity)
    _ = (kC * kk ^ 3) * (R * S⁻¹ * sd) := by ring
    _ ≤ kC4 * (R * S⁻¹ * sd) := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = R / S * kC4 * sd := by rw [div_eq_mul_inv]; ring

theorem level_exponent_of_formal_degree {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT ep0 CV C4 : ℝ} (h40 : 40 ≤ Cl)
    (hep : ep0 ≤ 1 / 2) (hC : 4 ≤ C4) (hh : LocalBesselAndTopKernel.hyp D large₂ C0 C' Cl Cg cb Cu cT CT) (h2g : LocalBesselAndTopKernel.MidVolumeChain D large₂ ep0 CV) :
    LocalBesselAndTopKernel.BesselBoundOneSlotDifference D C4 := by
  intro u u' τ l hl1 hl2 hne d hd1 hd2
  obtain ⟨h5, hv, hg⟩ := sze_facts hh
  have hk5 := five_le_k D
  have hok := cfg_ok hh.1 hh.2.1 τ
  have hsm := cfg_small hh.2.1 h40 τ
  have hka0 := ka_pos_of hv
  obtain ⟨ed, hY⟩ := mem_cutI D τ l hl1 hl2 d hd1 hd2
  have hFD : Sz.FormalDegreeLower (cfgOf D τ) (1 / 2) (VV D τ) := by
    unfold Sz.FormalDegreeLower
    have hp := Vand_lam_pos _ hok
    have := (h2g τ).1
    rw [← Vand_lam] at this
    nlinarith
  have key := P.beta_bound_on_boundary (cfgOf D τ) D.R.rS large₂.sc.b (deOf D u) (deOf D u') D.host.ka D.host.rdE (gg D)
    (VV D τ) (Tr D u) (Tr D u') (d - vOne D τ l) l hok (m_eq D) hsm (isWord_deOf D u) (isWord_deOf D u')
    (by rw [rdE_eq]; linarith) (ka_eq D) (by have := Real.pi_lt_four; linarith) hFD (Tr_pos D u) (Tr_pos D u') hl1
    (by show l + 2 ≤ D.R.k; omega) (deOf_ne D u u' τ (h5 τ) l hl1 hl2 hne) hY
  rw [← beUU_eq D u u' τ (h5 τ), ed] at key
  have etv : Sz.tv (cfgOf D τ) (deOf D u) (deOf D u') D.host.ka D.host.rdE (gg D) (VV D τ) (Tr D u) (Tr D u') =
      tV D u u' τ := by
    unfold Sz.tv tV
    show Real.sqrt (Sz.Tcrit D.R.k D.R.m D.host.ka D.host.rdE (gg D) (VV D τ)
        (Sz.Vand D.R.k ((cfgOf D τ).u (deOf D u))) *
      Sz.Tcrit D.R.k D.R.m D.host.ka D.host.rdE (gg D) (VV D τ)
        (Sz.Vand D.R.k ((cfgOf D τ).u (deOf D u'))) / _) = _
    rw [Vand_u D u τ (h5 τ u), Vand_u D u' τ (h5 τ u'), Tcrit_eq D u τ hka0.le, Tcrit_eq D u' τ hka0.le]
  rw [etv] at key
  obtain ⟨hA0, hA⟩ := P.a_zero_le_one_sixty (cfgOf D τ) large₂.sc.b hok hsm
  refine le_trans key ?_
  change Sz.AZero (cfgOf D τ) large₂.sc.b * tV D u u' τ * Real.sqrt (D.R.k : ℝ) * Real.sqrt (d / (D.s.Del : ℝ)) ≤ _
  have htv : 0 ≤ tV D u u' τ := Real.sqrt_nonneg _
  have hsd := Real.sqrt_nonneg (d / (D.s.Del : ℝ))
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hk0 : (0 : ℝ) < D.R.k := by linarith
  have hs2 := two_le_sqrt_k D
  have hss : Real.sqrt (D.R.k : ℝ) * Real.sqrt (D.R.k : ℝ) = D.R.k := Real.mul_self_sqrt hk0.le
  have hk5' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
  have hpow : (D.R.k : ℝ) ^ 4 ≤ (D.R.k : ℝ) ^ C4 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hk1 (by push_cast; linarith)
  have hsk : 160 * Real.sqrt (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ 4 := by
    have e : (D.R.k : ℝ) ^ 4 = (D.R.k : ℝ) * D.R.k * D.R.k * (Real.sqrt (D.R.k : ℝ) * Real.sqrt (D.R.k : ℝ)) := by
      rw [hss]; ring
    rw [e]
    have h125 : 125 ≤ (D.R.k : ℝ) * D.R.k * D.R.k := by nlinarith [mul_self_nonneg ((D.R.k : ℝ) - 5)]
    have : 2 * Real.sqrt (D.R.k : ℝ) ≤ Real.sqrt (D.R.k : ℝ) * Real.sqrt (D.R.k : ℝ) := by nlinarith
    nlinarith
  calc Sz.AZero (cfgOf D τ) large₂.sc.b * tV D u u' τ * Real.sqrt (D.R.k : ℝ) * Real.sqrt (d / (D.s.Del : ℝ))
      = (Sz.AZero (cfgOf D τ) large₂.sc.b * Real.sqrt (D.R.k : ℝ)) * (tV D u u' τ * Real.sqrt (d / (D.s.Del : ℝ))) := by
        ring
    _ ≤ (D.R.k : ℝ) ^ C4 * (tV D u u' τ * Real.sqrt (d / (D.s.Del : ℝ))) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg htv hsd)
        calc Sz.AZero (cfgOf D τ) large₂.sc.b * Real.sqrt (D.R.k : ℝ) ≤ 160 * Real.sqrt (D.R.k : ℝ) :=
              mul_le_mul_of_nonneg_right hA (by linarith)
          _ ≤ _ := hsk.trans hpow
    _ = _ := by ring

section Family

variable {eps : ℝ} {Fm : FamP eps}

theorem family_exponent_of_lower_bound {C0 Cg cb Cu cT CT C3' C4 : ℝ} (h40 : 40 ≤ sCl Fm) (hC : C3' + 3 ≤ C4)
    (h : LocalBesselAndTopKernel.LocalSplitExponents Fm C0 Cg cb Cu cT CT C3') : LocalBesselAndTopKernel.SchurOrthogonalityRealPlace Fm C0 Cg cb Cu cT CT C4 := by
  obtain ⟨x0, H⟩ := h
  exact ⟨x0, fun x hx i hh => level_exponent_of_lower_bound h40 hC hh (H x hx i hh)⟩

theorem family_exponent_of_formal_degree {C0 Cg cb Cu cT CT ep0 CV C4 : ℝ} (h40 : 40 ≤ sCl Fm) (hep : ep0 ≤ 1 / 2) (hC : 4 ≤ C4)
    (h : LocalBesselAndTopKernel.FamilyTopBound Fm C0 Cg cb Cu cT CT ep0 CV) : LocalBesselAndTopKernel.SchurOrthogonalityRealPlace Fm C0 Cg cb Cu cT CT C4 := by
  obtain ⟨x0, H⟩ := h
  exact ⟨x0, fun x hx i hh => level_exponent_of_formal_degree h40 hep hC hh (H x hx i hh)⟩

end Family

end Formalism.MainNotions.BridgeLemma

end
