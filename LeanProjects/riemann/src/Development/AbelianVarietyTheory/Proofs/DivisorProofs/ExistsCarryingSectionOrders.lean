import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionWeightBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyUnitPowTwistingSectionOnComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemCuspFormsOfBoundedSectionComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaBoundLengthUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqThetaConstantSpanningClassesLeExpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentialVolumeSmallStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentialVolumeLargeStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovHt.KeySection

open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.ThetaConst GlobalTheory.EtaForm

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

variable (Dw) in

theorem wtZ_zero_eq (m : ℕ) : wtZ (0 : (E →+* ℂ) × ℕ → ℕ) (2 * m) = wtOf Dw (weightOf Dw 0 m) m := by
  refine Prod.ext (funext fun x => ?_) (by simp [wtZ, wtOf])
  simp only [wtZ, wtOf, weightOf]
  split_ifs <;> simp <;> omega

theorem nsmul_wtOf (k : ℕ) (la : AllWt.Weight Dw) (m : ℤ) : k • wtOf Dw la m = wtOf Dw (k • la) (k * m) := by
  induction k with
  | zero => simp [wtOf_zero]
  | succ k ih => rw [succ_nsmul, ih, ← wtOf_add, succ_nsmul]; congr 1; push_cast; ring

theorem homN_pow {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ) {G : WTZ E} (hG : Even G.2) (f : Rul Xo c)
    (z : Σ k, Frame (U.X k).Ψ r) (hz : z.2 ∈ (U.X z.1).dom) (k : ℕ) :
    homN U x ((k + 1) • G) (f ^ (k + 1)) z = homN U x G f z ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, pow_succ, homN_mul U x (by simpa using hG.mul_left _) hG _ _ z hz, ih, ← pow_succ]

theorem le_val_pow {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] {la : HeightOneSpectrum (𝓞 K)}
    {v : R → EReal} (hv : IsVal la v) {f : R} {a : ℝ} (h : (a : EReal) ≤ v f) (k : ℕ) :
    (((k + 1 : ℕ) * a : ℝ) : EReal) ≤ v (f ^ (k + 1)) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ, hv.mul]
    refine le_trans (le_of_eq ?_) (add_le_add ih h)
    rw [← EReal.coe_add]
    congr 1
    push_cast
    ring

theorem wtOf_hodge_anti (n : ℕ) (τ : E →+* ℂ) (i j : ℕ) (hij : i ≤ j) :
    (wtOf Dw ((n : ℤ) • hodgeWt Dw) 0).1 (τ, j) ≤ (wtOf Dw ((n : ℤ) • hodgeWt Dw) 0).1 (τ, i) := by
  simp only [wtOf, hodgeWt, barWt, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp_all <;> omega

theorem pow_mul_mem {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {Z : Comp Xo c} {G₀ : WTZ E} (h₀ : Even G₀.2) {θ : Rul Xo c}
    (h : ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * θ ∈ cuspOn U Z (G + G₀)) (k : ℕ) {G : WTZ E} (hG : Even G.2)
    {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) : θ ^ k * f ∈ cuspOn U Z (G + k • G₀) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    have := h _ (hG.add (by simpa using h₀.mul_left _)) _ ih
    rwa [add_assoc, ← succ_nsmul, mul_right_comm, ← pow_succ] at this

theorem cost_const {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {Z : Comp Xo c} {la : AllWt.Weight Dw}
    (S : ConstSec U x Z la 0) (s : ℝ) : ∃ e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ, (∀ w, e w = -S.rho_vw w / 8) ∧
      cost e (fun σ => s + Real.log (S.cInf σ) / 8) = s - S.deg / 8 := by
  have hfin : (Function.support fun w => -S.rho_vw w / 8).Finite :=
    S.finite_rho.subset fun w hw h0 => hw (by simp [h0])
  refine ⟨Finsupp.ofSupportFinite _ hfin, fun _ => rfl, ?_⟩
  have hn : (Module.finrank ℚ c.F : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have h1 : ∑ᶠ w, S.rho_vw w * lw c.F w = ∑ w ∈ hfin.toFinset, S.rho_vw w * lw c.F w :=
    finsum_eq_sum_of_support_subset _ fun w hw => by
      simp only [Set.Finite.coe_toFinset, Function.mem_support] at hw ⊢
      intro h0
      exact hw (by rw [show S.rho_vw w = 0 by linarith, zero_mul])
  have h2 : ((Finsupp.ofSupportFinite _ hfin).sum fun w a => a * Real.log (Ideal.absNorm w.asIdeal : ℝ)) =
      -(Module.finrank ℚ c.F : ℝ) / 8 * ∑ w ∈ hfin.toFinset, S.rho_vw w * lw c.F w := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    show -S.rho_vw w / 8 * _ = _
    unfold lw
    field_simp
  unfold cost ConstSec.deg lineDeg
  rw [h1, h2, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul]
  field_simp
  ring

theorem exists_twist {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x om : ℝ} (h : FlatDegree U x om) (Z : Comp Xo c)
    (hZ : HasPts U Z) (n : ℤ) : ∃ S : ConstSec U x Z (parWt Dw fun _ => -n) 0,
      S.deg = n * (Fintype.card (Psi H) * (((Dw.p : ℝ) - Dw.q) / 2 * om)) := by
  have s : ∀ τ, FlatSec U x Z τ := fun τ => (h Z τ).1.some
  refine ⟨(ConstSec.prod hZ Finset.univ fun τ => (s τ).toFrame.zpow n).copy
    (by rw [parWt_eq_sum]; simp only [neg_neg]; convert rfl) (by simp), ?_⟩
  refine (ConstSec.prod_spec hZ Finset.univ fun τ => (s τ).toFrame.zpow n).2.2.2.2.trans ?_
  have : ∀ τ, ((s τ).toFrame.zpow n).deg = n * (((Dw.p : ℝ) - Dw.q) / 2 * om) := fun τ => by
    have h1 := (h Z τ).2 (s τ)
    rw [FlatSec.deg_eq_toFrame, neg_neg, flatDegVal] at h1
    rw [(ConstSec.zpow_spec _ _).2.2.2, add_right_cancel h1]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Free

set_option maxHeartbeats 1000000 in

theorem exists_section {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (hL : GlobalTheory.FlatCore.Laws U x) (hM : 5 ^ 4 ∣ l.M) (Z : Comp Xo c)
    (S : ConstSec U x Z (parWt Dw fun _ => -(12 * ((Dw.p + Dw.q : ℕ) : ℤ))) 0) (u : AllWt.Weight Dw) (β A : ℝ)
    (hb : ∀ (xs : Fin (Dw.p + Dw.q) → LatMod Dw (5 ^ 4)) (f : Rul Xo c), Submodule.span (𝓞 D.host.E) (Set.range xs) = ⊤ →
      IsTauRule Xo c 5 (fun _ : Unit => 1) (fun _ => xs) f → ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X,
      (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
        homN (U σ) x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) ⟨y.1, y.2.1⟩ ≤ A ∧
        ENNReal.ofReal (homN (U σ) x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) ⟨y.1, y.2.1⟩) ^ 3 ≤
          ENNReal.ofReal (Real.exp β) * bergOn (U σ) (V σ) (dict σ) Z (wtOf Dw u 0) y) :
    ∃ (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) (t : (c.F →+* ℂ) → ℝ), Carries U Z u (uPrime Dw u) θ ∧
      (∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ →
        ∀ y : IntFr Xo c T io, y.IsAlg → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ →
          ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧
      InfBd U x V dict Z (wtOf Dw u 0) (wtOf Dw ((8 : ℤ) • (u - uPrime Dw u)) 0) 8 θ t ∧
      cost e t = β / 2 + ((3 * (Dw.p + Dw.q) : ℕ) : ℝ) *
        (2 * ((Nat.card (Psi H) * (Dw.p + Dw.q) : ℕ) : ℝ) * Real.log (2 * Real.pi)) / 8 - S.deg / 8 := by
  have h5 : Odd 5 := by decide
  obtain ⟨hks, hK⟩ := GlobalTheory.KeyPowTw.exists_twSec_keyPow _ H Dw l Xo c r U x hL.unf hL.xi hL.geo hL.pos hL.good
  obtain ⟨K, hK0, hK1⟩ := hK Z (3 * (Dw.p + Dw.q))
  set κ : ℝ := ((3 * (Dw.p + Dw.q) : ℕ) : ℝ) *
    (2 * ((Nat.card (Psi H) * (Dw.p + Dw.q) : ℕ) : ℝ) * Real.log (2 * Real.pi)) with hκ
  obtain ⟨x₀, hx₀⟩ := exists_isAdm Dw (R := 5) (by norm_num)
  obtain ⟨w, f, hf, hfZ⟩ := exists_isGenRule_nonzeroOn (Xo := Xo) (c := c) h5 (by norm_num) hM x₀ Z
  have hsp := hx₀.spans (by norm_num) w
  replace hb := hb _ f hsp hf
  obtain ⟨e, he, hc⟩ := cost_const S (β / 2 + κ / 8)
  have hw : (8 : ℤ) • (u - uPrime Dw u) = ((24 * (Dw.p + Dw.q) : ℕ) : ℤ) • hodgeWt Dw := by
    rw [uPrime, sub_sub_cancel, smul_smul]
    congr 1
    push_cast
    ring
  have hG : (11 + 1) • wtZ (0 : (D.host.E →+* ℂ) × ℕ → ℕ) (2 * (Dw.p + Dw.q)) +
      wtOf Dw 0 (-(4 * ((3 * (Dw.p + Dw.q) : ℕ) : ℤ))) + wtOf Dw (parWt Dw fun _ => -(12 * ((Dw.p + Dw.q : ℕ) : ℤ))) 0 =
      wtOf Dw ((8 : ℤ) • (u - uPrime Dw u)) 0 := by
    rw [wtZ_zero_eq Dw, nsmul_wtOf, ← wtOf_add, ← wtOf_add, hw]
    congr 1
    · funext τ j
      simp only [weightOf, hodgeWt, barWt, parWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
      split_ifs <;> push_cast <;> ring
    · push_cast
      ring
  have hev : Even (wtZ (0 : (D.host.E →+* ℂ) × ℕ → ℕ) (2 * (Dw.p + Dw.q))).2 := by
    rw [wtZ_zero_eq Dw]; exact even_wtOf _ _
  have hev' : Even ((11 + 1) • wtZ (0 : (D.host.E →+* ℂ) × ℕ → ℕ) (2 * (Dw.p + Dw.q))).2 := by
    rw [wtZ_zero_eq Dw, nsmul_wtOf]; exact even_wtOf _ _
  have hf2 : f ^ 2 ∈ secZ Xo c (exZ Dw (wtZ 0 (2 * (Dw.p + Dw.q)))) := by
    have := IsTauRule.mem_sec h5 hf
    rw [← secZ_nat] at this
    convert pow_mem_secZ this 2 using 2
    funext i
    cases i <;> simp [exZ, wtZ, ex]
  have hmem : (f ^ 2) ^ (11 + 1) * K.sig * S.sig ∈ secZ Xo c (exZ Dw (wtOf Dw ((8 : ℤ) • (u - uPrime Dw u)) 0)) := by
    rw [← hG, exZ_add_eq, exZ_add_eq]
    refine mul_mem_secZ (mul_mem_secZ ?_ K.sig_mem) S.sig_mem
    convert pow_mem_secZ hf2 (11 + 1) using 2
    funext i
    cases i <;> simp [exZ, wtZ]
  have hsupp : (f ^ 2) ^ (11 + 1) * K.sig * S.sig ∈ suppOn Z := mul_mem_suppOn _ S.sig_mem_suppOn
  have hnorm : ∀ σ, GoodEmb c σ → ∀ z ∈ framesOn (U σ) Z,
      homN (U σ) x (wtOf Dw ((8 : ℤ) • (u - uPrime Dw u)) 0) ((f ^ 2) ^ (11 + 1) * K.sig * S.sig) z =
        homN (U σ) x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) z ^ (11 + 1) * K.cInf σ * S.cInf σ := fun σ hσ => by
    have h1 := fun z hz => S.homN_mul_sig (G := (11 + 1) • wtZ 0 (2 * (Dw.p + Dw.q)) +
      wtOf Dw 0 (-(4 * ((3 * (Dw.p + Dw.q) : ℕ) : ℤ)))) (hev'.add K.even) ((f ^ 2) ^ (11 + 1) * K.sig) (σ := σ) (z := z) hz
    have h2 := fun z hz => K.homN_mul_sig hev' ((f ^ 2) ^ (11 + 1)) (σ := σ) (z := z) hz
    rw [show goodOf c σ = σ from if_pos hσ] at h1 h2
    intro z hz
    rw [← hG, ← homN_pow (U σ) x hev _ z hz.1, ← h2 z hz]
    exact h1 z hz
  refine ⟨(f ^ 2) ^ (11 + 1) * K.sig * S.sig, e, _, ⟨hmem, ?_, fun k g hg => ?_⟩, ?_, ⟨fun σ => ?_, ?_⟩, hc⟩
  · have h1 := congrArg (genVal Z) K.mul_inv
    have h2 := congrArg (genVal Z) S.mul_inv
    rw [map_mul, genVal_idem] at h1 h2
    rw [map_mul, map_mul, map_pow, map_pow]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hfZ)) (left_ne_zero_of_mul_eq_one h1))
      (left_ne_zero_of_mul_eq_one h2)
  · have h1 := GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd _ H Dw l Xo c r U x Z _ _ hks hL.unf hL.pos (even_wtOf _ _)
      (fun τ i j hij _ => by rw [hw]; exact wtOf_hodge_anti _ τ i j hij) hmem hsupp fun σ hσ =>
        ⟨A ^ (11 + 1) * K.cInf σ * S.cInf σ, fun z hz => by
          rw [hnorm σ hσ z hz]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (homN_nonneg _ _ _ _ _) (hb σ hσ ⟨z.1, z.2, hz.1⟩ hz).1 _) (K.cInf_pos σ).le)
            (S.cInf_pos σ).le⟩
    have h2 := pow_mul_mem (even_wtOf _ _) h1 k (by rw [nsmul_wtOf]; exact even_wtOf _ _) hg
    convert h2 using 2
    rw [nsmul_wtOf, nsmul_wtOf, nsmul_wtOf, ← wtOf_add]
    congr 1
    · funext τ j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
      push_cast
      ring
  · intro la T io e₀ ho y hy φ hφ
    have hv : (fun g => nval T.V e₀ (evI y g)) ∈ valSet Xo c (algCls Xo c) la := ⟨PtV.mk la ho y hy () trivial, rfl⟩
    rcases mem_valOn_or (Z := Z) hv with hv | hv
    · have h1 : ((φ / 625 / e₀ : ℝ) : EReal) ≤ nval T.V e₀ (evI y f) := by
        by_cases h0 : evI y f = 0
        · rw [h0, nval_zero]; exact le_top
        · rw [nval_of_ne h0, EReal.coe_le_coe_iff]
          have := GlobalTheory.ThetaSteep.tau_bound y hφ h5 (by norm_num) (fun _ => hsp) hf h0
          exact div_le_div_of_nonneg_right (by push_cast at this; linarith) (Nat.cast_nonneg _)
      have h2 := le_val_pow (isVal_valOn hv) (le_val_pow (isVal_valOn hv) h1 1) 11
      have h3 := K.lo_le la _ hv
      have h4 := S.val_mul_sig ((f ^ 2) ^ (11 + 1) * K.sig) hv
      rw [(isVal_valOn hv).mul _ K.sig] at h4
      refine le_trans ?_ (le_of_le_of_eq (add_le_add (add_le_add h2 h3) le_rfl) h4.symm)
      rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff, he]
      have h6 : 0 ≤ φ / e₀ := div_nonneg hφ.nonneg (Nat.cast_nonneg _)
      have h7 := hK0 la
      simp only [Pi.zero_apply]
      push_cast
      rw [mul_div_assoc, div_right_comm]
      linarith
    · exact (hv _ hsupp).symm ▸ le_top
  · have h1 : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := Formalism.L2.Pj.goodOf_conj c σ
    obtain ⟨z, hz⟩ := (S.hasPts.1 σ).1
    have h2 := fun z hz => S.homN_eq (σ := (starRingEnd ℂ).comp σ) (z := z) hz
    rw [h1] at h2
    beta_reduce
    rw [← h2 z hz, S.homN_eq hz]
  · intro σ hσ y hy
    have h1 := pow_le_pow_left' (hb σ hσ y hy).2 8
    have ha := homN_nonneg (U σ) x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) ⟨y.1, y.2.1⟩
    have hk : K.cInf σ ≤ Real.exp κ := (Real.log_le_iff_le_exp (K.cInf_pos σ)).1 (hK1 σ)
    have hs := S.cInf_pos σ
    have hk0 := K.cInf_pos σ
    rw [hnorm σ hσ _ hy]
    generalize homN (U σ) x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) ⟨y.1, y.2.1⟩ = a at h1 ha
    have h2 : Real.exp (2 * (8 : ℕ) * (β / 2 + κ / 8 + Real.log (S.cInf σ) / 8)) =
        (Real.exp κ * S.cInf σ) ^ 2 * Real.exp β ^ 8 := by
      rw [← Real.exp_log hs, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.log_exp]
      congr 1
      push_cast
      ring
    rw [h2, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (Real.exp_pos β).le, mul_assoc (ENNReal.ofReal _),
      ← mul_pow]
    refine le_trans ?_ (mul_le_mul_right h1 _)
    rw [← pow_mul, ← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (a ^ (11 + 1) * K.cInf σ * S.cInf σ) ^ 2 ≤ (a ^ (11 + 1) * Real.exp κ * S.cInf σ) ^ 2 := by gcongr
      _ = _ := by ring

theorem theta_le_bergman : Hypotheses2 → HypothesesH → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP C =>
    ∀ u1, Quo p i PP u1 → ∃ β : ℝ, 0 ≤ β ∧ lenT p i PP * β ≤ C * unitE p ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂)
      (xs : Fin ((dat p i).p + (dat p i).q) → LatMod (dat p i) (5 ^ 4)) (f : Rul Y.d.Xo₂ Y.d.c₂),
      Submodule.span (𝓞 (Fm.D x ι).host.E) (Set.range xs) = ⊤ →
      IsTauRule Y.d.Xo₂ Y.d.c₂ 5 (fun _ : Unit => 1) (fun _ => xs) f → ∀ σ, GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X,
      (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z →
        homN (Y.U σ) (xiR (Fm.D x ι)) (wtZ 0 (2 * ((dat p i).p + (dat p i).q))) (f ^ 2) ⟨y.1, y.2.1⟩ ≤ Real.exp β ∧
        ENNReal.ofReal (homN (Y.U σ) (xiR (Fm.D x ι)) (wtZ 0 (2 * ((dat p i).p + (dat p i).q))) (f ^ 2) ⟨y.1, y.2.1⟩) ^ 3 ≤
          ENNReal.ofReal (Real.exp β) *
            bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  intro hP hH hD hS hF
  refine Closed.imp (Closed.and (GlobalTheory.T.eta_bound_length_unit hS) (Closed.and (GlobalTheory.T.frame_exponential_volume_large hP hH hD hS hF) (GlobalTheory.T.frame_exponential_volume_small hP hH hD hS hF))) ?_
  rintro eps Fm CH - ⟨⟨C₁, c₁, h₁⟩, ⟨_, -, h₂⟩, ⟨C₃, c₃, h₃⟩⟩
  obtain ⟨x0, h⟩ := h₁.and (h₂.and h₃)
  refine ⟨C₁ + C₃, add_nonneg c₁ c₃, x0, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h x hx hle ι p hp
  obtain ⟨a1, a2, a3, a4⟩ := h₁ i hi Y hY
  obtain ⟨B, b1, b2, b3⟩ := h₃ i hi Y hY u1 hu
  have hb : 1 ≤ (Fm.L x ι).sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x ι).sc.one_lt_alt]) _)
  obtain ⟨r1, r2⟩ := a4 1 le_rfl (by push_cast; exact one_le_pow₀ hb)
  refine ⟨_ + B, add_nonneg a2 b1, by rw [mul_add, add_mul]; exact add_le_add a3 b2, fun Z xs f hs hf σ hσ y hy => ?_⟩
  have d := GlobalTheory.T.normSq_thetaConstant_spanning_classes_le_exp _ _ _ _ _ _ σ _ (Y.U σ) (xiR (Fm.D x ι)) hσ (hY.1.unf σ hσ) 5 (by decide) (by norm_num) xs f hs hf
    _ _ _ _ r1 (Or.inr a1) ⟨y.1, y.2.1⟩ y.2.2
  have e2 := h₂ i hi Y hY u1 hu Z σ hσ y hy
  have e3 := b3 Z σ hσ y hy
  have e4 := r2 (((Y.U σ).X y.1).firstMinimumSq y.2.1)
  have ha := homN_nonneg (Y.U σ) (xiR (Fm.D x ι)) (wtZ 0 (2 * ((dat p i).p + (dat p i).q))) (f ^ 2) ⟨y.1, y.2.1⟩
  unfold ReciprocityTheory.ChartRestriction.G.I2.phiFD Data.la1 at d
  unfold Data.la1 at e2
  dsimp only at d
  generalize homN (Y.U σ) (xiR (Fm.D x ι)) (wtZ 0 (2 * ((dat p i).p + (dat p i).q))) (f ^ 2) ⟨y.1, y.2.1⟩ = a at d ha ⊢
  generalize bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y = G at e2 e3 ⊢
  generalize GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 = P
    at d a2 ⊢
  generalize hφ : 2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) /
    (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E ^ 2 * Real.sqrt (((Y.U σ).X y.1).firstMinimumSq y.2.1) ^ 2) = φ at d e2
  have φ0 : 0 ≤ φ := by rw [← hφ]; positivity
  have key : ∀ s t : ℝ, a ≤ Real.exp s → 3 * s ≤ P + B + t → ENNReal.ofReal (Real.exp t) ≤ G →
      ENNReal.ofReal a ^ 3 ≤ ENNReal.ofReal (Real.exp (P + B)) * G := fun s t h1 h2 h3 => by
    refine le_trans ?_ (mul_le_mul_right h3 _)
    rw [← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal ((pow_le_pow_left₀ ha h1 3).trans ?_)
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by exact_mod_cast h2)
  have d0 : a ≤ Real.exp (P / 625) := d.trans (Real.exp_le_exp.2 (by split_ifs <;> push_cast <;> linarith))
  refine ⟨d0.trans (Real.exp_le_exp.2 (by linarith)), ?_⟩
  rcases lt_or_ge ((Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1) (Fm.L x ι).sc.b with h | h
  · rw [if_pos (e4 h)] at d
    exact key _ _ d (by push_cast; linarith) (e2 h)
  · exact key _ _ d0 (by linarith) (e3 h)

theorem twist_cost_le {f r p q L om PP : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ L) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = r)
    (ho : |om| ≤ 3 * L) (hP : (f * r * L) ^ 12 ≤ PP) :
    3 * r * (2 * (f * r) * Real.log (2 * Real.pi)) / 8 - 12 * r * (f * ((p - q) / 2 * om)) / 8 ≤ 10 * PP := by
  have h1 : Real.log (2 * Real.pi) ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 * Real.pi by positivity)
    linarith [Real.pi_le_four]
  have h2 : -((p - q) / 2 * om) ≤ r / 2 * (3 * L) := by
    refine (neg_le_abs _).trans ?_
    rw [abs_mul]
    exact mul_le_mul (abs_le.2 ⟨by linarith, by linarith⟩) ho (abs_nonneg _) (by linarith)
  have hfr : 1 ≤ f * r := one_le_mul_of_one_le_of_one_le hf hr
  have hZ : 1 ≤ f * r * L := one_le_mul_of_one_le_of_one_le hfr hL
  have h3 : f * r * L * r ≤ PP := by
    refine le_trans ?_ ((pow_le_pow_right₀ hZ (by norm_num : 2 ≤ 12)).trans hP)
    rw [sq]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  have h4 : f * r * r ≤ f * r * L * r := by
    have : f * r ≤ f * r * L := le_mul_of_one_le_right (by linarith) hL
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have h5 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ f * r * r by positivity)
  have h6 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ f * r by positivity)
  nlinarith

set_option maxHeartbeats 1000000 in

theorem key_section : Hypotheses2 → HypothesesH → DeepGood → Size → FlatDeg → (Covers fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) := by
  intro hP hH hD hS hF
  refine Closed.imp (Closed.and (theta_le_bergman hP hH hD hS hF) (Closed.and hF (Closed.and hS
    (Closed.and (GlobalTheory.CovTop.Sizes.hostN 1) GlobalTheory.CovTop.WtShape.wtN)))) ?_
  rintro eps Fm CH - ⟨⟨C₁, c₁, h₁⟩, ⟨_, -, h₂⟩, ⟨_, -, h₃⟩, ⟨_, -, h₄⟩, ⟨_, -, h₅⟩⟩
  obtain ⟨x0, h⟩ := h₁.and (h₂.and (h₃.and (h₄.and h₅)))
  refine ⟨C₁ + 10, by linarith, x0, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h x hx hle ι p hp
  obtain ⟨β, b1, b2, b3⟩ := h₁ i hi Y hY u1 hu
  have hN := h₄ i
  have hW := h₅ i
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨by omega, by omega⟩ hY.1
  have hM : 5 ^ 4 ∣ Y.d.l₂.M := by
    rw [hY.1.lev.1.2.1, hY.1.pd]
    exact ((pow_dvd_pow_of_dvd (by norm_num : 5 ∣ 15) 4).trans
      (pow_dvd_pow 15 (GlobalTheory.ThetaSteep.four_le_expL hN.big.2.1))).mul_left _
  have hL1 : 1 ≤ (Fm.L x ι).sc.L := by linarith [hN.big.2.1]
  have hf : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast le_trans (by norm_num) hN.f8
  have hr : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hW.sig.2.2 ▸ hL.pos
  have hPP : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hN.ppLow
  have hT : lenT p i (Fm.parT x hx ι).PP * (Fm.parT x hx ι).PP ≤ unitE p := by
    have hD : (1 : ℝ) ≤ dimFlag (dat p i) := by
      rw [hW.dim]
      have m2 := (Fm.D x ι).R.two_le_m
      have k3 := (Fm.D x ι).R.m_add_three_le_k
      have f8 := hN.f8
      exact_mod_cast Nat.mul_pos (by omega) (Nat.choose_pos (by unfold Ranks.r; omega))
    refine le_trans ?_ (hW.what₂.2.trans (h₃ i).2.1)
    rw [mul_comm, mul_assoc _ _ (Fm.L x ι).sc.L]
    exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD) hL1)
  have hu0 : 0 ≤ (lenT p i (Fm.parT x hx ι).PP : ℝ) * β := by positivity
  refine ⟨β / 2 + 10 * (Fm.parT x hx ι).PP, by positivity, by linarith, fun Z => ?_⟩
  obtain ⟨S, hS⟩ := exists_twist (h₂ i hi Y hY) Z (hasPts Y.U hL.pos hL.good hL.unf Z)
    (12 * (((dat p i).p + (dat p i).q : ℕ) : ℤ))
  obtain ⟨θ, e, t, k1, k2, k3, k4⟩ := exists_section Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict hL hM Z
    S u1 β _ (b3 Z)
  refine ⟨θ, e, t, k1, fun la T io e₀ ho y hy _ => k2 la T io e₀ ho y hy, k3, ?_⟩
  have hc := twist_cost_le hf hr hL1 (Nat.cast_nonneg (dat p i).p) (Nat.cast_nonneg (dat p i).q)
    (by exact_mod_cast hW.sig.2.2) hW.om hN.ppLow
  rw [k4, hS, ← Nat.card_eq_fintype_card, hW.card, hW.sig.2.2]
  push_cast
  linarith

end GlobalTheory.CovHt.KeySection

end
