import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecEqOfSecBCIdOne
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FreqRealNonnegIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFjNeZeroAtSplitPoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TransvInOfHasPrinc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SumReCmTypeEqHalfTrace
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmLettersIsLieBasisAlongArcStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCoeffNeZeroOfFourierJacobiArcDatumStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataAtSplitIsotropicPointStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcDetect

theorem exists_place (p : ℕ) (hp : p.Prime) : ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits := by
  have hne : (Ideal.span {(p : (⊥ : Subring ℂ))}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨n, hn⟩ := Subring.mem_bot.1 v.2
    have h1 : ((p : ℤ) * n : ℤ) = 1 := by
      have := congrArg Subtype.val hv
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [← hn] at this
      exact_mod_cast this
    have := Int.isUnit_iff_natAbs_eq.1 (IsUnit.of_mul_eq_one _ h1)
    simp at this
    exact hp.one_lt.ne' this
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  exact ⟨W, hW ⟨p, Ideal.mem_span_singleton_self _, by simp⟩⟩

theorem iSup_sub_iInf_le {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) (A B : ℝ) (h1 : ∀ i, x i ≤ A) (h2 : ∀ i, -B ≤ x i) :
    (⨆ i, x i) - ⨅ i, x i ≤ A + B := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have := ciSup_le h1
  have := le_ciInf h2
  linarith

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_cm {r : ℕ} (X : Data E r) (g : (E →+* ℂ) → ℕ) :
    ∑ τ : X.Ψ, (g τ.1 + g (conjEmb τ.1)) = ∑ τ, g τ := by
  classical
  rw [← Finset.sum_add_sum_compl X.Ψ g]
  have hc : X.Ψᶜ = X.Ψ.image NumberField.ComplexEmbedding.conjugate := by
    ext σ
    simp only [Finset.mem_compl, Finset.mem_image]
    constructor
    · intro h
      exact ⟨NumberField.ComplexEmbedding.conjugate σ, (X.cmType _).2 (by simpa using h), by simp⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact (X.cmType τ).1 hτ
  rw [hc, Finset.sum_image (fun a _ b _ h => by simpa using congrArg NumberField.ComplexEmbedding.conjugate h),
    ← Finset.sum_add_distrib]
  exact Finset.sum_coe_sort X.Ψ (fun τ => g τ + g (ComplexEmbedding.conjugate τ))

theorem card_cm {r : ℕ} (X : Data E r) : Fintype.card X.Ψ = fdeg E := by
  have h := sum_cm X (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  unfold fdeg
  rw [← NumberField.Embeddings.card E ℂ]
  omega

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem laU_dominant {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (h : Dom a n)
    (k : U.Comp) : (U.X k).IsDominant (laU U a n k) := by
  intro τ
  refine ⟨fun i j hij hj => ?_, fun i j hi hij => ?_, fun i j hi hj => ?_⟩
  · have hij' : (i : ℕ) ≤ j := hij
    have := h.1 (Function.invFun (relab c σ) (conjEmb τ.1))
      (show (U.X k).p0 - 1 - (j : ℕ) ≤ (U.X k).p0 - 1 - (i : ℕ) by omega)
    unfold laU
    rw [if_neg (by omega), if_neg (by omega)]
    dsimp only at this
    omega
  · have hij' : (i : ℕ) ≤ j := hij
    have := h.1 (Function.invFun (relab c σ) τ.1)
      (show (i : ℕ) - (U.X k).p0 ≤ (j : ℕ) - (U.X k).p0 by omega)
    unfold laU
    rw [if_pos (by omega), if_pos (by omega)]
    dsimp only at this
    omega
  · unfold laU
    rw [if_neg (by omega), if_pos (by omega)]
    omega

theorem invFun_relab (τ : E →+* ℂ) : Function.invFun (relab c c.F.val.toRingHom) τ = τ := by
  have h : ∀ τ : E →+* ℂ, relab c c.F.val.toRingHom τ = τ := fun τ => RingHom.ext fun _ => rfl
  have h2 : relab c c.F.val.toRingHom (Function.invFun (relab c c.F.val.toRingHom) τ) = τ :=
    Function.invFun_eq ⟨τ, h τ⟩
  rwa [h] at h2

theorem sum_spread_le {r : ℕ} (hr : 0 < r) (U : Unf Xo c c.F.val.toRingHom r) (hU : IsUnf U)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) :
    ∑ τ, (U.X k).spread (laU U a n k) τ ≤ (absA Dw a : ℝ) + (fdeg E : ℝ) * n := by
  obtain ⟨hrk, hk, -⟩ := hU
  obtain ⟨hp, hΨ⟩ := hk k
  let B : (E →+* ℂ) → ℕ := fun τ => ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))
  have hB : ∀ τ i, i < Dw.mult τ → a (τ, i) ≤ B τ := fun τ i hi =>
    Finset.single_le_sum (f := fun i : Fin (Dw.mult τ) => a (τ, (i : ℕ))) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ⟨i, hi⟩)
  have h1 : ∀ τ : (U.X k).Ψ, (U.X k).spread (laU U a n k) τ ≤ ((B τ.1 + B (conjEmb τ.1) : ℕ) : ℝ) + n := by
    intro τ
    have m1 : Dw.mult τ.1 = Dw.p := if_pos ((hΨ _).1 τ.2)
    have m2 : Dw.mult (conjEmb τ.1) = Dw.q :=
      if_neg fun h => ((U.X k).cmType τ.1).1 τ.2 ((hΨ _).2 h)
    have hn : ((n / 2 : ℕ) : ℝ) + ((n / 2 : ℕ) : ℝ) ≤ n := by
      have : n / 2 + n / 2 ≤ n := by omega
      exact_mod_cast this
    have key : ∀ i, -((B (conjEmb τ.1) : ℤ) + ((n / 2 : ℕ) : ℤ)) ≤ laU U a n k τ i ∧
        laU U a n k τ i ≤ (B τ.1 : ℤ) + ((n / 2 : ℕ) : ℤ) := by
      intro i
      have hi := i.2
      unfold laU
      rw [invFun_relab, invFun_relab]
      split_ifs with h
      · have a1 := hB τ.1 ((i : ℕ) - (U.X k).p0) (by omega)
        constructor <;> omega
      · have a2 := hB (conjEmb τ.1) ((U.X k).p0 - 1 - (i : ℕ)) (by omega)
        constructor <;> omega
    refine (iSup_sub_iInf_le hr _ ((B τ.1 : ℝ) + ((n / 2 : ℕ) : ℝ))
      ((B (conjEmb τ.1) : ℝ) + ((n / 2 : ℕ) : ℝ)) (fun i => ?_) (fun i => ?_)).trans ?_
    · have h1 := (Int.cast_le (R := ℝ)).2 (key i).2
      rwa [Int.cast_add, Int.cast_natCast, Int.cast_natCast] at h1
    · exact_mod_cast (key i).1
    · rw [Nat.cast_add]; linarith
  refine (Finset.sum_le_sum fun τ _ => h1 τ).trans ?_
  rw [Finset.sum_add_distrib, ← Nat.cast_sum, sum_cm (U.X k) B, Finset.sum_const, Finset.card_univ, card_cm,
    nsmul_eq_mul]
  rfl

theorem exists_split {r : ℕ} (X₀ : Data E r) (X : DataX E r) (hX : X.toData = X₀) (la : Wt X₀.Ψ r)
    (P : Frame X₀.Ψ r → ℂ) (c₁ w : ℝ) (q g : ℕ) (hq : X₀.p0 = q) (hg : X.g = g)
    (hdom : X₀.IsDominant la) (hc : 0 < c₁) (hw : 1 ≤ w) (hspr : (∑ τ, X₀.spread la τ) ≤ w) (hr : (r : ℝ) ≤ w)
    (hχ : ∀ gm ∈ X₀.Γ, X₀.χ la gm = 1) (hP : P ∈ X₀.SS la) (hP' : P ∉ X₀.SSgt la c₁) :
    ∃ (ξ : Fin r → E) (ν : X₀.Ψ → ℝ) (x : Frame X₀.Ψ r) (lam : Fin (r - 2) → Fin r → E),
      X₀.IsIso ξ ∧ ∑ τ, ν τ ≤ c₁ ∧ x ∈ X₀.dom ∧ SplitData X ξ (LaQ E r q g X.NA X.NC c₁ w) (hX ▸ x) lam ∧
      (∀ m ∈ X₀.Λp ξ, ∃ e : E, e • ξ ∈ X₀.Λ ∧
        ((nQ E r g X.NA X.NC c₁ w : ℕ) : ℂ) • X₀.aproj x ξ (X₀.embV m) = X₀.embV (e • ξ)) ∧
      X₀.fj la ξ ν P x ≠ 0 := by
  subst hX hq hg
  obtain ⟨ξ, ν, hξ, hν, -, -, h⟩ := GlobalTheory.FJDetect.exists_fj_ne_zero_at_split_point' X la P c₁ w hdom hc hw hspr hr
    (fun gm hgm _ => hχ gm hgm) hP hP'
  obtain ⟨x, hx, lam, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h (nQ E r X.g X.NA X.NC c₁ w) (by
    unfold nQ
    push_cast
    exact (Nat.le_ceil _).trans (le_add_of_nonneg_right zero_le_one))
  refine ⟨ξ, ν, x, lam, hξ, hν, hx, ⟨h1, h2, h3, h4, h5, fun j τ => (h6 j τ).trans ?_⟩, h7, h8⟩
  refine pow_le_pow_left₀ ?_ (le_max_right _ _) 2
  have hw0 : 0 < w := by linarith
  unfold d6La ReciprocityTheory.MultiplicativeHeights.approxR d5mu d6rh dE
  positivity

end Weight

theorem detect_of_tie (hK : Known) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) {n' : ℕ} {La c₁ : ℝ}
    (s : CMIn d.a d.e d.th d.jj n' La c₁) (em : K₁ →+* ℂ) [Algebra (FractionRing ℂ) ℂ]
    [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (hσ : em.comp (algebraMap c.F K₁) = σ) {r : ℕ}
    (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r)
    (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Std d → GoodEmb c σ → IsUnf U → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n →
    (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → (U.X k).IsIso ξ' → x ∈ (U.X k).dom →
    Comparison₂ Uw d.a em s.ξ k ξ' x → ∀ F ∈ sec Xo c a' n, (∀ k', (U.X k').IsBddSec (laU U a' n k') (rdU U F k')) →
    (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 s.ν₀).re) (rdU U F k) x ≠ 0 →
    ∃ mo : ArcLt Dw →₀ ℕ, cfOf d.yF mo d.jj F ≠ 0 := by
  subst hσ
  exact GlobalTheory.T.exists_coeff_ne_zero_of_fourierJacobi_arcDatum hK E H Dw l Xo c K₁ d n' La c₁ s em r U Uw k ξ' x a' n

theorem exists_fam_cfOf_ne_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r) (k : U.Comp) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ w : ℝ), ModelsAt Xo c → IsUnf U → l.A = 1 → 3 ≤ r → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → Xx.g = l.M → 0 < c₁ → ((absA Dw a' : ℝ) + (fdeg E : ℝ) * n + r ≤ w) → ∀ F ∈ sec Xo c a' n, (∀ k', rdU U F k' ∈ (U.X k').SS (laU U a' n k')) → rdU U F k ∉ (U.X k).SSgt (laU U a' n k) c₁ → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra c.F K₁) (d : ArcDatum Xo c K₁), Fam (nQ E r l.M Xx.NA Xx.NC c₁ w) (LaQ E r Dw.q l.M Xx.NA Xx.NC c₁ w) c₁ d ∧ cfOf d.yF d.μ d.jj F ≠ 0 := by
  intro hK E _ _ _ H Dw l Xo c r U k Xx hX 𝔄 a' n c₁ w hM hU hA hr hP hD hχ h𝔄 hΛ hg hc hw F hF hS hS'
  letI : Algebra (FractionRing ℂ) ℂ := FractionRing.liftAlgebra ℂ ℂ
  haveI : IsScalarTower ℂ (FractionRing ℂ) ℂ := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  have hr3 : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have h0 : (0 : ℝ) ≤ (absA Dw a' : ℝ) + (fdeg E : ℝ) * n := by positivity
  obtain ⟨ξ, ν, x, lam, hξ, hν, hx, hsp, htor, hfj⟩ := exists_split (U.X k) Xx hX (laU U a' n k) (rdU U F k) c₁ w
    Dw.q l.M (hU.2.1 k).1 hg (laU_dominant U hD k) hc (by linarith)
    ((sum_spread_le (by omega) U hU a' n k).trans (by linarith)) (by linarith) (hχ k) (hS k) hS'
  obtain ⟨ν₀, hν1, hν2, hν3, hν4⟩ := GlobalTheory.FjFreq.freq_real_nonneg_integral E r (U.X k) _ _ (hS k).1 ξ hξ ν x hx hfj
  obtain rfl : ν = fun τ => (τ.1 ν₀).re := funext hν2
  rw [GlobalTheory.sum_re_cmType_eq_half_trace] at hν
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c _ r U hU
  have htv := GlobalTheory.TransvPrinc.transvIn_of_hasPrinc E H Dw l Xo c _ r U a' n hP hχ k
  obtain ⟨K₁, _, _, _, em, a, e, th, jj, s, hem, hs, htie⟩ := GlobalTheory.T.exists_cmArcData_at_splitIsotropicPoint hK E H Dw l Xo c r U Uw k ξ x Xx hX 𝔄
    _ _ c₁ lam (nQ E r l.M Xx.NA Xx.NC c₁ w) ν₀ hU hA hr hξ hx h𝔄 hΛ hsp le_rfl (Nat.succ_pos _) htor hν1 hν3
    (fun s h1 h2 => hν4 s h1 (htv ξ hξ s h1 h2)) hν
  obtain ⟨Wp, hWp⟩ := exists_place 2 Nat.prime_two
  obtain ⟨Y, hY, hYp⟩ := hM 2 Wp Nat.prime_two hWp
  obtain ⟨χ, W, -, hd⟩ := GlobalTheory.ArcDatumExists.exists_arcDatum hK.laws hK.laws2 E H Dw l Xo c K₁ Wp Y hY a
  obtain ⟨d, d1, d2, d3, d4, d5, -, d7, d8, d9⟩ := hd e
    (GlobalTheory.T.cmLetters_isLieBasis_along_arc hK E H Dw l Xo c K₁ a e th jj _ _ c₁ s _ _ Y χ W) th s.th_nz.ne_zero 0 jj
  obtain ⟨Wp', Y', a₁, χ', W', e', yF, th', i12, i3, mu, jj'⟩ := d
  dsimp only at d1 d2 d3 d4 d5 d7
  subst d1 d3 d7
  cases d2
  cases d4
  cases d5
  obtain ⟨mo, hmo⟩ := detect_of_tie hK ⟨Wp', Y', a₁, χ', W', e', yF, th', i12, i3, mu, jj'⟩ s em _ hem U Uw k ξ x a' n
    ⟨d8, d9, hYp⟩ rfl hU hP hD hχ hξ hx htie F hF (fun k' => (hS k').1) (by rw [hs]; exact hfj)
  exact ⟨K₁, _, _, _, ⟨Wp', Y', a₁, χ', W', e', yF, th', i12, i3, mo, jj'⟩, ⟨⟨d8, d9, hYp⟩, ⟨s⟩⟩, hmo⟩

end GlobalTheory.ArcDetect
