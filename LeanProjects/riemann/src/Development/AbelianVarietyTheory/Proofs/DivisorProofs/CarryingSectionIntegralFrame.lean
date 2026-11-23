import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasPhiExistsExtAndUnique

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovMult

open GlobalTheory.SlopeRec GlobalTheory.FlatLine GlobalTheory.RefSum

section Places

variable {K : Type} [Field K] [NumberField K]

theorem exists_prime_mem (la : HeightOneSpectrum (𝓞 K)) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ la.asIdeal := by
  have h0 : Ideal.absNorm la.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
  have key : ∀ n : ℕ, n ≠ 0 → (n : 𝓞 K) ∈ la.asIdeal → ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ la.asIdeal := by
    intro n
    induction n using Nat.recOnMul with
    | zero => exact fun h => absurd rfl h
    | one => exact fun _ h => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) la.isPrime.ne_top
    | prime p hp => exact fun _ h => ⟨p, hp, h⟩
    | mul a b ha hb =>
      intro h hm
      rw [Nat.cast_mul] at hm
      exact (la.isPrime.mem_or_mem hm).elim (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))
  exact key _ h0 (Ideal.absNorm_mem _)

theorem vLa_nat_nonneg (la : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0) : 0 ≤ vLa la (n : K) := by
  have := vAdd_int_nonneg la (a := (n : 𝓞 K)) (by simpa using hn)
  simpa [vLa, Formalism.BasicNotions.vAdd] using this

theorem vLa_pos {la : HeightOneSpectrum (𝓞 K)} {q : ℕ} (hq : q ≠ 0) (h : (q : 𝓞 K) ∈ la.asIdeal) :
    0 < vLa la (q : K) := by
  have h1 : la.valuation K (q : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) (q : 𝓞 K)).2 h
    simpa using this
  have h0 : la.valuation K (q : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hq)
  unfold vLa
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  omega

theorem exists_spread {S : Finset ℕ} {a : ℕ → ℝ} {s : ℝ} (h : PrimeSum S a s) (e : HeightOneSpectrum (𝓞 K) →₀ ℝ)
    (t : (K →+* ℂ) → ℝ) : ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ, cost e' t ≤ cost e t + s ∧
      ∀ (la : HeightOneSpectrum (𝓞 K)) (q : ℕ), e la + (vLa la (q : K) : ℝ) * a q ≤ e' la := by
  classical
  obtain ⟨hp, h0, hS, hs⟩ := h
  have one : ∀ (q : ℕ), q ≠ 0 → ∀ (b : ℝ) (e : HeightOneSpectrum (𝓞 K) →₀ ℝ), ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ,
      cost e' t = cost e t + b * Real.log q ∧ ∀ la, e' la = e la + (vLa la (q : K) : ℝ) * b := by
    intro q hq b e
    have hf := fin_mul (finite_vAdd (K := K) (a := q) (Nat.cast_ne_zero.2 hq)) fun _ => b
    refine ⟨e + Finsupp.ofSupportFinite _ hf, ?_, fun la => rfl⟩
    have h1 := sum_vAdd_nat (K := K) hq
    have h2 : ((Finsupp.ofSupportFinite _ hf).sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ)) /
        (Module.finrank ℚ K : ℝ) = b * Real.log q := by
      rw [← h1, mul_finsum, Finsupp.sum, Finset.sum_div, finsum_eq_sum_of_support_subset (s := (Finsupp.ofSupportFinite _ hf).support)]
      · refine Finset.sum_congr rfl fun la _ => ?_
        simp only [Finsupp.ofSupportFinite_coe, lw]; ring
      · intro la hla
        simp only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe]
        intro h
        apply hla
        simp only
        rw [← mul_assoc, mul_comm b, h, zero_mul]
    rw [cost, cost, Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_mul _ _ _), ← h2]
    ring
  have all : ∀ T : Finset ℕ, (∀ q ∈ T, q ≠ 0) → ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ,
      cost e' t = cost e t + ∑ q ∈ T, a q * Real.log q ∧ ∀ la, e' la = e la + ∑ q ∈ T, (vLa la (q : K) : ℝ) * a q := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨e, by simp, by simp⟩
    | insert q T hq ih =>
      intro hT
      obtain ⟨e₁, h1, h2⟩ := ih fun r hr => hT r (Finset.mem_insert_of_mem hr)
      obtain ⟨e₂, h3, h4⟩ := one q (hT q (Finset.mem_insert_self _ _)) (a q) e₁
      exact ⟨e₂, by rw [h3, h1, Finset.sum_insert hq]; ring, fun la => by rw [h4, h2, Finset.sum_insert hq]; ring⟩
  obtain ⟨e', h1, h2⟩ := all S fun q hq => (hp q hq).ne_zero
  have hn : ∀ la, ∀ q ∈ S, 0 ≤ (vLa la (q : K) : ℝ) * a q := fun la q hq =>
    mul_nonneg (by exact_mod_cast vLa_nat_nonneg la (hp q hq).ne_zero) (h0 q)
  refine ⟨e', by linarith, fun la q => ?_⟩
  rw [h2]
  by_cases hq : q ∈ S
  · exact add_le_add_right (Finset.single_le_sum (hn la) hq) _
  · rw [hS q hq, mul_zero]
    exact add_le_add_right (Finset.sum_nonneg (hn la)) _

end Places

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem depthOn_le (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {cst a : ℝ} {G : WTZ E} {q : ℕ} (hq : q ≠ 0)
    (ha : refExp_vp U cst G q ≤ (a : EReal)) {la : HeightOneSpectrum (𝓞 c.F)} (hla : (q : 𝓞 c.F) ∈ la.asIdeal)
    {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) {y : IntFr Xo c T io} (hy : y.IsAlg)
    {φ : ℝ} (hφ : HasPhi y φ) {Z : Comp Xo c} (hZ : letI := io.toAlgebra; LiesOn Z y.1) :
    depthOn U Z G (fun f => nval T.V e (evI y f)) ≤ (((vLa la (q : c.F) : ℝ) * a + cst * φ / e : ℝ) : EReal) := by
  letI := io.toAlgebra
  have hb := (refExp_vp_le_iff U).1 ha ⟨la, hla⟩ T io e ho y hy φ hφ
  rw [← EReal.coe_add] at hb
  have hm := vLa_pos hq hla
  have hv : vV T.V (q : T.Fr) = e * vLa la (q : c.F) := by rw [← ho.2, map_natCast]
  have hm' : (0 : ℝ) < vLa la (q : c.F) := by exact_mod_cast hm
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hn : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℝ) = e * vLa la (q : c.F) := by
    have : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℤ) = e * vLa la (q : c.F) := by
      rw [← hv, Int.toNat_of_nonneg (hv ▸ mul_nonneg (Nat.cast_nonneg _) hm.le)]
    exact_mod_cast this
  refine le_of_forall_gt_imp_ge_of_dense fun b hb' => ?_
  induction b using EReal.rec with
  | bot => exact absurd hb' not_lt_bot
  | top => exact le_top
  | coe b =>
    have hb1 := EReal.coe_lt_coe_iff.1 hb'
    have hlt : depthAt_vp U G q y < ((b / vLa la (q : c.F) : ℝ) : EReal) := by
      refine hb.trans_lt (EReal.coe_lt_coe_iff.2 ?_)
      rw [lt_div_iff₀ hm', hv]
      refine lt_of_eq_of_lt ?_ hb1
      push_cast; field_simp
    unfold depthAt_vp depth_vw at hlt
    obtain ⟨w, hw⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hwl, hw⟩ := iInf_lt_iff.1 hw
    have hne : evI y (w : Rul Xo c) ≠ 0 := fun h0 => by
      simp only [h0, nval_zero] at hw
      exact not_top_lt hw
    obtain ⟨g, hg, hgl⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hU Z _ w
    have hev : evI y (g : Rul Xo c) = evI y (w : Rul Xo c) := hg T.Fr y.1 hZ
    refine (iInf₂_le g (hgl hwl)).trans ?_
    simp only [nval_of_ne hne] at hw
    beta_reduce
    rw [hev, nval_of_ne hne, EReal.coe_le_coe_iff]
    have h2 := EReal.coe_lt_coe_iff.1 hw
    rw [hn, ← div_div, div_lt_div_iff_of_pos_right hm'] at h2
    exact h2.le

theorem exists_bound (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {a : ℕ → ℝ} {G : WTZ E}
    (ha : ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) G q ≤ (a q : EReal)) {Z : Comp Xo c} {θ : Rul Xo c} {w : Ix Dw → ℤ}
    (hθ : θ ∈ secZ Xo c w) {e e' : HeightOneSpectrum (𝓞 c.F) →₀ ℝ}
    (he : ∀ (la : HeightOneSpectrum (𝓞 c.F)) (q : ℕ), e la + (vLa la (q : c.F) : ℝ) * a q ≤ e' la)
    (hk : ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ →
      ∀ y : IntFr Xo c T io, y.IsAlg → (∃ (G' : WTZ E), ∃ f ∈ cuspOn U Z G', evI y f ≠ 0) → ∀ φ : ℝ, HasPhi y φ →
        ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ))
    {la : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ (recVals Xo c).1 la) {G' : WTZ E} {f : Rul Xo c}
    (hf : f ∈ cuspOn U Z G') (hf0 : v f ≠ ⊤) :
    ∃ B : ℝ, depthOn U Z G v ≤ (B : EReal) ∧ ((8 * B - 8 * e' la : ℝ) : EReal) ≤ v θ := by
  obtain ⟨⟨_, T, io, e₀, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  obtain ⟨T', i, e₁, y', φ, -, ho', hy', hφ, -, hv⟩ := exists_ext_hasPhi ho y hy
  obtain ⟨q, hq, hla⟩ := exists_prime_mem la
  have hf1 : evI y' f ≠ 0 := fun h => hf0 (by
    show nval T.V e₀ (evI y f) = ⊤
    rw [← (hv f hf.1.1.1).2, h, nval_zero])
  letI := (i.comp io).toAlgebra
  have hZ : LiesOn Z y'.1 := by
    by_contra h
    exact hf1 (hf.2 _ _ ((liesOff_iff Z y'.1).2 h))
  refine ⟨_, le_trans (le_of_eq ?_) (depthOn_le hU hq.ne_zero (ha q hq) hla ho' hy' hφ hZ), ?_⟩
  · exact iInf_congr fun g => iInf_congr fun _ => (hv g g.2.1.1.1).2.symm
  · refine le_trans (EReal.coe_le_coe_iff.2 ?_) ((hk la T' _ e₁ ho' y' hy' ⟨G', f, hf, hf1⟩ φ hφ).trans_eq (hv θ hθ.1).2)
    have := he la q
    have e2 : 8 / 2500 * φ / e₁ = 8 * (1 / 2500 * φ / e₁) := by ring
    linarith

theorem mult_of (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
    {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r} {u u' : AllWt.Weight Dw} {S : Finset ℕ} {a : ℕ → ℝ} {s cc : ℝ}
    (hS : PrimeSum S a s) (ha : ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) (wtOf Dw u 0) q ≤ (a q : EReal)) {Z : Comp Xo c}
    (hZ : ∃ (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) (t : (c.F →+* ℂ) → ℝ), Carries U Z u u' θ ∧
      (∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ →
        ∀ y : IntFr Xo c T io, y.IsAlg → (∃ (G' : WTZ E), ∃ f ∈ cuspOn U Z G', evI y f ≠ 0) → ∀ φ : ℝ, HasPhi y φ →
          ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧
      InfBd U x V dict Z (wtOf Dw u 0) (wtOf Dw ((8 : ℤ) • (u - u')) 0) 8 θ t ∧ cost e t ≤ cc) :
    Mult U x V dict Z u u' (cc + s) := by
  obtain ⟨θ, e, t, hC, hk, hI, hco⟩ := hZ
  obtain ⟨e', he', he⟩ := exists_spread hS e t
  have key := fun la v hv G' f hf hf0 => exists_bound hU ha hC.1 he hk (la := la) (v := v) hv (G' := G') (f := f) hf hf0
  refine ⟨fun la v hv G' f hf hf0 => ?_, θ, e', t, hC, fun la v hv ⟨w, _, hw⟩ => ?_, hI, by linarith⟩
  · obtain ⟨B, hB, -⟩ := key la v hv G' f hf hf0
    by_contra hn
    push Not at hn
    exact EReal.coe_ne_top B (top_le_iff.1 ((le_iInf₂ fun w hw => (hn w hw).ge).trans hB))
  · obtain ⟨B, hB, hB'⟩ := key la v hv _ w w.2 hw
    calc _ ≤ ((8 : ℕ) : EReal) * (B : EReal) := mul_le_mul_of_nonneg_left hB (by exact_mod_cast Nat.zero_le 8)
      _ = ((8 * B - 8 * e' la : ℝ) : EReal) + ((((8 : ℕ) : ℝ) * e' la : ℝ) : EReal) := by
        rw [← EReal.coe_add, ← EReal.coe_natCast, ← EReal.coe_mul]; congr 1; push_cast; ring
      _ ≤ _ := add_le_add_left hB' _

theorem budget_add {T a b C₁ C₂ u : ℝ} (h₁ : T * b ≤ C₁ * u) (h₂ : T * a ≤ C₂ * u) : T * (a + b) ≤ (C₁ + C₂) * u := by
  linarith

theorem multC_of_refW : GlobalTheory.RefSum.RefW → (Covers fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) → MultC := by
  intro hR hK
  refine Closed.imp (Closed.and hR hK) fun _ _ _ ⟨⟨C₁, h₁, hR⟩, C₂, h₂, hK⟩ => ⟨C₁ + C₂, add_nonneg h₁ h₂, ?_⟩
  refine (hR.and hK).imp fun _ h x hx hle ι p hp i hi Y hY u1 hu => ?_
  obtain ⟨hR, hK⟩ := h x hx hle ι p hp
  obtain ⟨S, a, s, hS, hs, ha⟩ := hR i hi Y hY u1 hu
  obtain ⟨cc, hc0, hc, hZ⟩ := hK i hi Y hY u1 hu
  have hs0 : 0 ≤ s := (Finset.sum_nonneg fun q _ => mul_nonneg (hS.2.1 q) (Real.log_natCast_nonneg q)).trans hS.2.2.2
  exact ⟨cc + s, add_nonneg hc0 hs0, budget_add hs hc, fun Z => mult_of hY.1.unf hS ha (hZ Z)⟩

end GlobalTheory.CovMult

end
