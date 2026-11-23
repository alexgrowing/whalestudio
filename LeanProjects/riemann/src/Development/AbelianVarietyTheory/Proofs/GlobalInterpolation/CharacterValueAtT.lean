import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalRingCardinality.SpanPowerMembership.Places
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSupportedIdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RingHomEqOfComapEqUnramifiedDegreeOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StarDetMulDetMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVDetLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormSpanInvol
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowPrincipal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocCharEqZpowMul
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SpanImageLeOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjPConjP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsComapPrime

open NumberField IsDedekindDomain WithZero

noncomputable section

namespace GlobalTheory.CharVal

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

section Val

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]

theorem conjP_conjP' [StarRing E] (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext x
  rw [mem_conjP, mem_conjP, cO_cO]

theorem valuation_conjP [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    (conjPrime₂ P).valuation E x = P.valuation E (star x) := by
  have : conjPrime₂ P = Formalism.BasicNotions.Examples₂.PlacesToy.conjW P := by
    ext r
    have := Formalism.BasicNotions.Examples₂.PlacesToy.mem_conjW_pow P r 1
    rw [pow_one, pow_one] at this
    rw [this, mem_conjP]
    rfl
  rw [this, Formalism.BasicNotions.Examples₂.PlacesToy.valuation_conjW]

theorem natCast_mem_conjP [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (p : ℕ) :
    ((p : ℕ) : 𝓞 E) ∈ (conjPrime₂ P).asIdeal ↔ ((p : ℕ) : 𝓞 E) ∈ P.asIdeal := by
  rw [mem_conjP, map_natCast]

theorem val_natCast_of_notMem_sq {Q : HeightOneSpectrum (𝓞 E)} {p : ℕ} (h1 : ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal)
    (h2 : ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2) : Q.valuation E (p : E) = exp (-1 : ℤ) := by
  have ha : ((p : ℕ) : 𝓞 E) ≠ 0 := by intro h; rw [h] at h2; exact h2 (zero_mem _)
  have e1 := (Q.intValuation_le_pow_iff_mem _ 1).2 (by simpa using h1)
  have e2 := mt (Q.intValuation_le_pow_iff_mem _ 2).1 h2
  have h0 : Q.intValuation ((p : ℕ) : 𝓞 E) ≠ 0 := Q.intValuation_ne_zero _ ha
  rw [← map_natCast (algebraMap (𝓞 E) E), HeightOneSpectrum.valuation_of_algebraMap]
  rw [← exp_log h0] at e1 e2 ⊢
  rw [exp_le_exp] at e1 e2
  congr 1
  push_cast at e1 e2
  omega

theorem exists_pull (φ : E →+* K) (w : HeightOneSpectrum (𝓞 K)) :
    ∃ Q : HeightOneSpectrum (𝓞 E), ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom φ r ∈ w.asIdeal :=
  _root_.GlobalTheory.ComapPrimeExistence.exists_comap_prime φ w

theorem val_emb_le_one {φ : E →+* K} {w : HeightOneSpectrum (𝓞 K)} {Q : HeightOneSpectrum (𝓞 E)}
    (h : ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom φ r ∈ w.asIdeal) {x : E} (hx : Q.valuation E x ≤ 1) :
    w.valuation K (φ x) ≤ 1 := by
  obtain ⟨r, s, hs, hrs⟩ := (intAt_iff x).2 hx
  refine (intAt_iff _).1 ⟨RingOfIntegers.mapRingHom φ r, RingOfIntegers.mapRingHom φ s, fun h' => hs ((h s).2 h'), ?_⟩
  have := congrArg φ hrs
  rw [map_mul] at this
  exact this

theorem val_emb_eq_one {φ : E →+* K} {w : HeightOneSpectrum (𝓞 K)} {Q : HeightOneSpectrum (𝓞 E)}
    (h : ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom φ r ∈ w.asIdeal) {x : E} (hx : Q.valuation E x = 1) :
    w.valuation K (φ x) = 1 := by
  have h1 := val_emb_le_one h hx.le
  have h2 := val_emb_le_one h (x := x⁻¹) (by rw [map_inv₀, hx, inv_one])
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h0 : w.valuation K (φ x) ≠ 0 := by simpa using hx0
  rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 h0)] at h2
  exact le_antisymm h1 h2

theorem val_emb_zpow {φ : E →+* K} {w : HeightOneSpectrum (𝓞 K)} {Q : HeightOneSpectrum (𝓞 E)}
    (h : ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom φ r ∈ w.asIdeal) {p : ℕ}
    (hp : Q.valuation E (p : E) = exp (-1 : ℤ)) {x : E} {M : ℤ} (hx : Q.valuation E x = exp (-M)) :
    w.valuation K (φ x) = w.valuation K (p : K) ^ M := by
  have hp0 : (p : E) ≠ 0 := by intro h0; rw [h0, map_zero] at hp; exact exp_ne_zero hp.symm
  have hpK : (p : K) ≠ 0 := by rw [← map_natCast φ]; simpa using hp0
  have h1 : Q.valuation E (x / (p : E) ^ M) = 1 := by
    rw [map_div₀, map_zpow₀, hp, hx, ← exp_zsmul]
    simp
  have h2 := val_emb_eq_one h h1
  rw [map_div₀, map_zpow₀, map_natCast, map_div₀, map_zpow₀, div_eq_one_iff_eq (zpow_ne_zero _ (by simpa using hpK))] at h2
  exact h2

theorem unit_of_pow {w : HeightOneSpectrum (𝓞 K)} {x : K} {M : ℕ} (hM : 0 < M) (h : w.valuation K (x ^ M) = 1) :
    w.valuation K x = 1 := by
  rw [map_pow] at h
  exact (pow_eq_one_iff_of_nonneg zero_le hM.ne').1 h

theorem unit_of_finOrder {w : HeightOneSpectrum (𝓞 K)} {ζ : Kˣ} (h : IsOfFinOrder ζ) : w.valuation K (ζ : K) = 1 := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine unit_of_pow hn ?_
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one, map_one]

theorem val_vp_of_pow {w : HeightOneSpectrum (𝓞 K)} {p : ℕ} (hp : p.Prime) (hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) {x : K} {M : ℕ}
    (hM : 0 < M) {n : ℤ} (h : w.valuation K x ^ M = w.valuation K (p : K) ^ n) : x ≠ 0 ∧ val_vp w p x = (n : ℚ) / M := by
  have hp0 : w.valuation K (p : K) ≠ 0 := by simpa using hp.ne_zero
  have hp1 : w.valuation K (p : K) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K)]
    exact (w.valuation_lt_one_iff_mem _).2 hw
  have hx0 : w.valuation K x ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM.ne'] at h
    exact zpow_ne_zero _ hp0 h.symm
  refine ⟨by simpa using hx0, ?_⟩
  have h1 := congrArg log h
  rw [log_pow, log_zpow] at h1
  have h2 : log (w.valuation K (p : K)) ≠ 0 := by
    intro h3
    rw [← exp_log hp0, h3] at hp1
    simp at hp1
  unfold val_vp ordE
  have h3 : ((log (w.valuation K (p : K)) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h2
  have h4 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have h5 : (M : ℚ) * ((log (w.valuation K x) : ℤ) : ℚ) = n * ((log (w.valuation K (p : K)) : ℤ) : ℚ) := by
    simp only [nsmul_eq_mul, smul_eq_mul] at h1
    exact_mod_cast h1
  push_cast
  field_simp
  linarith

theorem val_vp_mul {w : HeightOneSpectrum (𝓞 K)} {p : ℕ} {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    val_vp w p (x * y) = val_vp w p x + val_vp w p y := by
  unfold val_vp ordE
  rw [map_mul, log_mul (by simpa using hx) (by simpa using hy)]
  push_cast
  ring

theorem val_vp_zpow {w : HeightOneSpectrum (𝓞 K)} {p : ℕ} (x : K) (n : ℤ) :
    val_vp w p (x ^ n) = n * val_vp w p x := by
  unfold val_vp ordE
  rw [map_zpow₀, log_zpow]
  simp only [smul_eq_mul]
  push_cast
  ring

theorem val_vp_inv {w : HeightOneSpectrum (𝓞 K)} {p : ℕ} (x : K) : val_vp w p x⁻¹ = -val_vp w p x := by
  rw [← zpow_neg_one, val_vp_zpow]
  simp

theorem val_vp_unit {w : HeightOneSpectrum (𝓞 K)} {p : ℕ} {x : K} (h : w.valuation K x = 1) : val_vp w p x = 0 := by
  unfold val_vp ordE
  rw [h]
  simp

theorem exists_over (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 K) := by
    intro hu
    have h2 := hu.map (Algebra.norm ℤ)
    have e : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq] at h2
    exact hp.ne_one (by simpa using h2)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 K)}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩,
    hle (Ideal.mem_span_singleton_self _)⟩

theorem natCast_notMem_of_ne {a p : ℕ} (ha : a.Prime) (hp : p.Prime) (h : a ≠ p)
    (w : HeightOneSpectrum (𝓞 E)) (hw : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) : ((a : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  intro hT
  obtain ⟨x, y, e⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes ha hp).2 h)
  apply one_notMem w
  have e' : (x : 𝓞 E) * (a : 𝓞 E) + (y : 𝓞 E) * (p : 𝓞 E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) e
  rw [← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hT) (Ideal.mul_mem_left _ _ hw)

end Val

section See

variable {X : Fields}

structure SplitOver (p : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : Prop where
  prime : p.Prime
  norm : Ideal.absNorm P.asIdeal = p
  unram : ((p : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2
  ne : P ≠ conjPrime₂ P

theorem SplitOver.mem {p : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (h : SplitOver p P) : ((p : ℕ) : 𝓞 X.E) ∈ P.asIdeal :=
  h.norm ▸ Ideal.absNorm_mem _

theorem SplitOver.val {p : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (h : SplitOver p P) : P.valuation X.E (p : X.E) = exp (-1 : ℤ) :=
  val_natCast_of_notMem_sq h.mem h.unram

theorem SplitOver.valBar {p : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (h : SplitOver p P) :
    (conjPrime₂ P).valuation X.E (p : X.E) = exp (-1 : ℤ) := by
  rw [valuation_conjP, star_natCast, h.val]

theorem mem_pullW (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) (r : 𝓞 X.E) :
    r ∈ (pullW τ w).asIdeal ↔ RingOfIntegers.mapRingHom (X.emb τ) r ∈ w.asIdeal := Iff.rfl

theorem see_unique (hX : X.Ok) {p : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (h : SplitOver p P) {w : HeightOneSpectrum (𝓞 X.K)}
    {τ τ' : X.Tau} (h1 : SeesP w τ P ∨ SeesPbar w τ P) (h2 : SeesP w τ' P ∨ SeesPbar w τ' P) : τ = τ' := by
  have a : ∀ σ, SeesP w σ P → ∀ r : 𝓞 X.E, r ∈ P.asIdeal ↔ RingOfIntegers.mapRingHom (X.emb σ) r ∈ w.asIdeal := by
    intro σ hσ r
    rw [← mem_pullW, hσ]
  have b : ∀ σ, SeesPbar w σ P → ∀ r : 𝓞 X.E, r ∈ P.asIdeal ↔ RingOfIntegers.mapRingHom (X.embBar σ) r ∈ w.asIdeal := by
    intro σ hσ r
    have e : RingOfIntegers.mapRingHom (X.embBar σ) r = RingOfIntegers.mapRingHom (X.emb σ) (cO X.E r) := rfl
    rw [e, ← mem_pullW, hσ, mem_conjP, cO_cO]
  have u := fun φ ψ => GlobalTheory.ringHom_eq_of_comap_eq_unramified_degree_one X.E X.K φ ψ w P p h.prime h.norm h.unram
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact hX.emb_inj (u _ _ (a _ h1) (a _ h2))
  · exact absurd (u _ _ (a _ h1) (b _ h2)) (hX.emb_ne _ _)
  · exact absurd (u _ _ (a _ h2) (b _ h1)) (hX.emb_ne _ _)
  · have e := u _ _ (b _ h1) (b _ h2)
    apply hX.emb_inj
    ext x
    have := congrArg (fun φ : X.E →+* X.K => φ (star x)) e
    simpa [Fields.embBar, starRingEnd_apply] using this

theorem val_prod (hX : X.Ok) {p : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (h : SplitOver p P) (w : HeightOneSpectrum (𝓞 X.K))
    {y : X.E} {M : ℤ} (h1 : P.valuation X.E y = exp (-M)) (h2 : (conjPrime₂ P).valuation X.E y = exp M)
    (h3 : ∀ Q, Q ≠ P → Q ≠ conjPrime₂ P → Q.valuation X.E y = 1) (n : X.Tau → ℤ) (τ : X.Tau) :
    (SeesP w τ P → w.valuation X.K (∏ σ, X.emb σ y ^ n σ) = w.valuation X.K (p : X.K) ^ (M * n τ)) ∧
    (SeesPbar w τ P → w.valuation X.K (∏ σ, X.emb σ y ^ n σ) = w.valuation X.K (p : X.K) ^ (-M * n τ)) := by
  have key : SeesP w τ P ∨ SeesPbar w τ P →
      w.valuation X.K (∏ σ, X.emb σ y ^ n σ) = w.valuation X.K (X.emb τ y) ^ n τ := by
    intro hτ
    rw [map_prod, Finset.prod_eq_single τ, map_zpow₀]
    · intro σ _ hσ
      rw [map_zpow₀, val_emb_eq_one (mem_pullW σ w) (h3 _ (fun e => hσ (see_unique hX h (Or.inl e) hτ))
        (fun e => hσ (see_unique hX h (Or.inr e) hτ))), one_zpow]
    · simp
  constructor
  · intro hτ
    rw [key (Or.inl hτ), zpow_mul]
    congr 1
    refine val_emb_zpow (mem_pullW τ w) ?_ ?_ <;> rw [show pullW τ w = P from hτ]
    exacts [h.val, h1]
  · intro hτ
    rw [key (Or.inr hτ), zpow_mul]
    congr 1
    refine val_emb_zpow (mem_pullW τ w) ?_ ?_ <;> rw [show pullW τ w = conjPrime₂ P from hτ]
    exacts [h.valBar, by rw [neg_neg, h2]]

theorem val_prod_unit (w : HeightOneSpectrum (𝓞 X.K)) {y : X.E} (h : ∀ τ, (pullW τ w).valuation X.E y = 1) (n : X.Tau → ℤ) :
    w.valuation X.K (∏ σ, X.emb σ y ^ n σ) = 1 := by
  rw [map_prod]
  refine Finset.prod_eq_one fun σ _ => ?_
  rw [map_zpow₀, val_emb_eq_one (mem_pullW σ w) (h σ), one_zpow]

theorem natCast_mem_pullW (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) (p : ℕ) :
    ((p : ℕ) : 𝓞 X.E) ∈ (pullW τ w).asIdeal ↔ ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal := by
  rw [mem_pullW, map_natCast]

theorem finrank_E (hX : X.Ok) : Module.finrank ℚ X.E = 2 * X.f := by
  rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]

variable {Pr : Primes X}

theorem splitOver_vT (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vT u) :
    SplitOver (Pr.T u) P where
  prime := hPr.T_prime u
  norm := hPr.vT_norm u P hP
  unram := GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO (Pr.piT u) (Pr.T u) (cO_cO (E := X.E)) (hPr.T_prime u) (hPr.piT_norm u) (hPr.piT_cop u)
    (by rw [finrank_E hX, ← hPr.vT_card u]; rfl) (hPr.vT_norm u) P hP
  ne := fun e => conj_piT_notMem hPr u ⟨P, hP⟩ (by
    have := decoFin_mem_of_mem_divs hP
    rw [e, mem_conjP] at this
    exact this)

theorem val_q_vG (hX : X.Ok) (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) :
    P.valuation X.E (Formalism.L2.Col.qOf P : X.E) = exp (-1 : ℤ) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, P ∈ Pr.vG i := by
    rcases Finset.mem_union.1 hP with h2 | h2
    exacts [⟨0, h2⟩, ⟨1, h2⟩]
  have hcc : ∀ x, X.conjO (X.conjO x) = x := cO_cO (E := X.E)
  refine val_natCast_of_notMem_sq (Ideal.absNorm_mem _) ?_
  rw [show Formalism.L2.Col.qOf P = Pr.g i from hPr.vG_norm i P hi]
  exact GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO (X.conjO (Pr.piG i)) (Pr.g i) hcc (hPr.g_prime i) (by rw [hcc, mul_comm, hPr.piG_norm i])
    (by rw [hcc]; exact (hPr.piG_cop i).symm) (by rw [finrank_E hX, ← hPr.vG_card i]; rfl) (hPr.vG_norm i) P hi

end See

section Chi

variable {D : D7} {X : Fields} {s : Seam D X} {χ : TaylorLogMetric.IdE D → ℂ}

theorem desc_spec {K : Type} [Field K] (σ : K →+* ℂ) {z : ℂ} (h : ∃ k, σ k = z) : σ (desc σ z) = z := by
  unfold desc
  rw [dif_pos h]
  exact h.choose_spec

theorem desc_map {K : Type} [Field K] (σ : K →+* ℂ) (k : K) : desc σ (σ k) = k :=
  σ.injective (desc_spec σ ⟨k, rfl⟩)

theorem symm_conj (hs : s.Ok) (x : D.host.E) : s.iE.symm (D.host.conj x) = star (s.iE.symm x) := by
  apply s.iE.injective
  rw [hs.2, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem normOne_idTo (hs : s.Ok) {I J : Submodule (𝓞 X.E) X.E} (h1 : ∀ x, x ∈ J ↔ star x ∈ I) (h2 : I * J = 1) :
    TaylorLogMetric.N1 D (idTo s I) := by
  obtain ⟨t1, t2, t3, -⟩ := GlobalTheory.IdealTransport.transport D X s
  exact ⟨idTo s J, fun x => by rw [t1, t1, h1, symm_conj hs], by rw [← t2, h2, t3]⟩

theorem of_normOne (hs : s.Ok) {𝔞 : TaylorLogMetric.IdE D} (h : TaylorLogMetric.N1 D 𝔞) :
    ∃ I J : Submodule (𝓞 X.E) X.E, idTo s I = 𝔞 ∧ (∀ x, x ∈ J ↔ star x ∈ I) ∧ I * J = 1 := by
  obtain ⟨t1, t2, t3, -, t5, -⟩ := GlobalTheory.IdealTransport.transport D X s
  obtain ⟨𝔟, h1, h2⟩ := h
  obtain ⟨I, rfl⟩ := t5 𝔞
  obtain ⟨J, rfl⟩ := t5 𝔟
  refine ⟨I, J, rfl, fun x => ?_, ?_⟩
  · have := h1 (s.iE x)
    rwa [t1, t1, symm_conj hs, RingEquiv.symm_apply_apply] at this
  · rw [← t2, ← t3] at h2
    ext x
    have := t1 (I * J) (s.iE x)
    rw [h2, t1, RingEquiv.symm_apply_apply] at this
    exact this.symm

theorem chi_span (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) {y : X.E} (hy : star y * y = 1) :
    χ (idTo s (Submodule.span (𝓞 X.E) {y})) = s.σ₀ (∏ τ, X.emb τ y ^ (-1 : ℤ)) := by
  obtain ⟨-, -, -, t4, -⟩ := GlobalTheory.IdealTransport.transport D X s
  letI := D.host.cmStar
  have hst : star (s.iE y) = s.iE (star y) := by
    apply D.host.φ₀.injective
    rw [hs.2]
    change D.host.φ₀ (@NumberField.IsCMField.complexConj D.host.E _ _
      (D.host.isCMField_hostE) _ (s.iE y)) = _
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  have hu : s.iE y ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, mul_comm (s.iE y), and_self, hst, ← map_mul, hy, map_one]
  have := hχ.2 ⟨_, hu⟩
  rw [t4, this, map_prod, ← s.iT.prod_comp]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [zpow_neg_one, map_inv₀, hs.1]

theorem chi_core (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) (hK : ChiInK s χ) {I J : Submodule (𝓞 X.E) X.E}
    (h1 : ∀ x, x ∈ J ↔ star x ∈ I) (h2 : I * J = 1) :
    ∃ (h : ℕ) (y : X.E), 0 < h ∧ star y * y = 1 ∧ Submodule.span (𝓞 X.E) {y} = I ^ h ∧
      chiK s χ (idTo s I) ^ h = ∏ τ, X.emb τ y ^ (-1 : ℤ) := by
  obtain ⟨c1, h, y, hh, hy, hyI⟩ := GlobalTheory.NormOneIdeal.pow_eq_span_norm_one X.E I J h1 h2
  obtain ⟨-, t2, -⟩ := GlobalTheory.IdealTransport.transport D X s
  have hn : ∀ n : ℕ, TaylorLogMetric.N1 D (idTo s (I ^ n)) := fun n => normOne_idTo hs (c1 n) (by rw [← mul_pow, h2, one_pow])
  have hp : ∀ n : ℕ, χ (idTo s (I ^ n)) = χ (idTo s I) ^ n := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Submodule.one_eq_span, chi_span hs hχ (by simp)]
      simp
    | succ n ih => rw [pow_succ, pow_succ, t2, hχ.1 _ _ (hn n) (normOne_idTo hs h1 h2), ih]
  refine ⟨h, y, hh, hy, hyI, s.σ₀.injective ?_⟩
  rw [← chi_span hs hχ hy, hyI, hp, map_pow, IndefiniteRowSideFullHecke.CharacterValuation.chiK, desc_spec _ (hK _ (normOne_idTo hs h1 h2))]

theorem chiK_ne_zero (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) (hK : ChiInK s χ) {I J : Submodule (𝓞 X.E) X.E}
    (h1 : ∀ x, x ∈ J ↔ star x ∈ I) (h2 : I * J = 1) : chiK s χ (idTo s I) ≠ 0 := by
  obtain ⟨h, y, hh, hy, -, e⟩ := chi_core hs hχ hK h1 h2
  have hy0 : y ≠ 0 := right_ne_zero_of_mul_eq_one hy
  intro h0
  rw [h0, zero_pow hh.ne'] at e
  exact Finset.prod_ne_zero_iff.2 (fun τ _ => zpow_ne_zero _ (by simpa using hy0)) e.symm

theorem chiDet_eq {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) : chiDet s χ N = chiK s χ (idTo s (detLat N)) := by
  obtain ⟨-, -, -, -, -, t6⟩ := GlobalTheory.IdealTransport.transport D X s
  rw [chiDet, t6]

theorem chiDet_ne_zero (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) (hK : ChiInK s χ) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)}
    (hN : IsSdLat N) : chiDet s χ N ≠ 0 := by
  obtain ⟨J, h1, h2⟩ := GlobalTheory.DetSelfDual.detLat_mul_conj X.E n N hN
  rw [chiDet_eq]
  exact chiK_ne_zero hs hχ hK h1 h2

theorem maxV_detLat_std {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)}
    {P : HeightOneSpectrum (𝓞 E)} (h : localization₂ P.asIdeal N = stdAt E n P) : MaxV P (detLat N) 1 := by
  have := GlobalTheory.CharVal.DetFrame.maxV_detLat E n N P 1 (fun x => by rw [h]; rfl)
  simpa using this

theorem chiDet_unit (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) (hK : ChiInK s χ) {p : ℕ} {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)}
    (hN : IsSdLat N) (hS : StdOver p N) : UnitAt w (chiDet s χ N) := by
  obtain ⟨J, h1, h2⟩ := GlobalTheory.DetSelfDual.detLat_mul_conj X.E n N hN
  obtain ⟨h, y, hh, -, hyI, e⟩ := chi_core hs hχ hK h1 h2
  rw [chiDet_eq]
  refine unit_of_pow hh ?_
  rw [e]
  refine val_prod_unit w (fun τ => ?_) _
  have := (maxV_detLat_std (hS _ ((natCast_mem_pullW τ w p).2 hw))).pow h
  rw [← hyI, one_pow] at this
  exact (maxV_span_singleton y).unique this

theorem chiFK_eq (hs : s.Ok) (hK : ChiInK s χ) (a b : ℕ) {N : Submodule (𝓞 X.E) (Sp X.E a)}
    {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N') :
    chiFK s χ a b N N' = chiDet s χ N ^ (((b / 2 : ℕ) : ℤ)) * chiDet s χ N' ^ (-((a / 2 : ℕ) : ℤ)) := by
  obtain ⟨-, -, -, -, -, t6⟩ := GlobalTheory.IdealTransport.transport D X s
  obtain ⟨J, h1, h2⟩ := GlobalTheory.DetSelfDual.detLat_mul_conj X.E a N hN
  obtain ⟨J', h1', h2'⟩ := GlobalTheory.DetSelfDual.detLat_mul_conj X.E b N' hN'
  rw [← desc_map s.σ₀ (_ * _), map_mul, map_zpow₀, map_zpow₀, chiDet, chiDet, IndefiniteRowSideFullHecke.CharacterValuation.chiK, IndefiniteRowSideFullHecke.CharacterValuation.chiK,
    desc_spec _ (hK _ (t6 a N ▸ normOne_idTo hs h1 h2)), desc_spec _ (hK _ (t6 b N' ▸ normOne_idTo hs h1' h2'))]
  rfl

end Chi

section PartsChi

variable {D : D7} {Z : Dat} {s : Seam D Z.X} {χ : TaylorLogMetric.IdE D → ℂ}

theorem partBChi (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) (hK : ChiInK s χ) (u : Z.Pr.Word) {w : HeightOneSpectrum (𝓞 Z.X.K)}
    (hw : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal) : PartBChi Z s χ u w := by
  refine ⟨fun 𝔞 h𝔞 hloc => ?_, fun n N hN hS => chiDet_unit hs hχ hK hw hN hS, fun a b N N' _ _ hN hN' hS hS' => ?_⟩
  · obtain ⟨I, J, rfl, h1, h2⟩ := of_normOne hs h𝔞
    obtain ⟨h, y, hh, -, hyI, e⟩ := chi_core hs hχ hK h1 h2
    obtain ⟨-, t2, t3, t4, -⟩ := GlobalTheory.IdealTransport.transport D Z.X s
    have hp : ∀ n : ℕ, idTo s (I ^ n) = idTo s I ^ n := by
      intro n
      induction n with
      | zero => simpa using t3
      | succ n ih => rw [pow_succ, pow_succ, t2, ih]
    refine unit_of_pow hh ?_
    rw [e]
    refine val_prod_unit w (fun τ => ?_) _
    obtain ⟨Q, hQ⟩ := exists_pull (s.iE.symm : D.host.E →+* Z.X.E) (pullW τ w)
    have hT : ((Z.Pr.T u : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
      rw [hQ, map_natCast, natCast_mem_pullW]
      exact hw
    have h3 := (maxV_of_localization_eq (hloc Q hT)).pow h
    rw [← hp, ← hyI, t4, one_pow] at h3
    have h4 := val_emb_eq_one hQ ((maxV_span_singleton _).unique h3)
    simpa using h4
  · have h1 : w.valuation _ _ = 1 := chiDet_unit hs hχ hK hw hN hS
    have h2 : w.valuation _ _ = 1 := chiDet_unit hs hχ hK hw hN' hS'
    rw [UnitAt, chiFK_eq hs hK a b hN hN', map_mul, map_zpow₀, map_zpow₀, h1, h2]
    simp

theorem partA (hZ : Z.Ok) (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) (hK : ChiInK s χ) (u : Z.Pr.Word) : PartA Z s χ u := by
  intro P hP
  have hS := splitOver_vT hZ.fields hZ.primes u hP
  obtain ⟨⟨J, h1, h2⟩, m1, m2, m3, -⟩ := GlobalTheory.CharVal.Vp.vp_main Z.X.E P hS.ne
  obtain ⟨h, y, hh, hy, hyI, e⟩ := chi_core hs hχ hK h1 h2
  have v1 : P.valuation _ y = exp (-(h : ℤ)) := by
    rw [(maxV_span_singleton y).unique (hyI ▸ m1.pow h), ← exp_nsmul]; simp
  have v2 : (conjPrime₂ P).valuation _ y = exp (h : ℤ) := by
    rw [(maxV_span_singleton y).unique (hyI ▸ m2.pow h), ← exp_nsmul]; simp
  have v3 : ∀ Q, Q ≠ P → Q ≠ conjPrime₂ P → Q.valuation _ y = 1 := fun Q a b => by
    rw [(maxV_span_singleton y).unique (hyI ▸ (m3 Q a b).pow h), one_pow]
  have hh' : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  refine ⟨fun σ => ?_, fun w hw => ?_, fun w hw τ => ⟨fun hτ => ?_, fun hτ => ?_⟩⟩
  · have h3 : ‖σ (chiVp s χ P)‖ ^ h = 1 := by
      rw [← norm_pow, ← map_pow, chiVp, e, map_prod, norm_prod]
      refine Finset.prod_eq_one fun τ _ => ?_
      have h4 := congrArg (σ.comp (Z.X.emb τ)) hy
      rw [map_mul, hZ.fields.conjE, map_one] at h4
      have h5 := congrArg norm h4
      rw [norm_mul, Complex.norm_conj, norm_one, ← sq] at h5
      have h6 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h5
      rw [map_zpow₀, norm_zpow]
      rw [RingHom.comp_apply] at h6
      rw [h6, one_zpow]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hh.ne').1 h3
  · refine unit_of_pow hh ?_
    rw [chiVp, e]
    refine val_prod_unit w (fun τ => v3 _ (fun e' => hw ?_) (fun e' => hw ?_)) _
    · rw [← natCast_mem_pullW τ, e']; exact hS.mem
    · rw [← natCast_mem_pullW τ, e', natCast_mem_conjP]; exact hS.mem
  · have h3 := (val_prod hZ.fields hS w v1 v2 v3 (fun _ => -1) τ).1 hτ
    rw [← e, map_pow] at h3
    rw [chiVp, (val_vp_of_pow hS.prime hw hh h3).2]
    push_cast
    field_simp
  · have h3 := (val_prod hZ.fields hS w v1 v2 v3 (fun _ => -1) τ).2 hτ
    rw [← e, map_pow] at h3
    rw [chiVp, (val_vp_of_pow hS.prime hw hh h3).2]
    push_cast
    field_simp

end PartsChi

section Xi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem finOrder_apply {ξ : Chr F E L} (h : IsOfFinOrder ξ) (y : (AfE F E)ˣ) : IsOfFinOrder (ξ y) := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rw [← MonoidHom.pow_apply, h, MonoidHom.one_apply]⟩

theorem finOrder_unifVal {ξ : Chr F E L} (h : IsOfFinOrder ξ) (P : HeightOneSpectrum (𝓞 E)) : IsOfFinOrder (unifVal ξ P) := by
  unfold unifVal
  split_ifs with H
  · obtain ⟨b, hb1, hb2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
    obtain ⟨y, y₀, a1, a2, a3, a4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P (P.under (𝓞 F)) b rfl
    rw [← H.choose_spec (P.under (𝓞 F)) rfl y y₀ b a1 hb1 hb2 a2 a3 a4]
    exact finOrder_apply h y
  · exact IsOfFinOrder.one

theorem finOrder_qVal {ξ : Chr F E L} (h : IsOfFinOrder ξ) (P : HeightOneSpectrum (𝓞 E)) : IsOfFinOrder (qVal ξ P) := by
  unfold qVal qValC
  split_ifs with H
  · obtain ⟨y, y₀, a1, a2, a3, a4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P (P.under (𝓞 F)) ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) rfl
    rw [← H.choose_spec (P.under (𝓞 F)) rfl y y₀ a1 a2 a3 a4]
    exact finOrder_apply h y
  · exact IsOfFinOrder.one

theorem finOrder_tup {S : Set ℕ} (mu : Tup F E L S) : IsOfFinOrder (mu : Chr F E L) :=
  mu.2.1.1.1.2

theorem val_unif (P : HeightOneSpectrum (𝓞 E)) : P.valuation E ((Formalism.L2.Host.unif P : Eˣ) : E) = exp (-1 : ℤ) := by
  rw [← Formalism.L2.Host.unif_spec P]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm

end Xi

theorem productRule {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) : χ.ProductRule :=
  GlobalTheory.Mem.Chr.CharModel.productRule (F := L) ⟨χ.1, χ.2⟩

section Frames

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem ordDet_eq {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} {Q : HeightOneSpectrum (𝓞 E)} {m : ℤ}
    (hf : ∃ f : Sp E n ≃ₗ[E] Sp E n, ∀ x, f x ∈ localization₂ Q.asIdeal N ↔ x ∈ stdAt E n Q) (h : MaxV Q (detLat N) (exp (-m))) :
    ordDet Q N = m := by
  have := (GlobalTheory.CharVal.DetFrame.maxV_detLat E n N Q (frameAt Q N) (Classical.epsilon_spec hf)).unique h
  rw [ordDet, ordE, this, log_exp, neg_neg]

theorem ordDet_std {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} {Q : HeightOneSpectrum (𝓞 E)} (h : localization₂ Q.asIdeal N = stdAt E n Q) :
    ordDet Q N = 0 :=
  ordDet_eq ⟨1, fun x => by rw [h]; rfl⟩ (by simpa using maxV_detLat_std h)

theorem ordDet_vpLat {P Q : HeightOneSpectrum (𝓞 E)} (hP : P ≠ conjPrime₂ P) {m : ℤ} (h : MaxV Q (vpIdeal P) (exp (-m))) :
    ordDet Q (vpLat P) = m := by
  obtain ⟨-, -, -, -, e⟩ := GlobalTheory.CharVal.Vp.vp_main E P hP
  refine ordDet_eq ?_ (e ▸ h)
  obtain ⟨a, -, ha⟩ := h.2
  have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact exp_ne_zero ha.symm
  refine ⟨LinearEquiv.smulOfNeZero E (Sp E 1) a ha0, fun x => ?_⟩
  have e1 : LinearEquiv.smulOfNeZero E (Sp E 1) a ha0 x ∈ localization₂ Q.asIdeal (vpLat P) ↔ a * x 0 ∈ localization₂ Q.asIdeal (vpIdeal P) :=
    Iff.rfl
  rw [e1, h.mem_locP exp_ne_zero, stdAt, mem_localization_standardLattice, Fin.forall_fin_one, intAt_iff, map_mul, ha,
    mul_le_iff_le_one_right (zero_lt_iff.2 exp_ne_zero)]

end Frames

section Mu

variable {X : Fields} {Pr : Primes X} {m : ℕ} {Ch : Chars X Pr m} {σ₀ : X.K →+* ℂ} {e : X.Tau → ℚ} {j : Fin m}
  {μ : Formalism.L2.Host.HChar X.E}

theorem mu_core (hX : X.Ok) (hPr : Pr.Ok) (hμ : IsMu0 Ch σ₀ e j μ) (P : HeightOneSpectrum (𝓞 X.E)) (k : X.Eˣ) {c : X.K}
    (hc : σ₀ c = ((μ.locK P k : ℂˣ) : ℂ)) :
    ∃ (M : ℕ) (z : X.E) (n : X.Tau → ℤ), 0 < M ∧ (∀ τ, (n τ : ℚ) = 2 * e τ) ∧ P.valuation X.E z = P.valuation X.E (k : X.E) ^ M ∧
      (∀ Q : HeightOneSpectrum (𝓞 X.E), Q ≠ P → Q.valuation X.E z = 1) ∧ c ^ (2 * M) = ∏ τ, X.emb τ (z / star z) ^ n τ := by
  classical
  have hg : ∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := fun i => by exact_mod_cast (hPr.g_prime i).ne_zero
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf X.E μ (divs ((Pr.g 0 : ℕ) : 𝓞 X.E) ∪ divs ((Pr.g 1 : ℕ) : 𝓞 X.E))
    (productRule μ) (fun v hv => hμ.unr v fun i hi => hv (by
      rw [Finset.mem_union, mem_divs (hg 0), mem_divs (hg 1)]
      fin_cases i
      exacts [Or.inl hi, Or.inr hi])) hμ.tame P k
  obtain ⟨n, hn, hinf⟩ := hμ.inf
  refine ⟨M, z, fun τ => -n τ, hM, fun τ => by push_cast; rw [hn]; ring, h1, h2, σ₀.injective ?_⟩
  have h4 : ((μ.locK P k : ℂˣ) : ℂ) ^ M = (((μ.inf z : ℂˣ) : ℂ))⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, eq_inv_of_mul_eq_one_left h3, Units.val_inv_eq_inv_val]
  rw [map_pow, hc, mul_comm 2 M, pow_mul, h4, hinf z, ← Finset.prod_inv_distrib, ← Finset.prod_pow, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀, ← zpow_neg, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  congr 1
  change _ = X.embC σ₀ τ (z / star (z : X.E))
  have h0 : X.embC σ₀ τ (z : X.E) ≠ 0 := by simp
  rw [map_div₀, hX.conjE, div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem mu_unit (hX : X.Ok) (hPr : Pr.Ok) (hμ : IsMu0 Ch σ₀ e j μ) {P : HeightOneSpectrum (𝓞 X.E)} (k : X.Eˣ) {c : X.K}
    (hc : σ₀ c = ((μ.locK P k : ℂˣ) : ℂ)) {p : ℕ} (hP : ((p : ℕ) : 𝓞 X.E) ∉ P.asIdeal) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) : w.valuation X.K c = 1 := by
  obtain ⟨M, z, n, hM, -, -, h2, h3⟩ := mu_core hX hPr hμ P k hc
  refine unit_of_pow (M := 2 * M) (by omega) ?_
  rw [h3]
  refine val_prod_unit w (fun τ => ?_) n
  have h4 := (natCast_mem_pullW τ w p).2 hw
  rw [map_div₀, ← valuation_conjP, h2 _ (fun e' => hP (e' ▸ h4)), h2 _ (fun e' => hP (e' ▸ (natCast_mem_conjP _ p).2 h4)), div_one]

theorem mu_val (hX : X.Ok) (hPr : Pr.Ok) (hμ : IsMu0 Ch σ₀ e j μ) {p : ℕ} {P P' : HeightOneSpectrum (𝓞 X.E)} (h : SplitOver p P)
    {ε : ℤ} (hε : (P' = P ∧ ε = 1) ∨ (P' = conjPrime₂ P ∧ ε = -1)) {c : X.K} (hc : σ₀ c = ((μ.val P' : ℂˣ) : ℂ))
    {w : HeightOneSpectrum (𝓞 X.K)} (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) (τ : X.Tau) :
    (SeesP w τ P → val_vp w p c = ε * e τ) ∧ (SeesPbar w τ P → val_vp w p c = -(ε * e τ)) := by
  obtain ⟨M, z, n, hM, hn, h1, h2, h3⟩ := mu_core hX hPr hμ P' (Formalism.L2.Host.unif P') hc
  rw [val_unif, ← exp_nsmul] at h1
  have hne := h.ne
  have v1 : P.valuation X.E (z / star z) = exp (-(ε * M)) := by
    rw [map_div₀, ← valuation_conjP]
    rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [h1, h2 _ hne.symm]; simp
    · rw [h1, h2 _ hne]; simp
  have v2 : (conjPrime₂ P).valuation X.E (z / star z) = exp (ε * M) := by
    rw [map_div₀, ← valuation_conjP, conjP_conjP']
    rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [h1, h2 _ hne.symm]; simp
    · rw [h1, h2 _ hne]; simp
  have v3 : ∀ Q, Q ≠ P → Q ≠ conjPrime₂ P → Q.valuation X.E (z / star z) = 1 := by
    intro Q a b
    have a' : conjPrime₂ Q ≠ conjPrime₂ P := fun e' => a (by rw [← conjP_conjP' Q, e', conjP_conjP'])
    have b' : conjPrime₂ Q ≠ P := fun e' => b (by rw [← e', conjP_conjP'])
    rw [map_div₀, ← valuation_conjP]
    rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [h2 _ a, h2 _ b', div_one]
    · rw [h2 _ b, h2 _ a', div_one]
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have key := val_prod hX h w v1 v2 v3 n τ
  rw [← h3, map_pow] at key
  constructor
  · intro hτ
    rw [(val_vp_of_pow h.prime hw (by omega) (key.1 hτ)).2]
    push_cast
    rw [hn]
    field_simp
  · intro hτ
    rw [(val_vp_of_pow h.prime hw (by omega) (key.2 hτ)).2]
    push_cast
    rw [hn]
    field_simp

end Mu

section PartsMu

variable {D : D7} {Z : Dat} {s : Seam D Z.X} {χ : TaylorLogMetric.IdE D → ℂ}
  {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ}
  {mu : Tup Z.X.F Z.X.E Z.X.K S} {cst : LocCst Z.X (rowSG Z.Pr sel mu)}
  {m0 : Fin Z.R.m → Formalism.L2.Host.HChar Z.X.E} {eta : Formalism.L2.Host.HChar Z.X.E}

theorem natCast_mem_sel (hsel : IsSel Z.X sel) (v : HeightOneSpectrum (𝓞 Z.X.F)) (p : ℕ) :
    ((p : ℕ) : 𝓞 Z.X.E) ∈ (sel v).asIdeal ↔ ((p : ℕ) : 𝓞 Z.X.F) ∈ v.asIdeal := by
  rw [← hsel v, Ideal.under_def, Ideal.mem_comap, map_natCast]

theorem under_conjP (hX : Z.X.Ok) (Q : HeightOneSpectrum (𝓞 Z.X.E)) :
    (conjPrime₂ Q).asIdeal.under (𝓞 Z.X.F) = Q.asIdeal.under (𝓞 Z.X.F) := by
  ext r
  have e : cO Z.X.E (algebraMap (𝓞 Z.X.F) (𝓞 Z.X.E) r) = algebraMap (𝓞 Z.X.F) (𝓞 Z.X.E) r :=
    RingOfIntegers.ext (hX.star_F (r : Z.X.F))
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, e]

theorem eq_or_eq_conjP (hX : Z.X.Ok) {P Q : HeightOneSpectrum (𝓞 Z.X.E)} (hP : P ≠ conjPrime₂ P)
    (h : Q.asIdeal.under (𝓞 Z.X.F) = P.asIdeal.under (𝓞 Z.X.F)) : Q = P ∨ Q = conjPrime₂ P := by
  let c : Z.X.E →ₐ[Z.X.F] Z.X.E := { starRingEnd Z.X.E with commutes' := hX.star_F }
  let M : IntermediateField Z.X.F Z.X.E :=
    (AlgHom.equalizer c (AlgHom.id _ _)).toIntermediateField fun x hx => by
      have hx' : star x = x := hx
      change star x⁻¹ = x⁻¹
      rw [star_inv₀, hx']
  have hM : M = ⊥ := by
    have := IntermediateField.isSimpleOrder_of_finrank_prime Z.X.F Z.X.E (by rw [hX.rankE]; exact Nat.prime_two)
    refine (eq_bot_or_eq_top M).resolve_right fun e => hP ?_
    ext r
    have h1 : (r : Z.X.E) ∈ M := e ▸ IntermediateField.mem_top
    have h2 : cO Z.X.E r = r := RingOfIntegers.ext h1
    rw [mem_conjP, h2]
  by_contra H
  push Not at H
  have h1 : ¬ ((P.asIdeal : Set (𝓞 Z.X.E)) ⊆ Q.asIdeal ∪ (conjPrime₂ Q).asIdeal) := by
    rw [Ideal.subset_union]
    rintro (h1 | h1)
    · exact H.1 (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h1)).symm
    · have : P = conjPrime₂ Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le (conjPrime₂ Q).isPrime.ne_top h1)
      exact H.2 (by rw [this, conjP_conjP'])
  obtain ⟨a, ha, hna⟩ := Set.not_subset.1 h1
  have h2 : ((a * cO Z.X.E a : 𝓞 Z.X.E) : Z.X.E) ∈ M := by
    change star ((a : Z.X.E) * star (a : Z.X.E)) = (a : Z.X.E) * star (a : Z.X.E)
    rw [star_mul, star_star]
  rw [hM, IntermediateField.mem_bot] at h2
  obtain ⟨x, hx⟩ := h2
  have h3 : IsIntegral ℤ x := by
    rw [← isIntegral_algebraMap_iff (algebraMap Z.X.F Z.X.E).injective, hx]
    exact RingOfIntegers.isIntegral_coe _
  obtain ⟨r, h4⟩ : ∃ r : 𝓞 Z.X.F, algebraMap (𝓞 Z.X.F) (𝓞 Z.X.E) r = a * cO Z.X.E a := ⟨⟨x, h3⟩, RingOfIntegers.ext hx⟩
  have h5 : r ∈ P.asIdeal.under (𝓞 Z.X.F) := by
    rw [Ideal.under_def, Ideal.mem_comap, h4]
    exact Ideal.mul_mem_right _ _ ha
  rw [← h, Ideal.under_def, Ideal.mem_comap, h4] at h5
  rcases Q.isPrime.mem_or_mem h5 with h6 | h6
  · exact hna (Or.inl h6)
  · exact hna (Or.inr h6)

theorem mem_rowSG_cases {P : HeightOneSpectrum (𝓞 Z.X.E)} (hP : P ∈ rowSG Z.Pr sel mu) :
    P ∈ Z.Pr.vGs ∨ ∃ v ∈ Qprime (mu : Chr Z.X.F Z.X.E Z.X.K), sel v = P := by
  classical
  rcases Finset.mem_union.1 hP with h | h
  · exact Or.inl h
  · unfold QE at h
    split_ifs at h with h2
    · obtain ⟨v, hv, e⟩ := Finset.mem_image.1 h
      exact Or.inr ⟨v, by simpa using hv, e⟩
    · simp at h

theorem T_notMem_rowSG (hZ : Z.Ok) (hsel : IsSel Z.X sel) {u : Z.Pr.Word}
    (hT : UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.T u)) {P : HeightOneSpectrum (𝓞 Z.X.E)} (hP : P ∈ rowSG Z.Pr sel mu) :
    ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∉ P.asIdeal := by
  rcases mem_rowSG_cases hP with h | ⟨v, hv, rfl⟩
  · exact T_notMem_vGs hZ.primes u ⟨P, h⟩
  · rw [natCast_mem_sel hsel]
    exact fun h => hT v h hv

theorem g_notMem_sel (hZ : Z.Ok) (hsel : IsSel Z.X sel) {v : HeightOneSpectrum (𝓞 Z.X.F)}
    (hv : ¬ ∃ P ∈ rowSG Z.Pr sel mu, P.asIdeal.under (𝓞 Z.X.F) = v.asIdeal) (k : Fin 2) :
    ((Z.Pr.g k : ℕ) : 𝓞 Z.X.E) ∉ (sel v).asIdeal := by
  classical
  intro h
  have hsub : ∀ Q, Q ∈ Z.Pr.vG k → Q ∈ rowSG Z.Pr sel mu := fun Q hQ => Finset.mem_union_left _ (by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hQ, Or.inr hQ])
  have h0 : Z.X.conjO (Z.Pr.piG k) ≠ 0 := by
    refine right_ne_zero_of_mul (a := Z.Pr.piG k) ?_
    rw [hZ.primes.piG_norm k]
    exact_mod_cast (hZ.primes.g_prime k).ne_zero
  rw [← hZ.primes.piG_norm k] at h
  rcases (sel v).isPrime.mem_or_mem h with h | h
  · refine hv ⟨conjPrime₂ (sel v), hsub _ ((mem_divs h0 _).2 ?_), by rw [under_conjP hZ.fields, hsel v]⟩
    rw [mem_conjP]
    exact (cO_cO (Z.Pr.piG k)).symm ▸ h
  · exact hv ⟨sel v, hsub _ ((mem_divs h0 _).2 h), hsel v⟩

theorem muVal_unit (hZ : Z.Ok) (ht : Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta) (i : Fin Z.R.m)
    {P : HeightOneSpectrum (𝓞 Z.X.E)} (hg : ∀ k, ((Z.Pr.g k : ℕ) : 𝓞 Z.X.E) ∉ P.asIdeal) {p : ℕ}
    (hP : ((p : ℕ) : 𝓞 Z.X.E) ∉ P.asIdeal) {w : HeightOneSpectrum (𝓞 Z.X.K)} (hw : ((p : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal) :
    w.valuation Z.X.K (Z.Ch.muVal i P : Z.X.K) = 1 :=
  mu_unit hZ.fields hZ.primes (ht.mu0 i) _ (ht.muVal i P hg) hP hw

theorem mUof_val (i : Fin Z.R.m) (P : HeightOneSpectrum (𝓞 Z.X.E)) :
    ((mUof Z.Ch mu i.1 P : Z.X.Kˣ) : Z.X.K) =
      (Z.Ch.muVal i P : Z.X.K)⁻¹ * ((unifVal (mu : Chr Z.X.F Z.X.E Z.X.K) P : Z.X.Kˣ) : Z.X.K)⁻¹ := by
  simp [mUof, i.2]

theorem muOff_unit (hZ : Z.Ok) (ht : Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta) (hsel : IsSel Z.X sel) (i : Fin Z.R.m)
    {p : ℕ} {w : HeightOneSpectrum (𝓞 Z.X.K)} (hw : ((p : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal) {n : ℕ}
    {N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)} (hS : StdOver p N) :
    w.valuation Z.X.K (muOff sel (rowSG Z.Pr sel mu) (mUof Z.Ch mu i.1) N) = 1 := by
  unfold muOff
  refine finprod_induction (fun x => w.valuation Z.X.K x = 1) (map_one _) (fun x y hx hy => by rw [map_mul, hx, hy, one_mul]) fun v => ?_
  split_ifs with hv
  · exact map_one _
  · by_cases hp : ((p : ℕ) : 𝓞 Z.X.E) ∈ (sel v).asIdeal
    · rw [ordDet_std (hS _ hp), zpow_zero, Units.val_one, map_one]
    · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, mUof_val, map_mul, map_inv₀, map_inv₀,
        muVal_unit hZ ht i (g_notMem_sel hZ hsel hv) hp hw, unit_of_finOrder (finOrder_unifVal (finOrder_tup mu) _)]
      simp

theorem muOff_ne_zero (mU : HeightOneSpectrum (𝓞 Z.X.E) → Z.X.Kˣ) {n : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) :
    muOff sel (rowSG Z.Pr sel mu) mU N ≠ 0 := by
  unfold muOff
  refine finprod_induction (fun x => x ≠ 0) one_ne_zero (fun x y hx hy => mul_ne_zero hx hy) fun v => ?_
  split_ifs
  · exact one_ne_zero
  · exact Units.ne_zero _

theorem muAtT_unit (hZ : Z.Ok) (ht : Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta) (hsel : IsSel Z.X sel) {u : Z.Pr.Word}
    (hT : UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.T u)) (hG : ∀ k, UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.g k))
    (hc : MuqTieG (Pr := Z.Pr) (R := Z.R) sel mu cst Z.sig0 m0) (i : Fin Z.R.m)
    {w : HeightOneSpectrum (𝓞 Z.X.K)} (hw : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal) (P : rowSG Z.Pr sel mu) {a : Z.X.E} (ha : a ≠ 0) :
    w.valuation Z.X.K (muAtT Z.Ch sel mu cst i.1 P a) = 1 := by
  have hTP := T_notMem_rowSG hZ hsel hT P.2
  have hq := unit_of_finOrder (w := w) (finOrder_qVal (finOrder_tup mu) P.1)
  have key : ∀ (cq : Z.X.K) (ψ : (𝓞 Z.X.E ⧸ P.1.asIdeal)ˣ →* Z.X.Kˣ),
      P.1.valuation Z.X.E (Formalism.L2.Col.qOf P.1 : Z.X.E) = exp (-1 : ℤ) → w.valuation Z.X.K cq = 1 →
      w.valuation Z.X.K (LocE.locChar (Formalism.L2.Col.qOf P.1) cq ψ a) = 1 := by
    intro cq ψ h1 h2
    obtain ⟨z, ζ, hζ, e⟩ := GlobalTheory.LocCharVal.locChar_eq_zpow_mul Z.X.E Z.X.K P.1 _ cq ψ a h1 ha
    rw [e, map_mul, map_zpow₀, h2, unit_of_finOrder hζ, one_zpow, one_mul]
  unfold muAtT
  by_cases hP : P.1 ∈ Z.Pr.vGs
  · refine key _ _ (val_q_vG hZ.fields hZ.primes hP) ?_
    rw [if_pos hP]
    have h1 := hc i.1 i.2 P hP (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) rfl
    have h2 : Z.sig0 ((cst.muq (i.1 + 1) P * ((qVal (mu : Chr Z.X.F Z.X.E Z.X.K) P.1 : Z.X.Kˣ) : Z.X.K))⁻¹) =
        (((m0 i).locK P.1 (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) : ℂˣ) : ℂ) := by
      rw [map_inv₀, map_mul, h1, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one, inv_inv]
    have h3 := mu_unit hZ.fields hZ.primes (ht.mu0 i) _ h2 hTP hw
    rwa [map_inv₀, map_mul, hq, mul_one, inv_eq_one] at h3
  · obtain ⟨v, hv, e⟩ := (mem_rowSG_cases P.2).resolve_left hP
    have hgood : GoodPl Z.X.E S v := by
      by_contra hn
      exact hv (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 mu.2).2 v) hn)
    have hd := Proof.NormalFormAtPrime.degOne_of_split hZ.fields.rankE hgood.1 hgood.2.1 (P := P.1) (e ▸ hsel v)
    refine key _ _ (val_natCast_of_notMem_sq (Ideal.absNorm_mem _) hd.2) ?_
    have hg : ∀ k, ((Z.Pr.g k : ℕ) : 𝓞 Z.X.E) ∉ P.1.asIdeal := fun k h => hG k v ((natCast_mem_sel hsel v _).1 (e ▸ h)) hv
    rw [if_neg hP, muqT, dif_pos i.2, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀,
      hq, muVal_unit hZ ht i hg hTP hw]
    simp

theorem locProd_unit (hZ : Z.Ok) (ht : Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta) (hsel : IsSel Z.X sel) {u : Z.Pr.Word}
    (hT : UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.T u)) (hG : ∀ k, UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.g k))
    (hc : MuqTieG (Pr := Z.Pr) (R := Z.R) sel mu cst Z.sig0 m0) (i : Fin Z.R.m)
    {w : HeightOneSpectrum (𝓞 Z.X.K)} (hw : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal) {n : ℕ}
    (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) :
    w.valuation Z.X.K (∏ P : rowSG Z.Pr sel mu, muAtT Z.Ch sel mu cst i.1 P ((LinearEquiv.det (fr P) : Z.X.Eˣ) : Z.X.E)) = 1 := by
  rw [map_prod]
  exact Finset.prod_eq_one fun P _ => muAtT_unit hZ ht hsel hT hG hc i hw P (Units.ne_zero _)

theorem half_N (R : Ranks) (i : ℕ) : (((R.N i / 2 : ℕ) : ℤ) : ℚ) = (R.N i : ℚ) / 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  have : R.N i = 2 * (a + i * (c + 1)) := by unfold Ranks.N; rw [ha, hc]; ring
  rw [this, Nat.mul_div_cancel_left _ two_pos]
  push_cast
  ring

theorem half_N_succ (R : Ranks) (i : ℕ) : R.N (i + 1) / 2 = R.N i / 2 + (R.t + 1) / 2 := by
  obtain ⟨c, hc⟩ := R.t_odd
  have : R.N (i + 1) = R.N i + 2 * (c + 1) := by unfold Ranks.N; rw [hc]; ring
  omega

theorem muOff_vpLat (hZ : Z.Ok) (ht : Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta) (hsel : IsSel Z.X sel) {u : Z.Pr.Word}
    (hT : UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.T u)) (i : Fin Z.R.m)
    {w : HeightOneSpectrum (𝓞 Z.X.K)} (hw : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal) {P : HeightOneSpectrum (𝓞 Z.X.E)}
    (hP : P ∈ Z.Pr.vT u) (τ : Z.X.Tau) :
    (SeesP w τ P → val_vp w (Z.Pr.T u) (muOff sel (rowSG Z.Pr sel mu) (mUof Z.Ch mu i.1) (vpLat P)) = -(Z.W.row τ).e i) ∧
    (SeesPbar w τ P → val_vp w (Z.Pr.T u) (muOff sel (rowSG Z.Pr sel mu) (mUof Z.Ch mu i.1) (vpLat P)) = (Z.W.row τ).e i) := by
  have hS := splitOver_vT hZ.fields hZ.primes u hP
  obtain ⟨-, m1, m2, m3, -⟩ := GlobalTheory.CharVal.Vp.vp_main Z.X.E P hS.ne
  set v₀ : HeightOneSpectrum (𝓞 Z.X.F) := P.under (𝓞 Z.X.F) with hv₀
  have hPv : P.asIdeal.under (𝓞 Z.X.F) = v₀.asIdeal := rfl
  have hTv : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.F) ∈ v₀.asIdeal := by
    rw [← hPv, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hS.mem
  have hno : ¬ ∃ Q ∈ rowSG Z.Pr sel mu, Q.asIdeal.under (𝓞 Z.X.F) = v₀.asIdeal := by
    rintro ⟨Q, hQ, e⟩
    apply T_notMem_rowSG hZ hsel hT hQ
    rw [← e, Ideal.under_def, Ideal.mem_comap, map_natCast] at hTv
    exact hTv
  have hsel0 : sel v₀ = P ∨ sel v₀ = conjPrime₂ P := eq_or_eq_conjP hZ.fields hS.ne (hsel v₀)
  obtain ⟨ε, hε, hord⟩ : ∃ ε : ℤ, ((sel v₀ = P ∧ ε = 1) ∨ (sel v₀ = conjPrime₂ P ∧ ε = -1)) ∧ ordDet (sel v₀) (vpLat P) = ε := by
    rcases hsel0 with h | h
    · exact ⟨1, Or.inl ⟨h, rfl⟩, by rw [h]; exact ordDet_vpLat hS.ne m1⟩
    · exact ⟨-1, Or.inr ⟨h, rfl⟩, by rw [h]; exact ordDet_vpLat hS.ne (by rw [neg_neg]; exact m2)⟩
  have hε2 : (ε : ℚ) * ε = 1 := by rcases hε with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hoff : muOff sel (rowSG Z.Pr sel mu) (mUof Z.Ch mu i.1) (vpLat P) = ((mUof Z.Ch mu i.1 (sel v₀) : Z.X.Kˣ) : Z.X.K) ^ ε := by
    unfold muOff
    rw [finprod_eq_single _ v₀, if_neg hno, hord, Units.val_zpow_eq_zpow_val]
    intro v hv
    split_ifs
    · rfl
    · have a : sel v ≠ P := fun e => hv (HeightOneSpectrum.ext (by rw [← hsel v, e, hPv]))
      have b : sel v ≠ conjPrime₂ P := fun e => hv (HeightOneSpectrum.ext (by rw [← hsel v, e, under_conjP hZ.fields, hPv]))
      rw [ordDet_vpLat hS.ne (m := 0) (by simpa using m3 _ a b), zpow_zero, Units.val_one]
  have key := mu_val hZ.fields hZ.primes (ht.mu0 i) hS hε (ht.muVal i _ (g_notMem_sel hZ hsel hno)) hw τ
  rw [hoff, val_vp_zpow, mUof_val, val_vp_mul (by simp) (by simp), val_vp_inv, val_vp_inv,
    val_vp_unit (unit_of_finOrder (finOrder_unifVal (finOrder_tup mu) _))]
  constructor
  · intro hτ
    rw [key.1 hτ]
    linear_combination (-(Z.W.row τ).e i) * hε2
  · intro hτ
    rw [key.2 hτ]
    linear_combination ((Z.W.row τ).e i) * hε2

end PartsMu

theorem charValAtT : CharValAtT := by
  intro Z D s χ u hZ hs _ hχ hK
  refine ⟨partA hZ hs hχ hK u, fun w hw => partBChi hs hχ hK u hw, ?_⟩
  intro m0 eta ht sel hsel S mu hT hG cst hc i
  refine ⟨fun w hw => ⟨?_, ?_⟩, ?_⟩
  · have hinv : ∀ (n : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)), StdOver (Z.Pr.T u) N →
        ∀ fr : Frs Z.X.E n (rowSG Z.Pr sel mu), w.valuation Z.X.K (muInv Z sel mu cst i.1 N fr) = 1 := by
      intro n N hS fr
      rw [muInv, muInvDet, map_mul, muOff_unit hZ ht hsel i hw hS, locProd_unit hZ ht hsel hT hG hc i hw fr, one_mul]
    refine ⟨fun n N hN hS => ⟨muOff_unit hZ ht hsel i hw hS, fun fr _ => ?_⟩, fun a b N fr N' fr' _ _ hS hS' _ _ => ?_⟩
    · have h1 : w.valuation _ _ = 1 := chiDet_unit hs hχ hK hw hN hS
      refine ⟨hinv n N hS fr, ?_, ?_⟩
      · rw [UnitAt, rho, map_mul, map_zpow₀, h1, hinv n N hS fr, one_zpow, one_mul]
      · rw [UnitAt, rho', map_mul, map_zpow₀, map_inv₀, h1, hinv n N hS fr, one_zpow, inv_one, one_mul]
    · rw [UnitAt, scal, map_mul, map_inv₀, hinv a N hS fr, hinv b N' hS' fr', inv_one, one_mul]
  · intro P hP τ hτ
    have hS := splitOver_vT hZ.fields hZ.primes u hP
    obtain ⟨⟨J, j1, j2⟩, -, -, -, e⟩ := GlobalTheory.CharVal.Vp.vp_main Z.X.E P hS.ne
    have hdet : chiDet s χ (vpLat P) = chiVp s χ P := by rw [chiDet_eq, e, chiVp]
    have hc0 : chiVp s χ P ≠ 0 := chiK_ne_zero hs hχ hK j1 j2
    have hl := locProd_unit hZ ht hsel hT hG hc i hw (n := 1) (fun _ => 1)
    have hl0 := UnitAt.ne_zero hl
    have hm0 : muInv Z sel mu cst i.1 (vpLat P) (fun _ => 1) ≠ 0 := mul_ne_zero (muOff_ne_zero _ _) hl0
    have hm : val_vp w (Z.Pr.T u) (muInv Z sel mu cst i.1 (vpLat P) (fun _ => 1)) =
        (Z.W.row τ).e i * val_vp w (Z.Pr.T u) (chiVp s χ P) := by
      have a := muOff_vpLat hZ ht hsel hT i hw hP τ
      have b := ((partA hZ hs hχ hK u P hP).2.2 w hw τ)
      rw [muInv, muInvDet, val_vp_mul (muOff_ne_zero _ _) hl0, val_vp_unit hl, add_zero]
      rcases hτ with hτ | hτ
      · rw [a.1 hτ, b.1 hτ]; ring
      · rw [a.2 hτ, b.2 hτ]; ring
    rw [rho, rho', hdet]
    refine ⟨mul_ne_zero hm0 (zpow_ne_zero _ hc0), mul_ne_zero (inv_ne_zero hm0) (zpow_ne_zero _ hc0), ?_, ?_⟩
    · rw [val_vp_mul hm0 (zpow_ne_zero _ hc0), val_vp_zpow, hm, Int.cast_neg, half_N, sPrime, sExp']
      ring
    · rw [val_vp_mul (inv_ne_zero hm0) (zpow_ne_zero _ hc0), val_vp_zpow, val_vp_inv, hm, half_N, sPlain, sExp,
        Nat.add_sub_cancel]
      ring
  · intro n N fr hN _
    obtain ⟨w, hw⟩ := exists_over Z.X.K (hZ.primes.T_prime u)
    have h0 := chiDet_ne_zero hs hχ hK hN
    have hm0 : muInv Z sel mu cst i.1 N fr ≠ 0 :=
      mul_ne_zero (muOff_ne_zero _ _) (UnitAt.ne_zero (locProd_unit hZ ht hsel hT hG hc i hw fr))
    refine ⟨h0, ?_⟩
    rw [rho, rho', mul_mul_mul_comm, mul_inv_cancel₀ hm0, one_mul, ← zpow_add₀ h0, half_N_succ]
    congr 1
    push_cast
    ring

end GlobalTheory.CharVal
