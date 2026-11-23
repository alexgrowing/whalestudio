import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecAct
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationFinOrderApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

noncomputable section

namespace GlobalTheory.KerTie.MuqUnit

theorem dvd_absNorm_of_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (h : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal) : p ∣ Ideal.absNorm P.asIdeal := by
  by_contra hn
  have hc : IsCoprime ((p : ℤ)) ((Ideal.absNorm P.asIdeal : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 E))
  have h1 : (1 : 𝓞 E) ∈ P.asIdeal := by
    rw [← hab]
    refine P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ ?_) (P.asIdeal.mul_mem_left _ ?_)
    · simpa using h
    · simpa using Ideal.absNorm_mem P.asIdeal
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem exists_coprime_mul_isIntegral {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (x : K)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → w.valuation K x ≤ 1) :
    ∃ M : ℕ, M.Coprime p ∧ IsIntegral ℤ ((M : K) * x) := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  have hd0 : y.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hy0
  have hdint : IsIntegral ℤ ((y.natAbs : K) * x) := by
    rcases Int.natAbs_eq y with e | e
    · have e2 : ((y.natAbs : ℤ) : K) = (y : K) := congrArg (fun z : ℤ => (z : K)) e.symm
      have : (y.natAbs : K) * x = y • x := by
        rw [zsmul_eq_mul, ← e2, Int.cast_natCast]
      rw [this]; exact hyint
    · have : (y.natAbs : K) * x = -(y • x) := by
        rw [zsmul_eq_mul, ← neg_mul]; congr 1
        have e' : (y : K) = -((y.natAbs : ℤ) : K) := by
          have := congrArg (fun z : ℤ => (z : K)) e
          simpa using this
        rw [e', neg_neg, Int.cast_natCast]
      rw [this]; exact hyint.neg
  obtain ⟨e, M, hpM, hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.ne_one
  refine ⟨M, (Nat.Prime.coprime_iff_not_dvd hp).2 hpM |>.symm, ?_⟩
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((M : K) * x) fun w => by
    by_cases hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal
    · rw [map_mul]
      refine mul_le_one' ?_ (h w hw)
      have := w.valuation_le_one (K := K) (M : 𝓞 K)
      simpa using this
    · obtain ⟨s, hs⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((y.natAbs : K) * x) fun v => by
        obtain ⟨t, ht⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K) (R := ℤ) (B := K)).1 hdint
        rw [← ht]; exact v.valuation_le_one t
      have hp1 : w.valuation K (p : K) = 1 := by
        have := (w.intValuation_eq_one_iff (x := ((p : ℕ) : 𝓞 K))).2 hw
        rw [← map_natCast (algebraMap (𝓞 K) K), HeightOneSpectrum.valuation_of_algebraMap]
        exact this
      have hle : w.valuation K ((y.natAbs : K) * x) ≤ 1 := by rw [← hs]; exact w.valuation_le_one s
      rw [hd, Nat.cast_mul, Nat.cast_pow, mul_assoc, map_mul, map_pow, hp1, one_pow, one_mul] at hle
      exact hle
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r

theorem intOff_of_val {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (S : Finset ℕ) (x : K)
    (h : ∀ p : ℕ, p.Prime → p ∉ S → ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → w.valuation K x ≤ 1) :
    IntOff S (σ x) := by
  have hQ : σ x ∈ TaylorLogMetric.Qbar := by
    rw [TaylorLogMetric.Qbar, mem_algebraicClosure_iff']
    exact (Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom
  refine ⟨hQ, fun p hp lam hpS => ?_⟩
  rw [lamC_of_mem lam hQ]
  obtain ⟨M, hM, hint⟩ := exists_coprime_mul_isIntegral hp.out x (h p hp.out hpS)
  have h1 : IsIntegral ℤ ((M : ℂ) * σ x) := by
    have := map_isIntegral_int σ hint
    simpa using this
  have h2 : IsIntegral ℤ ((M : TaylorLogMetric.Qbar) * (⟨σ x, hQ⟩ : TaylorLogMetric.Qbar)) :=
    (isIntegral_algHom_iff ((algebraMap TaylorLogMetric.Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 (by simpa using h1)
  exact GlobalTheory.HeckeVal.norm_le_one_of_denom lam hM h2

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie.MuqUnit

open GlobalTheory.CharVal

variable {X : Fields} {Pr : Primes X} {m : ℕ} {Ch : Chars X Pr m} {σ₀ : X.K →+* ℂ} {e : X.Tau → ℚ} {j : Fin m}
  {μ : Formalism.L2.Host.HChar X.E}

theorem mu_core_of_conj (hconj : ∀ τ (x : X.E), X.embC σ₀ τ (star x) = starRingEnd ℂ (X.embC σ₀ τ x)) (hPr : Pr.Ok)
    (hμ : IsMu0 Ch σ₀ e j μ) (P : HeightOneSpectrum (𝓞 X.E)) (k : X.Eˣ) {c : X.K}
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
  rw [map_div₀, hconj, div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem mu_unit_of_conj (hconj : ∀ τ (x : X.E), X.embC σ₀ τ (star x) = starRingEnd ℂ (X.embC σ₀ τ x)) (hPr : Pr.Ok)
    (hμ : IsMu0 Ch σ₀ e j μ) {P : HeightOneSpectrum (𝓞 X.E)} (k : X.Eˣ) {c : X.K}
    (hc : σ₀ c = ((μ.locK P k : ℂˣ) : ℂ)) {p : ℕ} (hP : ((p : ℕ) : 𝓞 X.E) ∉ P.asIdeal) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) : w.valuation X.K c = 1 := by
  obtain ⟨M, z, n, hM, -, -, h2, h3⟩ := mu_core_of_conj hconj hPr hμ P k hc
  refine unit_of_pow (M := 2 * M) (by omega) ?_
  rw [h3]
  refine val_prod_unit w (fun τ => ?_) n
  have h4 := (natCast_mem_pullW τ w p).2 hw
  rw [map_div₀, ← valuation_conjP, h2 _ (fun e' => hP (e' ▸ h4)), h2 _ (fun e' => hP (e' ▸ (natCast_mem_conjP _ p).2 h4)), div_one]

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie.MuqUnit

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

theorem embC_star (t : KerEntTied ex) (τ : t.X.Tau) (x : t.X.E) :
    t.X.embC t.seam.σ₀ τ (star x) = starRingEnd ℂ (t.X.embC t.seam.σ₀ τ x) := by
  change t.seam.σ₀ (t.X.emb τ (star x)) = starRingEnd ℂ (t.seam.σ₀ (t.X.emb τ x))
  rw [t.seam_ok.1, t.seam_ok.1, t.seam_ok.2]
  exact D.host.conjE_apply (TaylorLogMetric.embT D (t.seam.iT τ)) (t.seam.iE x)

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie

open MuqUnit

theorem muq_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < D.R.m → ∀ P : rowSG t.Pr t.sel (t.tup μ), P.1 ∉ t.Pr.vGs → IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).muq (i + 1) P)) ∧ IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).muq (i + 1) P)⁻¹) := by
  intro D L hT Gi Gl K Y cX ex t hmu hval u μ hQg i hi P hP
  have hPQ : P.1 ∈ QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K) := (Finset.mem_union.1 P.2).resolve_left hP
  have hg : ∀ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal := fun k hk =>
    hQg k (t.g_rec k ▸ (t.Q_rec μ (t.Pr.g k)).2 ⟨t.pr_ok.g_prime k, P.1, hPQ, hk⟩)
  have hq := (t.idx_ok μ).muqQ i hi P hP
  have key : ∀ p : ℕ, p.Prime → p ∉ (t.O u μ).S → ∀ w : HeightOneSpectrum (𝓞 t.X.K), ((p : ℕ) : 𝓞 t.X.K) ∈ w.asIdeal →
      w.valuation t.X.K ((t.cst μ).muq (i + 1) P) = 1 := by
    intro p hp hpS w hw
    have hpP : ((p : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal := fun h =>
      hpS ((sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P).2 p hp (dvd_absNorm_of_mem P.1 hp h))
    obtain ⟨e, he⟩ := hmu ⟨i, hi⟩
    have hm := mu_unit_of_conj (embC_star t) t.pr_ok he (Formalism.L2.Host.unif P.1) (hval ⟨i, hi⟩ P.1 hg) hpP hw
    have htw := (GlobalTheory.ColPeriod.twistUnit t.X.F t.X.E t.X.K t.S (t.tup μ) P.1 w).2
    rw [hq, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, hm, htw]
    simp
  refine ⟨intOff_of_val _ _ _ fun p hp hpS w hw => (key p hp hpS w hw).le, ?_⟩
  have h2 := intOff_of_val t.seam.σ₀ (t.O u μ).S ((t.cst μ).muq (i + 1) P)⁻¹ fun p hp hpS w hw => by
    rw [map_inv₀, key p hp hpS w hw, inv_one]
  exact h2

end GlobalTheory.KerTie
