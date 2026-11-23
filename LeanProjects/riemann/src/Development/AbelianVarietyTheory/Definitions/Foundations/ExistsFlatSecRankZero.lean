import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.BeSumStatementIffDefectSumBound
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfB
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfD
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumPf

noncomputable section

namespace GlobalTheory.FlatLine

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

section Line

variable {K : Type} [Field K] [NumberField K]

def lineDeg (r : (K →+* ℂ) → ℝ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ) : ℝ :=
  (∑ᶠ la, ρ la * lw K la) - (∑ σ, Real.log (r σ)) / (finrank ℚ K : ℝ)

omit [NumberField K] in

theorem fin_mul {ρ : HeightOneSpectrum (𝓞 K) → ℝ} (h : (Function.support ρ).Finite)
    (g : HeightOneSpectrum (𝓞 K) → ℝ) : (Function.support fun la => ρ la * g la).Finite :=
  h.subset (Function.support_mul_subset_left _ _)

theorem lineDeg_mul {r r' : (K →+* ℂ) → ℝ} {ρ ρ' : HeightOneSpectrum (𝓞 K) → ℝ} (hr : ∀ σ, 0 < r σ)
    (hr' : ∀ σ, 0 < r' σ) (h : (Function.support ρ).Finite) (h' : (Function.support ρ').Finite) :
    lineDeg (r * r') (ρ + ρ') = lineDeg r ρ + lineDeg r' ρ' := by
  simp only [lineDeg, Pi.add_apply, Pi.mul_apply, add_mul, Real.log_mul (hr _).ne' (hr' _).ne',
    Finset.sum_add_distrib]
  rw [finsum_add_distrib (fin_mul h _) (fin_mul h' _)]
  ring

theorem lineDeg_inv (r : (K →+* ℂ) → ℝ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ) : lineDeg r⁻¹ (-ρ) = -lineDeg r ρ := by
  simp only [lineDeg, Pi.neg_apply, Pi.inv_apply, neg_mul, Real.log_inv, Finset.sum_neg_distrib, finsum_neg_distrib]
  ring

theorem lineDeg_one : lineDeg (K := K) 1 0 = 0 := by simp [lineDeg]

theorem finite_vAdd {a : K} (ha : a ≠ 0) :
    (Function.support fun la : HeightOneSpectrum (𝓞 K) => (vAdd la a : ℝ)).Finite := by
  have h := (FinitePlace.hasFiniteMulSupport ha).preimage
    (f := FinitePlace.equivHeightOneSpectrum.symm) (Equiv.injective _).injOn
  refine h.subset fun la hla h1 => hla ?_
  have h2 : FinitePlace.mk la a = 1 := h1
  rw [finitePlace_eq_zpow la ha, zpow_eq_one_iff_right₀ (by positivity) (one_lt_absNorm_real la).ne'] at h2
  have : vAdd la a = 0 := neg_eq_zero.1 h2
  simp [this]

theorem lineDeg_num {a : K} (ha : a ≠ 0) : lineDeg (fun σ : K →+* ℂ => ‖σ a‖) (fun la => (vAdd la a : ℝ)) = 0 := by
  have h1 := FinitePlace.prod_eq_inv_abs_norm ha
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at h1
  have h2 : ∀ la : HeightOneSpectrum (𝓞 K), FinitePlace.equivHeightOneSpectrum.symm la a =
      Real.exp (-((vAdd la a : ℝ) * Real.log (Ideal.absNorm la.asIdeal : ℝ))) := fun la => by
    show FinitePlace.mk la a = _
    rw [finitePlace_eq_zpow la ha, ← Real.rpow_intCast, Real.rpow_def_of_pos (by linarith [one_lt_absNorm_real la])]
    congr 1
    simp only [vLa, vAdd]; push_cast; ring
  have hf := fin_mul (finite_vAdd ha) fun la => Real.log (Ideal.absNorm la.asIdeal : ℝ)
  have h3 : ∏ᶠ la : HeightOneSpectrum (𝓞 K), FinitePlace.equivHeightOneSpectrum.symm la a =
      Real.exp (-∑ᶠ la : HeightOneSpectrum (𝓞 K), (vAdd la a : ℝ) * Real.log (Ideal.absNorm la.asIdeal : ℝ)) := by
    rw [finsum_eq_sum _ hf, ← Finset.sum_neg_distrib, Real.exp_sum, finprod_eq_prod_of_mulSupport_subset (s := hf.toFinset)]
    · exact Finset.prod_congr rfl fun la _ => h2 la
    · intro la hla
      simp only [Set.Finite.coe_toFinset]
      intro h0
      apply hla
      simp only at h0 ⊢
      rw [h2, h0]; simp
  have h4 : ∑ σ : K →+* ℂ, Real.log ‖σ a‖ = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
    rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.2 ((map_ne_zero σ).2 ha)), ← norm_prod]
    congr 1
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ a
    rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ : K →+* ℂ => σ a) _ (fun _ => rfl)] at this
    rw [← this]
    simp
  rw [h3] at h1
  have h5 := congrArg Real.log h1
  rw [Real.log_exp, Rat.cast_inv, Real.log_inv, Rat.cast_abs, neg_inj] at h5
  simp only [lineDeg, lw, ← mul_div_assoc]
  rw [h4, ← h5]
  simp only [div_eq_mul_inv]
  rw [finsum_mul, sub_self]

theorem sum_vAdd_nat {n : ℕ} (hn : n ≠ 0) : ∑ᶠ la, (vAdd la (n : K) : ℝ) * lw K la = Real.log n := by
  have h := lineDeg_num (K := K) (a := n) (Nat.cast_ne_zero.2 hn)
  have hK : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  simp only [lineDeg, map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ, Embeddings.card,
    nsmul_eq_mul] at h
  rw [sub_eq_zero.1 h]; field_simp

theorem vla_span {x : 𝓞 K} (hx : x ≠ 0) (la : HeightOneSpectrum (𝓞 K)) :
    (QAt.vla la (Ideal.span {x}) : ℤ) = vAdd la (x : K) := by
  classical
  rw [vAdd, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hx]
  simp [QAt.vla]

theorem vAdd_natCast {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : n ≠ 0) {la : HeightOneSpectrum (𝓞 K)}
    (hm : (ℓ : 𝓞 K) ∈ la.asIdeal) : vAdd la (n : K) = padicValNat ℓ n * vAdd la (ℓ : K) := by
  obtain ⟨k, m, hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn ℓ hℓ.ne_one
  haveI := Fact.mk hℓ
  have hm0 : m ≠ 0 := by rintro rfl; exact hnd (dvd_zero _)
  have h1 : la.valuation K ((m : 𝓞 K) : K) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hmm
    have hc : IsCoprime (ℓ : 𝓞 K) (m : 𝓞 K) := Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hnd)
    obtain ⟨a, b, hab⟩ := hc
    exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hmm)))
  have h1' : la.valuation K (m : K) = 1 := by simpa using h1
  rw [padicValNat.mul (pow_ne_zero _ hℓ.ne_zero) hm0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hnd]
  simp [vAdd, h1']

variable {E : Type} [Field E] [NumberField E]

theorem finite_ord (σ : E →+* K) :
    (Function.support fun la : HeightOneSpectrum (𝓞 K) => (ord_vw la (conjDifferent σ) : ℝ)).Finite :=
  (Ideal.finite_factors (conjDifferent_ne_bot σ)).subset fun la h => by
    refine (QAt.BeSumPf.vla_ne_zero_iff la (conjDifferent_ne_bot σ)).1 fun h0 => h ?_
    simp [DefectSumCompare.ord_vw_eq_vla la (conjDifferent_ne_bot σ), h0]

theorem sum_ord (σ : E →+* K) : ∑ᶠ la, (ord_vw la (conjDifferent σ) : ℝ) * lw K la = lrd E := by
  have hf := fin_mul (finite_ord σ) fun la => Real.log (Ideal.absNorm la.asIdeal : ℝ)
  have h1 := QAt.BeSumPf.sum_vla_log_fin _ (conjDifferent_ne_bot σ) (finite_ord σ).toFinset fun v hv => by
    simpa [DefectSumCompare.ord_vw_eq_vla v (conjDifferent_ne_bot σ)] using hv
  letI := σ.toAlgebra
  have h2 : Ideal.absNorm (conjDifferent σ) = (discr E).natAbs ^ finrank E K := by
    have := Ideal.absNorm_algebraMap (𝓞 E) (𝓞 K) (differentIdeal ℤ (𝓞 E))
    rw [absNorm_differentIdeal E, ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K] at this
    exact this
  have h3 : (finrank ℚ K : ℝ) = finrank ℚ E * finrank E K := by
    rw [← Module.finrank_mul_finrank ℚ E K]; push_cast; rfl
  have hK : (finrank E K : ℝ) ≠ 0 := by
    intro h; rw [h, mul_zero] at h3; exact (Nat.cast_ne_zero.mpr finrank_pos.ne') h3
  have hE : (finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  simp only [lw, div_eq_mul_inv, ← mul_assoc]
  rw [← finsum_mul, finsum_eq_sum_of_support_subset (s := (finite_ord σ).toFinset) _
    (by simpa using Function.support_mul_subset_left _ _)]
  simp only [DefectSumCompare.ord_vw_eq_vla _ (conjDifferent_ne_bot σ)] at h1 ⊢
  rw [h1, h2, h3, Nat.cast_pow, Real.log_pow, Nat.cast_natAbs, Int.cast_abs, DefectSumCompare.log_discr_eq]
  field_simp

end Line

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  Formalism.L2.Pj.CompSplitPfB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

def parWt (Dw : Datum H) (w : Psi H → ℤ) : Weight Dw := fun τ _ => w τ

open Classical in

def flatWt (Dw : Datum H) (τ : Psi H) : Weight Dw := parWt Dw fun τ' => if τ' = τ then -1 else 0

theorem parWt_eq_sum (w : Psi H → ℤ) : parWt Dw w = ∑ τ, (-w τ) • flatWt Dw τ := by
  classical
  funext τ i
  simp [parWt, flatWt, Finset.sum_apply]

example (τ : Psi H) (i : Fin (Dw.mult τ.1)) (j : Fin (Dw.mult (conjEmb τ.1))) (hi : (i : ℕ) < Dw.p)
    (hj : (j : ℕ) < Dw.q) : exOf Dw (flatWt Dw τ) 0 (some ⟨τ.1, i⟩) = -1 ∧
      exOf Dw (flatWt Dw τ) 0 (some ⟨conjEmb τ.1, j⟩) = 1 ∧ exOf Dw (flatWt Dw τ) 0 none = 0 := by
  refine ⟨(wtOf_big _ 0 τ i hi).trans ?_, (wtOf_small _ 0 τ j hj).trans ?_, rfl⟩ <;> simp [flatWt, parWt]

def different_vp (E : Type) [Field E] [NumberField E] (ℓ : ℕ) : ℚ :=
  (padicValNat ℓ (discr E).natAbs : ℚ) / (finrank ℚ E : ℚ)

def flDefect_vp (Dw : Datum H) (ℓ : ℕ) : ℚ := Dw.q * (different_vp E ℓ - if ℓ = H.d then 1 else 0)

theorem flDefect_vp_of_ne {ℓ : ℕ} (h : ℓ ≠ H.d) : flDefect_vp Dw ℓ = Dw.q * different_vp E ℓ := by
  simp [flDefect_vp, h]

theorem flDefect_vp_d (h : different_vp E H.d = 1 / 2) : flDefect_vp Dw H.d = -(Dw.q * different_vp E H.d) := by
  simp only [flDefect_vp, h, if_true]; ring

theorem flDefect_vp_eq_zero {ℓ : ℕ} (h : ℓ ≠ H.d) (h' : ¬ ℓ ∣ (discr E).natAbs) : flDefect_vp Dw ℓ = 0 := by
  simp [flDefect_vp, h, different_vp, padicValNat.eq_zero_of_not_dvd h']

def flDefect_vw (Dw : Datum H) (c : Coeff l) (τ : Psi H) (la : HeightOneSpectrum (𝓞 c.F)) : ℝ :=
  Dw.q * ((ord_vw la (conjDifferent (embF c τ.1)) : ℝ) - (vAdd la (H.d : c.F) : ℝ))

variable {c : Coeff l}

theorem flDefect_vw_eq [IsGalois ℚ E] (τ : Psi H) {ℓ : ℕ} (hℓ : ℓ.Prime) {la : HeightOneSpectrum (𝓞 c.F)}
    (hm : (ℓ : 𝓞 c.F) ∈ la.asIdeal) :
    flDefect_vw Dw c τ la = (vAdd la (ℓ : c.F) : ℝ) * (flDefect_vp Dw ℓ : ℝ) := by
  have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have h1 := DefectSumCompare.vla_discAt (embF c τ.1) la
  have h2 := vla_span (K := c.F) (x := ((discr E).natAbs : ℕ)) (Nat.cast_ne_zero.2 hd) la
  have h3 := vAdd_natCast hℓ hd hm
  have h4 : (finrank ℚ E : ℝ) * ord_vw la (conjDifferent (embF c τ.1)) =
      padicValNat ℓ (discr E).natAbs * (vAdd la (ℓ : c.F) : ℝ) := by
    have h5 : ((finrank ℚ E * ord_vw la (conjDifferent (embF c τ.1)) : ℕ) : ℤ) =
        padicValNat ℓ (discr E).natAbs * vAdd la (ℓ : c.F) := by
      rw [← h1, ← h3]; exact h2
    have h7 := congrArg (Int.cast : ℤ → ℝ) h5
    simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul] using h7
  have h6 : (vAdd la (H.d : c.F) : ℝ) = (if ℓ = H.d then 1 else 0) * (vAdd la (ℓ : c.F) : ℝ) := by
    split_ifs with h
    · rw [h, one_mul]
    · rw [vAdd_natCast hℓ H.d_prime.ne_zero hm, padicValNat.eq_zero_of_not_dvd
        fun h' => h ((Nat.prime_dvd_prime_iff_eq hℓ H.d_prime).1 h')]
      simp
  have hE : (finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  rw [flDefect_vw, h6, eq_div_of_mul_eq hE ((mul_comm _ _).trans h4), flDefect_vp, different_vp]
  split_ifs <;> push_cast <;> ring

theorem finite_flDefect_vw (τ : Psi H) : (Function.support (flDefect_vw Dw c τ)).Finite :=
  ((finite_ord (embF c τ.1)).union (finite_vAdd (K := c.F) (Nat.cast_ne_zero.2 H.d_prime.ne_zero))).subset
    fun la h => by
      by_contra hn
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
      exact h (by rw [flDefect_vw, hn.1, hn.2]; simp)

theorem sum_flDefect_vw (τ : Psi H) :
    ∑ᶠ la, flDefect_vw Dw c τ la * lw c.F la = Dw.q * (lrd E - Real.log H.d) := by
  simp only [flDefect_vw, mul_assoc, sub_mul]
  rw [← mul_finsum, finsum_sub_distrib (fin_mul (finite_ord _) _)
    (fin_mul (finite_vAdd (Nat.cast_ne_zero.2 H.d_prime.ne_zero)) _), sum_ord, sum_vAdd_nat H.d_prime.ne_zero]

variable {Xo : Moduli Dw l}

def idem (Z : Comp Xo c) : Rul Xo c := cspB_rule Xo c Z (cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z)

abbrev Tested {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Prop :=
  FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

theorem idem_mul_idem (Z : Comp Xo c) : idem Z * idem Z = idem Z :=
  funext fun _ => funext fun y =>
    (cspB_idem_idem _ (cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z) y.x y.x_over).eq

theorem idem_mem_secZ (Z : Comp Xo c) : idem Z ∈ secZ Xo c 0 :=
  ⟨cspB_rule_natural _ _, fun p t y y' h => by simp [idem, cspB_rule_bor _ _ p t y y' h]⟩

theorem evR_idem {Z : Comp Xo c} {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} (h : LiesOn Z y)
    (ht : Tested y) : evR Xo c (idem Z) y = 1 := by
  rw [idem, cspB_evR _ _ y ht]
  refine cspB_idem_eq_of (cspB_idem_idem _ _ _ _) IsIdempotentElem.one fun q => ?_
  rw [cspB_idem_spec]
  exact iff_of_true (h q) ((Ideal.ne_top_iff_one _).1 q.isPrime.ne_top)

theorem idem_mem_suppOn (Z : Comp Xo c) : idem Z ∈ suppOn Z := fun S _ _ y h => by
  by_cases ht : Tested y
  · rw [idem, cspB_evR _ _ y ht]
    refine cspB_idem_eq_of (cspB_idem_idem _ _ _ _) IsIdempotentElem.zero fun q => ?_
    rw [cspB_idem_spec]
    exact iff_of_false (h q) (not_not.2 q.asIdeal.zero_mem)
  · exact cspB_evR_zero y ht _

def algOn (Z : Comp Xo c) (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι) : Prop :=
  algCls Xo c T ι y ∧ (letI := ι.toAlgebra; LiesOn Z y.1)

def valOn (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) := valSet Xo c (algOn Z) la

theorem valOn_subset (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) :
    valOn Z la ⊆ valSet Xo c (algCls Xo c) la := by
  rintro _ ⟨y, rfl⟩
  exact ⟨PtV.widen (fun _ _ _ h => h.1) y, rfl⟩

theorem isVal_valOn {Z : Comp Xo c} {la : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ valOn Z la) :
    IsVal la v := isVal_valSet la v hv

theorem mem_valOn_or {Z : Comp Xo c} {la : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal}
    (hv : v ∈ valSet Xo c (algCls Xo c) la) : v ∈ valOn Z la ∨ ∀ f ∈ suppOn Z, v f = ⊤ := by
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  by_cases h : LiesOn Z y.1
  · exact Or.inl ⟨PtV.mk la ho y ⟨hy, h⟩ () trivial, rfl⟩
  · refine Or.inr fun f hf => ?_
    show nval T.V e (evR Xo c f y.1) = ⊤
    rw [hf _ _ ((liesOff_iff Z y.1).2 h), nval_zero]

theorem mem_supLat_iff {Z : Comp Xo c} {C : Submodule c.F (Rul Xo c)} {f : C} (hf : (f : Rul Xo c) ∈ suppOn Z) :
    f ∈ supLat C ↔ ∀ la, ∀ v ∈ valOn Z la, 0 ≤ v (f : Rul Xo c) :=
  ⟨fun h la v hv => h la v (valOn_subset Z la hv), fun h la v hv =>
    (mem_valOn_or (Z := Z) hv).elim (h la v) fun h' => (h' _ hf).symm ▸ le_top⟩

theorem val_idem {Z : Comp Xo c} {la : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ valOn Z la) :
    v (idem Z) = 0 := by
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  show nval T.V e (evR Xo c (idem Z) y.1) = 0
  rw [evR_idem hy.2 y.2.1, nval_of_ne one_ne_zero]
  simp [vV]

theorem val_rat {Z : Comp Xo c} {la : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ valOn Z la)
    {f : Rul Xo c} {a : ℝ} (h : v f = a) : ∃ b : ℚ, a = b := by
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  have h' : nval T.V e (evI y f) = a := h
  by_cases h0 : evI y f = 0
  · rw [h0, nval_zero] at h'; exact absurd h' (EReal.top_ne_coe a)
  · rw [nval_of_ne h0, EReal.coe_eq_coe_iff] at h'
    exact ⟨(vV T.V (evI y f) : ℚ) / e, by rw [← h']; push_cast; rfl⟩

section Horiz

variable {r : ℕ}

def horizGen {Ψ : Finset (E →+* ℂ)} (τ : Ψ) (x : Frame Ψ r) : ℂ := (mat x τ).det⁻¹

open Classical in

def modelFlat {Ψ : Finset (E →+* ℂ)} (r : ℕ) (τ : Ψ) : Wt Ψ r := fun τ' _ => if τ' = τ then -1 else 0

theorem det_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (y : Matrix (Fin r) (Fin r) ℂ) :
    ‖(gram τ G y).det‖ = ‖τ G.det‖ * ‖y.det‖ ^ 2 := by
  have : gram τ G y = y.transpose * τ.mapMatrix G * (starRingEnd ℂ).mapMatrix y := by
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply]
    exact Finset.sum_comm
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, ← RingHom.map_det, norm_mul,
    norm_mul, Complex.norm_conj]
  ring

theorem pnorm_horizGen (X : Data E r) (τ : X.Ψ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    X.pnorm (modelFlat r τ) (horizGen τ) y = Real.sqrt ‖τ.1 X.Gm.det‖ := by
  have hd : ∀ i, dmin X.Gm y τ i ≠ 0 := fun i h0 => by
    have := (hy τ).2 i
    rw [h0] at this; simp at this
  have h0 : dmin X.Gm y τ 0 = 1 := by
    unfold dmin lminor
    exact Matrix.det_isEmpty (n := Fin 0)
  have hl : dmin X.Gm y τ (Fin.last r) = (gram τ.1 X.Gm (mat y τ)).det := rfl
  have ht : ∏ i : Fin r, dmin X.Gm y τ i.succ / dmin X.Gm y τ i.castSucc = (gram τ.1 X.Gm (mat y τ)).det := by
    have h1 := (Fin.prod_univ_succ (dmin X.Gm y τ)).symm.trans (Fin.prod_univ_castSucc (dmin X.Gm y τ))
    rw [h0, one_mul, hl] at h1
    rw [Finset.prod_div_distrib, h1, mul_div_cancel_left₀ _ (Finset.prod_ne_zero_iff.2 fun i _ => hd _)]
  have hx : ‖(mat y τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hy τ).1
  rw [Data.pnorm, Finset.prod_eq_single τ (fun τ' _ h => by simp [modelFlat, h]) (by simp)]
  simp only [modelFlat, if_true]
  rw [Real.finset_prod_rpow _ _ (fun _ _ => norm_nonneg _), ← norm_prod, ht, det_gram, horizGen, norm_inv]
  rw [show (-((-1 : ℤ) : ℝ) / 2) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sqrt_mul (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]
  field_simp

theorem modelWt_flatWt {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (τ : Psi H) (k : U.Comp)
    (hτ : relab c σ τ.1 ∈ (U.X k).Ψ) : modelWt U (wtOf Dw (flatWt Dw τ) 0) k = modelFlat r ⟨_, hτ⟩ := by
  funext ⟨ρ, hρ⟩ j
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k
  have hr := hU.1
  have hj := j.2
  obtain ⟨ρ', rfl⟩ := Finite.injective_iff_surjective.1 (relab_injective (E := E) (c := c) σ) ρ
  have hρΨ : ρ' (H.rt : E) = H.rt0 := by
    by_contra hn
    have h3 : relab c σ (conjEmb ρ') (H.rt : E) = H.rt0 := by
      have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
      exact (congrArg σ (Subtype.ext (conj_mem hn))).trans hσ0
    rw [relab_conj] at h3
    exact conj_not_mem ⟨_, (hΨ _).1 hρ⟩ h3
  have e : ((⟨ρ', hρΨ⟩ : Psi H) = τ) ↔ ((⟨relab c σ ρ', hρ⟩ : (U.X k).Ψ) = ⟨_, hτ⟩) := by
    rw [Subtype.ext_iff, Subtype.ext_iff]; exact (relab_injective σ).eq_iff.symm
  by_cases h : (j : ℕ) < Dw.q
  · refine (modelWt_wtOf_small U _ 0 k hp0 ⟨ρ', hρΨ⟩ hρ j h hj).trans ?_
    simp only [flatWt, parWt, modelFlat]
    by_cases h1 : (⟨ρ', hρΨ⟩ : Psi H) = τ
    · rw [if_pos h1, if_pos (e.1 h1)]
    · rw [if_neg h1, if_neg (mt e.2 h1)]
  · have := modelWt_wtOf_big U (flatWt Dw τ) 0 k hp0 ⟨ρ', hρΨ⟩ hρ (j - Dw.q) (by omega) (by omega)
    have ej : j = ⟨Dw.q + (j - Dw.q), by omega⟩ := Fin.ext (by simp only; omega)
    rw [ej]
    refine this.trans ?_
    simp only [flatWt, parWt, modelFlat]
    by_cases h1 : (⟨ρ', hρΨ⟩ : Psi H) = τ
    · rw [if_pos h1, if_pos (e.1 h1)]
    · rw [if_neg h1, if_neg (mt e.2 h1)]

def IsHorizontal {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (Z : Comp Xo c) (τ : Psi H) (f : Rul Xo c) : Prop :=
  ∀ k, ∃ (hτ : relab c σ τ.1 ∈ (U.X k).Ψ) (a : ℂ), ∀ y, (⟨k, y⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z →
    rdU U f k y = a * horizGen ⟨_, hτ⟩ y

theorem IsHorizontal.homN_const {σ : c.F →+* ℂ} {U : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) (x : ℝ)
    {Z : Comp Xo c} {τ : Psi H} {f : Rul Xo c} (h : IsHorizontal U Z τ f) (k : U.Comp) :
    ∃ b : ℝ, ∀ y, (⟨k, y⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z →
      homN U x (wtOf Dw (flatWt Dw τ) 0) f ⟨k, y⟩ = b := by
  obtain ⟨hτ, a, ha⟩ := h k
  refine ⟨lieFacZ Dw x (wtOf Dw (flatWt Dw τ) 0) * (‖a‖ * Real.sqrt ‖relab c σ τ.1 (U.X k).Gm.det‖), fun y hy => ?_⟩
  rw [← pnorm_horizGen (U.X k) ⟨_, hτ⟩ hy.1, homN, ptN, modelWt_flatWt U hσ hU τ k hτ]
  simp only [Data.pnorm, ha y hy, norm_mul, mul_assoc]

end Horiz

section Norm

variable {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)

theorem homN_zero (f : Rul Xo c) (z : Σ k, Frame (U.X k).Ψ r) : homN U x 0 f z = ‖rdU U f z.1 z.2‖ := by
  simp [homN, lieFacZ, ptN, Data.pnorm, modelWt]

theorem homN_smul (G : WTZ E) (a : c.F) (f : Rul Xo c) (z : Σ k, Frame (U.X k).Ψ r) :
    homN U x G (a • f) z = ‖σ a‖ * homN U x G f z := by
  unfold homN ptN
  rw [map_smulₛₗ]
  exact (congrArg _ (pnorm_smul _ _ (σ a) _ _)).trans (by ring)

theorem tested_of_homN_ne {G : WTZ E} {f : Rul Xo c} {z : Σ k, Frame (U.X k).Ψ r} (hz : z.2 ∈ (U.X z.1).dom)
    (h : homN U x G f z ≠ 0) : Tested (U.un z.1 ⟨z.2, hz⟩) := by
  by_contra ht
  apply h
  have : rdU U f z.1 z.2 = 0 := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hz, dif_pos]
    exact cspB_evR_zero _ ht f
  simp [homN, ptN, Data.pnorm, this]

theorem homN_idem {Z : Comp Xo c} {z : Σ k, Frame (U.X k).Ψ r} (hz : z.2 ∈ (U.X z.1).dom)
    (h : LiesOn Z (U.un z.1 ⟨z.2, hz⟩)) (ht : Tested (U.un z.1 ⟨z.2, hz⟩)) : homN U x 0 (idem Z) z = 1 := by
  have : rdU U (idem Z) z.1 z.2 = 1 := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hz, dif_pos]
    exact evR_idem (S := CAt σ) h ht
  rw [homN_zero, this, norm_one]

end Norm

theorem image_eq_singleton_iff {α β : Type*} {f : α → β} {s : Set α} {a : β} :
    f '' s = {a} ↔ s.Nonempty ∧ ∀ z ∈ s, f z = a := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem, Set.image_nonempty, Set.forall_mem_image]

theorem smul_mul_inv_smul {K R : Type} [Field K] [CommRing R] [Algebra K R] {a : K} (ha : a ≠ 0) (f g : R) :
    a • f * a⁻¹ • g = f * g := by
  rw [smul_mul_smul_comm, mul_inv_cancel₀ ha, one_smul]

theorem wtOf_add' (la la' : Weight Dw) : wtOf Dw (la + la') 0 = wtOf Dw la 0 + wtOf Dw la' 0 := wtOf_add la la' 0 0

theorem exOf_add' (la la' : Weight Dw) : exOf Dw (la + la') 0 = exOf Dw la 0 + exOf Dw la' 0 := exOf_add la la' 0 0

theorem exOf_zero : exOf Dw 0 0 = 0 := by
  funext i; rw [exOf, wtOf_zero]; cases i <;> rfl

theorem exOf_neg (la : Weight Dw) : exOf Dw (-la) 0 = -exOf Dw la 0 :=
  eq_neg_of_add_eq_zero_left (by rw [← exOf_add', neg_add_cancel, exOf_zero])

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

def HasPts (Z : Comp Xo c) : Prop :=
  (∀ σ, (framesOn (U (goodOf c σ)) Z).Nonempty ∧ ∀ z ∈ framesOn (U (goodOf c σ)) Z,
    ∀ hz : z.2 ∈ ((U (goodOf c σ)).X z.1).dom, Tested ((U (goodOf c σ)).un z.1 ⟨z.2, hz⟩)) ∧
  ∀ w, (valOn Z w).Nonempty

structure ConstSec (Z : Comp Xo c) (la : Weight Dw) (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) : Type where

  sig : Rul Xo c

  inv : Rul Xo c
  sig_mem : sig ∈ secZ Xo c (exOf Dw la 0)
  inv_mem : inv ∈ secZ Xo c (-exOf Dw la 0)
  idem_sig : idem Z * sig = sig
  idem_inv : idem Z * inv = inv
  mul_inv : sig * inv = idem Z

  cInf : (c.F →+* ℂ) → ℝ
  cInf_pos : ∀ σ, 0 < cInf σ
  norm_inf : ∀ σ, homN (U (goodOf c σ)) x (wtOf Dw la 0) sig '' framesOn (U (goodOf c σ)) Z = {cInf σ}

  rho_vw : HeightOneSpectrum (𝓞 c.F) → ℝ
  val_fin : ∀ w, (fun v : Rul Xo c → EReal => v sig) '' valOn Z w = {((δ w + rho_vw w : ℝ) : EReal)}
  finite_rho : (Function.support rho_vw).Finite

namespace ConstSec

variable {U x} {Z : Comp Xo c} {la la' : Weight Dw} {δ δ' : HeightOneSpectrum (𝓞 c.F) → ℝ}

section Basic

variable (s : ConstSec U x Z la δ)

theorem sig_mem_suppOn : s.sig ∈ suppOn Z := by
  rw [← s.idem_sig, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)

theorem inv_mem_suppOn : s.inv ∈ suppOn Z := by
  rw [← s.idem_inv, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)

theorem evR_mul_inv {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} (h : LiesOn Z y) (ht : Tested y) :
    evR Xo c s.sig y * evR Xo c s.inv y = 1 := by
  rw [← cspB_evR_mul, s.mul_inv, evR_idem h ht]

theorem homN_eq {σ : c.F →+* ℂ} {z} (hz : z ∈ framesOn (U (goodOf c σ)) Z) :
    homN (U (goodOf c σ)) x (wtOf Dw la 0) s.sig z = s.cInf σ := (image_eq_singleton_iff.1 (s.norm_inf σ)).2 z hz

theorem val_eq {w} {v : Rul Xo c → EReal} (hv : v ∈ valOn Z w) : v s.sig = ((δ w + s.rho_vw w : ℝ) : EReal) :=
  (image_eq_singleton_iff.1 (s.val_fin w)).2 v hv

include s in

theorem hasPts : HasPts U Z :=
  ⟨fun σ => ⟨(image_eq_singleton_iff.1 (s.norm_inf σ)).1, fun _ hz hd =>
    tested_of_homN_ne _ x hd ((s.homN_eq hz).symm ▸ (s.cInf_pos σ).ne')⟩,
   fun w => (image_eq_singleton_iff.1 (s.val_fin w)).1⟩

theorem sig_ne_zero : s.sig ≠ 0 := fun h => by
  obtain ⟨z, hz⟩ := (s.hasPts.1 c.F.val.toRingHom).1
  have h1 := s.homN_eq hz
  rw [h, ← zero_smul c.F (0 : Rul Xo c), homN_smul, map_zero, norm_zero, zero_mul] at h1
  exact (s.cInf_pos _).ne h1

theorem homN_mul_sig {G : WTZ E} (hG : Even G.2) (f : Rul Xo c) {σ : c.F →+* ℂ} {z}
    (hz : z ∈ framesOn (U (goodOf c σ)) Z) :
    homN (U (goodOf c σ)) x (G + wtOf Dw la 0) (f * s.sig) z = homN (U (goodOf c σ)) x G f z * s.cInf σ := by
  rw [homN_mul _ x hG (even_wtOf _ _) _ _ _ hz.1, s.homN_eq hz]

theorem val_mul_sig (f : Rul Xo c) {w} {v : Rul Xo c → EReal} (hv : v ∈ valOn Z w) :
    v (f * s.sig) = v f + ((δ w + s.rho_vw w : ℝ) : EReal) := by
  rw [(isVal_valOn hv).mul, s.val_eq hv]

theorem exists_rat (w : HeightOneSpectrum (𝓞 c.F)) : ∃ b : ℚ, δ w + s.rho_vw w = b := by
  obtain ⟨v, hv⟩ := s.hasPts.2 w
  exact val_rat hv (s.val_eq hv)

def cFin (w : HeightOneSpectrum (𝓞 c.F)) : ℝ := (Ideal.absNorm w.asIdeal : ℝ) ^ (-s.rho_vw w)

def deg : ℝ := lineDeg s.cInf s.rho_vw

theorem sum_log_eq : ((∑ᶠ w, Real.log (s.cFin w)) + ∑ σ, Real.log (s.cInf σ)) / (finrank ℚ c.F : ℝ) = -s.deg := by
  have : ∀ w, Real.log (s.cFin w) = -(s.rho_vw w * Real.log (Ideal.absNorm w.asIdeal : ℝ)) := fun w => by
    rw [cFin, Real.log_rpow (by linarith [one_lt_absNorm_real w]), neg_mul]
  simp only [this, deg, lineDeg, lw, finsum_neg_distrib, div_eq_mul_inv, ← mul_assoc]
  rw [← finsum_mul]; ring

end Basic

theorem ext {s t : ConstSec U x Z la δ} (h : s.sig = t.sig) : s = t := by
  have h1 : s.inv = t.inv :=
    calc s.inv = t.sig * t.inv * s.inv := by rw [t.mul_inv, s.idem_inv]
      _ = s.sig * s.inv * t.inv := by rw [h, mul_right_comm]
      _ = t.inv := by rw [s.mul_inv, t.idem_inv]
  have h2 : s.cInf = t.cInf := funext fun σ =>
    Set.singleton_injective ((s.norm_inf σ).symm.trans (h ▸ t.norm_inf σ))
  have h3 : s.rho_vw = t.rho_vw := funext fun w => by
    have := Set.singleton_injective ((s.val_fin w).symm.trans (h ▸ t.val_fin w))
    exact add_left_cancel (EReal.coe_eq_coe_iff.1 this)
  cases s; cases t
  congr

def copy (s : ConstSec U x Z la δ) (h : la = la') (h' : δ = δ') : ConstSec U x Z la' δ' :=
  { s with
    sig_mem := h ▸ s.sig_mem, inv_mem := h ▸ s.inv_mem, norm_inf := h ▸ s.norm_inf, val_fin := h' ▸ s.val_fin }

variable (x) in

def one (h : HasPts U Z) : ConstSec U x Z 0 0 where
  sig := idem Z
  inv := idem Z
  sig_mem := exOf_zero (Dw := Dw) ▸ idem_mem_secZ Z
  inv_mem := by rw [exOf_zero, neg_zero]; exact idem_mem_secZ Z
  idem_sig := idem_mul_idem Z
  idem_inv := idem_mul_idem Z
  mul_inv := idem_mul_idem Z
  cInf := 1
  cInf_pos _ := one_pos
  norm_inf σ := image_eq_singleton_iff.2 ⟨(h.1 σ).1, fun z hz => by
    rw [wtOf_zero]; exact homN_idem _ x hz.1 hz.2 ((h.1 σ).2 z hz _)⟩
  rho_vw := 0
  val_fin w := image_eq_singleton_iff.2 ⟨h.2 w, fun v hv => by simp [val_idem hv]⟩
  finite_rho := by simp

def smul (a : c.F) (ha : a ≠ 0) (s : ConstSec U x Z la δ) : ConstSec U x Z la δ where
  sig := a • s.sig
  inv := a⁻¹ • s.inv
  sig_mem := Submodule.smul_mem _ _ s.sig_mem
  inv_mem := Submodule.smul_mem _ _ s.inv_mem
  idem_sig := by rw [mul_smul_comm, s.idem_sig]
  idem_inv := by rw [mul_smul_comm, s.idem_inv]
  mul_inv := (smul_mul_inv_smul ha _ _).trans s.mul_inv
  cInf := (fun σ => ‖σ a‖) * s.cInf
  cInf_pos σ := mul_pos (norm_pos_iff.2 ((map_ne_zero σ).2 ha)) (s.cInf_pos σ)
  norm_inf σ := image_eq_singleton_iff.2 ⟨(s.hasPts.1 σ).1, fun z hz => by
    rw [homN_smul, s.homN_eq hz, norm_goodOf]; rfl⟩
  rho_vw := (fun w => (vAdd w a : ℝ)) + s.rho_vw
  val_fin w := image_eq_singleton_iff.2 ⟨s.hasPts.2 w, fun v hv => by
    rw [(isVal_valOn hv).smul _ _ ha, s.val_eq hv, ← EReal.coe_add, add_left_comm]; rfl⟩
  finite_rho := ((finite_vAdd ha).union s.finite_rho).subset (Function.support_add _ _)

def mul (s : ConstSec U x Z la δ) (t : ConstSec U x Z la' δ') : ConstSec U x Z (la + la') (δ + δ') where
  sig := s.sig * t.sig
  inv := s.inv * t.inv
  sig_mem := exOf_add' la la' ▸ mul_mem_secZ s.sig_mem t.sig_mem
  inv_mem := by rw [exOf_add', neg_add]; exact mul_mem_secZ s.inv_mem t.inv_mem
  idem_sig := by rw [← mul_assoc, s.idem_sig]
  idem_inv := by rw [← mul_assoc, s.idem_inv]
  mul_inv := by rw [mul_mul_mul_comm, s.mul_inv, t.mul_inv, idem_mul_idem]
  cInf := s.cInf * t.cInf
  cInf_pos σ := mul_pos (s.cInf_pos σ) (t.cInf_pos σ)
  norm_inf σ := image_eq_singleton_iff.2 ⟨(s.hasPts.1 σ).1, fun z hz => by
    rw [wtOf_add', t.homN_mul_sig (even_wtOf _ _) _ hz, s.homN_eq hz]; rfl⟩
  rho_vw := s.rho_vw + t.rho_vw
  val_fin w := image_eq_singleton_iff.2 ⟨s.hasPts.2 w, fun v hv => by
    rw [t.val_mul_sig _ hv, s.val_eq hv, ← EReal.coe_add, add_add_add_comm]; rfl⟩
  finite_rho := (s.finite_rho.union t.finite_rho).subset (Function.support_add _ _)

def symm (s : ConstSec U x Z la δ) : ConstSec U x Z (-la) (-δ) where
  sig := s.inv
  inv := s.sig
  sig_mem := exOf_neg la ▸ s.inv_mem
  inv_mem := by rw [exOf_neg, neg_neg]; exact s.sig_mem
  idem_sig := s.idem_inv
  idem_inv := s.idem_sig
  mul_inv := by rw [mul_comm, s.mul_inv]
  cInf := s.cInf⁻¹
  cInf_pos σ := inv_pos.2 (s.cInf_pos σ)
  norm_inf σ := image_eq_singleton_iff.2 ⟨(s.hasPts.1 σ).1, fun z hz => by
    have h := s.homN_mul_sig (even_wtOf (-la) 0) s.inv hz
    rw [← wtOf_add', neg_add_cancel, wtOf_zero, mul_comm s.inv, s.mul_inv,
      homN_idem _ x hz.1 hz.2 ((s.hasPts.1 σ).2 z hz _)] at h
    exact eq_inv_of_mul_eq_one_left h.symm⟩
  rho_vw := -s.rho_vw
  val_fin w := image_eq_singleton_iff.2 ⟨s.hasPts.2 w, fun v hv => by
    have h := s.val_mul_sig s.inv hv
    rw [mul_comm s.inv, s.mul_inv, val_idem hv] at h
    have hb := (isVal_valOn hv).ne_bot s.inv
    have ht : v s.inv ≠ ⊤ := fun h' => by rw [h', EReal.top_add_coe] at h; exact EReal.zero_ne_top h
    show v s.inv = _
    lift v s.inv to ℝ using ⟨ht, hb⟩ with b
    rw [← EReal.coe_add, ← EReal.coe_zero, EReal.coe_eq_coe_iff] at h
    rw [EReal.coe_eq_coe_iff, Pi.neg_apply, Pi.neg_apply]
    linarith⟩
  finite_rho := by simpa using s.finite_rho

def relat (s : ConstSec U x Z la δ) (δ' : HeightOneSpectrum (𝓞 c.F) → ℝ) (h : (Function.support (δ - δ')).Finite) :
    ConstSec U x Z la δ' :=
  { s with
    rho_vw := (δ - δ') + s.rho_vw
    val_fin := fun w => (s.val_fin w).trans (by simp only [Pi.add_apply, Pi.sub_apply]; congr 2; ring)
    finite_rho := (h.union s.finite_rho).subset (Function.support_add _ _) }

theorem deg_one (h : HasPts U Z) : (one x h).deg = 0 := lineDeg_one

theorem deg_smul (a : c.F) (ha : a ≠ 0) (s : ConstSec U x Z la δ) : (s.smul a ha).deg = s.deg :=
  (lineDeg_mul (fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 ha)) s.cInf_pos (finite_vAdd ha) s.finite_rho).trans
    (by rw [lineDeg_num ha, zero_add]; rfl)

theorem deg_mul (s : ConstSec U x Z la δ) (t : ConstSec U x Z la' δ') : (s.mul t).deg = s.deg + t.deg :=
  lineDeg_mul s.cInf_pos t.cInf_pos s.finite_rho t.finite_rho

theorem deg_symm (s : ConstSec U x Z la δ) : s.symm.deg = -s.deg := lineDeg_inv _ _

theorem deg_relat (s : ConstSec U x Z la δ) (δ' : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (h : (Function.support (δ - δ')).Finite) : (s.relat δ' h).deg = s.deg + ∑ᶠ w, (δ w - δ' w) * lw c.F w := by
  have := lineDeg_mul (r := 1) (fun _ => one_pos) s.cInf_pos h s.finite_rho
  rw [one_mul] at this
  refine this.trans ?_
  simp [lineDeg, deg, add_comm]

section Prod

variable {ι : Type} {lb : ι → Weight Dw} {ε : ι → HeightOneSpectrum (𝓞 c.F) → ℝ}

theorem exists_prod (h : HasPts U Z) (T : Finset ι) (s : ∀ i, ConstSec U x Z (lb i) (ε i)) :
    ∃ t : ConstSec U x Z (∑ i ∈ T, lb i) (∑ i ∈ T, ε i), t.sig = idem Z * ∏ i ∈ T, (s i).sig ∧
      t.inv = idem Z * ∏ i ∈ T, (s i).inv ∧ t.cInf = ∏ i ∈ T, (s i).cInf ∧ t.rho_vw = ∑ i ∈ T, (s i).rho_vw ∧
      t.deg = ∑ i ∈ T, (s i).deg := by
  induction T using Finset.cons_induction with
  | empty => exact ⟨one x h, by simp [one], by simp [one], rfl, rfl, deg_one h⟩
  | cons i T hi ih =>
    obtain ⟨t, h1, h2, h3, h4, h5⟩ := ih
    refine ⟨((s i).mul t).copy (Finset.sum_cons hi).symm (Finset.sum_cons hi).symm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.prod_cons, mul_left_comm, ← h1]; rfl
    · rw [Finset.prod_cons, mul_left_comm, ← h2]; rfl
    · rw [Finset.prod_cons, ← h3]; rfl
    · exact (congrArg ((s i).rho_vw + ·) h4).trans (Finset.sum_cons (f := fun i => (s i).rho_vw) hi).symm
    · exact (deg_mul _ _).trans ((congrArg ((s i).deg + ·) h5).trans
        (Finset.sum_cons (f := fun i => (s i).deg) hi).symm)

def prod (h : HasPts U Z) (T : Finset ι) (s : ∀ i, ConstSec U x Z (lb i) (ε i)) :
    ConstSec U x Z (∑ i ∈ T, lb i) (∑ i ∈ T, ε i) := (exists_prod h T s).choose

theorem prod_spec (h : HasPts U Z) (T : Finset ι) (s : ∀ i, ConstSec U x Z (lb i) (ε i)) :
    (prod h T s).sig = idem Z * ∏ i ∈ T, (s i).sig ∧ (prod h T s).inv = idem Z * ∏ i ∈ T, (s i).inv ∧
      (prod h T s).cInf = ∏ i ∈ T, (s i).cInf ∧ (prod h T s).rho_vw = ∑ i ∈ T, (s i).rho_vw ∧
      (prod h T s).deg = ∑ i ∈ T, (s i).deg := (exists_prod h T s).choose_spec

end Prod

theorem sum_range_toNat {A : Type} [AddCommGroup A] (a : A) (n : ℤ) :
    ∑ _i ∈ Finset.range n.toNat, a + ∑ _i ∈ Finset.range (-n).toNat, -a = n • a := by
  rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range, smul_neg, ← sub_eq_add_neg,
    ← natCast_zsmul, ← natCast_zsmul, ← sub_smul, Int.toNat_sub_toNat_neg]

def zpow (s : ConstSec U x Z la δ) (n : ℤ) : ConstSec U x Z (n • la) (n • δ) :=
  ((prod s.hasPts (Finset.range n.toNat) fun _ => s).mul
    (prod s.hasPts (Finset.range (-n).toNat) fun _ => s.symm)).copy (sum_range_toNat la n) (sum_range_toNat δ n)

theorem zpow_spec (s : ConstSec U x Z la δ) (n : ℤ) :
    (s.zpow n).sig = idem Z * (s.sig ^ n.toNat * s.inv ^ (-n).toNat) ∧ (∀ σ, (s.zpow n).cInf σ = s.cInf σ ^ n) ∧
      (s.zpow n).rho_vw = n • s.rho_vw ∧ (s.zpow n).deg = n * s.deg := by
  obtain ⟨a1, -, a2, a3, a4⟩ := prod_spec s.hasPts (Finset.range n.toNat) fun _ => s
  obtain ⟨b1, -, b2, b3, b4⟩ := prod_spec s.hasPts (Finset.range (-n).toNat) fun _ => s.symm
  refine ⟨?_, fun σ => ?_, ?_, ?_⟩
  · refine (congrArg₂ (· * ·) a1 b1).trans ?_
    rw [mul_mul_mul_comm, idem_mul_idem]; simp [symm]
  · refine (congrFun (congrArg₂ (· * ·) a2 b2) σ).trans ?_
    simp only [symm, Finset.prod_const, Finset.card_range, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, inv_pow]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (s.cInf_pos σ).ne', ← sub_eq_add_neg,
      Int.toNat_sub_toNat_neg]
  · exact (congrArg₂ (· + ·) a3 b3).trans (sum_range_toNat s.rho_vw n)
  · refine (deg_mul _ _).trans ?_
    rw [a4, b4, deg_symm, sum_range_toNat, zsmul_eq_mul]

end ConstSec

abbrev FlatSec (Z : Comp Xo c) (τ : Psi H) : Type := ConstSec U x Z (flatWt Dw τ) (flDefect_vw Dw c τ)

namespace FlatSec

variable {U x} {Z : Comp Xo c}

def toFrame {τ : Psi H} (s : FlatSec U x Z τ) : ConstSec U x Z (flatWt Dw τ) 0 :=
  s.relat 0 (by simpa using finite_flDefect_vw τ)

theorem deg_eq_toFrame {τ : Psi H} (s : FlatSec U x Z τ) :
    s.deg = s.toFrame.deg + Dw.q * (Real.log H.d - lrd E) := by
  rw [toFrame, ConstSec.deg_relat]
  simp only [Pi.zero_apply, sub_zero, sum_flDefect_vw]
  ring

theorem rho_rat {τ : Psi H} (s : FlatSec U x Z τ) (w : HeightOneSpectrum (𝓞 c.F)) : ∃ b : ℚ, s.rho_vw w = b := by
  obtain ⟨b, hb⟩ := s.exists_rat w
  refine ⟨b - Dw.q * ((ord_vw w (conjDifferent (embF c τ.1)) : ℚ) - (vAdd w (H.d : c.F) : ℚ)), ?_⟩
  rw [eq_sub_of_add_eq' hb, flDefect_vw]; push_cast; rfl

def shift (h : HasPts U Z) (s : ∀ τ, FlatSec U x Z τ) (w : Psi H → ℤ) :
    ConstSec U x Z (parWt Dw w) (∑ τ, (-w τ) • flDefect_vw Dw c τ) :=
  (ConstSec.prod h Finset.univ fun τ => (s τ).zpow (-w τ)).copy (parWt_eq_sum w).symm rfl

theorem shift_spec (h : HasPts U Z) (s : ∀ τ, FlatSec U x Z τ) (w : Psi H → ℤ) :
    (shift h s w).sig = idem Z * ∏ τ, ((s τ).zpow (-w τ)).sig ∧
      (∀ σ, (shift h s w).cInf σ = ∏ τ, (s τ).cInf σ ^ (-w τ)) ∧
      (∀ v, (shift h s w).rho_vw v = -∑ τ, w τ * (s τ).rho_vw v) ∧
      (shift h s w).deg = ∑ τ, w τ * -(s τ).deg := by
  obtain ⟨a1, -, a2, a3, a4⟩ := ConstSec.prod_spec h Finset.univ fun τ => (s τ).zpow (-w τ)
  refine ⟨a1, fun σ => (congrFun a2 σ).trans ?_, fun v => (congrFun a3 v).trans ?_, a4.trans ?_⟩
  · simp only [Finset.prod_apply, (ConstSec.zpow_spec _ _).2.1]
  · simp [Finset.sum_apply, (ConstSec.zpow_spec _ _).2.2.1]
  · simp [(ConstSec.zpow_spec _ _).2.2.2]

end FlatSec

open Classical in

def degFlat (Z : Comp Xo c) (τ : Psi H) : ℝ := if h : Nonempty (FlatSec U x Z τ) then h.some.deg else 0

def c1 (τ : Psi H) : ℝ := -(∑ᶠ Z : Comp Xo c, degFlat U x Z τ) / (Nat.card (Comp Xo c) : ℝ)

def FlatExistsAt (a : ℝ) : Prop :=
  ∀ (Z : Comp Xo c) (τ : Psi H), Nonempty (FlatSec U x Z τ) ∧ ∀ s : FlatSec U x Z τ, s.deg = -a

def FlatExists : Prop := ∃ a, FlatExistsAt U x a

def flatDegVal (Dw : Datum H) (logOm : ℝ) : ℝ :=
  ((Dw.p : ℝ) - Dw.q) / 2 * logOm + Dw.q * (Real.log H.d - lrd E)

def FlatDegree (logOm : ℝ) : Prop := FlatExistsAt U x (-flatDegVal Dw logOm)

variable {U x}

theorem FlatExistsAt.degFlat_eq {a : ℝ} (h : FlatExistsAt U x a) (Z : Comp Xo c) (τ : Psi H) :
    degFlat U x Z τ = -a := by
  rw [degFlat, dif_pos (h Z τ).1, (h Z τ).2]

theorem FlatExistsAt.c1_eq {a : ℝ} (h : FlatExistsAt U x a) (hne : CompNe Xo c) (τ : Psi H) : c1 U x τ = a := by
  haveI := CompFin.finite_comp Xo c
  haveI : Nonempty (Comp Xo c) := hne
  haveI := Fintype.ofFinite (Comp Xo c)
  have hc : (Fintype.card (Comp Xo c) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [c1, h.degFlat_eq, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]
  field_simp

theorem FlatExists.deg_eq (h : FlatExists U x) {Z : Comp Xo c} {τ : Psi H} (s : FlatSec U x Z τ) (τ' : Psi H) :
    s.deg = -c1 U x τ' := by
  obtain ⟨a, ha⟩ := h
  rw [ha.c1_eq ⟨Z⟩, (ha Z τ).2]

theorem FlatExists.nonempty (h : FlatExists U x) (Z : Comp Xo c) (τ : Psi H) : Nonempty (FlatSec U x Z τ) :=
  (h.choose_spec Z τ).1

theorem FlatExists.sum_log_eq (h : FlatExists U x) {Z : Comp Xo c} {τ : Psi H} (s : FlatSec U x Z τ) :
    ((∑ᶠ w, Real.log (s.cFin w)) + ∑ σ, Real.log (s.cInf σ)) / (finrank ℚ c.F : ℝ) = c1 U x τ := by
  rw [s.sum_log_eq, h.deg_eq s τ, neg_neg]

theorem FlatExists.deg_shift (h : FlatExists U x) {Z : Comp Xo c} (hp : HasPts U Z) (s : ∀ τ, FlatSec U x Z τ)
    (w : Psi H → ℤ) : (FlatSec.shift hp s w).deg = ∑ τ, w τ * c1 U x τ := by
  rw [(FlatSec.shift_spec hp s w).2.2.2]
  exact Finset.sum_congr rfl fun τ _ => by rw [h.deg_eq (s τ) τ, neg_neg]

theorem FlatDegree.c1_eq {logOm : ℝ} (h : FlatDegree U x logOm) (hne : CompNe Xo c) (τ : Psi H) :
    c1 U x τ = -(((Dw.p : ℝ) - Dw.q) / 2 * logOm) - Dw.q * (Real.log H.d - lrd E) := by
  rw [FlatExistsAt.c1_eq h hne, flatDegVal]; ring

theorem FlatDegree.flatExists {logOm : ℝ} (h : FlatDegree U x logOm) : FlatExists U x := ⟨_, h⟩

example (hq : Dw.q = 0) (τ : Psi H) : flDefect_vw Dw c τ = 0 := by
  funext w; simp [flDefect_vw, hq]

variable (x) in

theorem exists_flatSec_rank_zero (hp : Dw.p = 0) (hq : Dw.q = 0) {Z : Comp Xo c} (h : HasPts U Z) (τ : Psi H)
    {a : c.F} (ha : a ≠ 0) : ∃ s : FlatSec U x Z τ, s.sig = a • idem Z ∧ (∀ σ, s.cInf σ = ‖σ a‖) ∧
      (∀ w, s.rho_vw w = vAdd w a) ∧ s.deg = 0 :=
  ⟨((ConstSec.one x h).smul a ha).copy (funext fun _ => funext fun i => by have := i.2; omega)
      (funext fun w => by simp [flDefect_vw, hq]), rfl, fun σ => mul_one _, fun w => add_zero _,
    (ConstSec.deg_smul a ha _).trans (ConstSec.deg_one h)⟩

example {Z : Comp Xo c} {la : Weight Dw} (s : ConstSec U x Z la 0) (w : HeightOneSpectrum (𝓞 c.F))
    (h : (Function.support (0 - fun v => open Classical in if v = w then (1 : ℝ) else 0)).Finite) :
    (s.relat _ h).deg = s.deg - lw c.F w := by
  rw [ConstSec.deg_relat, finsum_eq_single _ w fun v hv => by simp [hv]]
  simp [sub_eq_add_neg]

end GlobalTheory.FlatLine
