import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyRingHomComplexOfLeContinuum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingHomOfIsIntegral

noncomputable section

namespace GlobalTheory.Mem.GaloisStage

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open scoped Pointwise

theorem finite_placesOver (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem nonempty_lData (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [hl : Fact l.Prime] : Nonempty (Formalism.GaloisCohomology.LData F Ω l) := by
  have hfin := finite_placesOver F hl.out.ne_zero
  have hun : UnramOutside (hfin.toFinset : Set (HeightOneSpectrum (𝓞 F))) (cycZ F Ω l) := by
    rw [unramOutside_iff _ _ (continuous_cycZ F Ω l)]
    intro v hv A hA σ hσ
    have hv' : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal := by simpa [placesOver] using hv
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hv' hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  exact ⟨⟨hfin.toFinset, hfin.coe_toFinset, fun v => placeOf Ω v.1, fun v => isPlaceOver_placeOf Ω v.1,
    QuotientGroup.lift _ (cycZ F Ω l) hun, MonoidHom.ext fun _ => rfl⟩⟩

theorem isAlgebraic_rat (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    [CharZero Ω] : Algebra.IsAlgebraic ℚ Ω :=
  Algebra.IsAlgebraic.trans ℚ F Ω

variable {R : Ranks}

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_isCMConjOm (H : Host R) (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] :
    ∃ c : Ω ≃+* Ω, IsCMConjOm H.E Ω c := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap H.E Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed H.E
  have : Algebra.IsAlgebraic ℚ Ω := isAlgebraic_rat H.E Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := {}
  let j : Ω →+* ℂ := (IsAlgClosed.lift : Ω →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) j
    ((starRingEnd ℂ).comp j) (Subsingleton.elim _ _)
  have h : ∀ x, j (σ.symm x) = starRingEnd ℂ (j x) := fun x => RingHom.congr_fun hσ x
  refine ⟨σ.symm.toRingEquiv, ⟨j, h⟩, fun x => ⟨H.conj x, j.injective ?_⟩⟩
  exact (h _).trans (H.conjE_apply (j.comp (algebraMap H.E Ω)) x).symm

theorem conj_mul_conj (H : Host R) : H.conj * H.conj = 1 := by
  ext1 x
  apply H.φ₀.injective
  rw [AlgEquiv.mul_apply, H.conjE_apply, H.conjE_apply, Complex.conj_conj]
  rfl

theorem conj_ne_one (H : Host R) : H.conj ≠ 1 := by
  intro h
  have h1 := H.conjE_apply H.φ₀ H.sqrtMinusD
  have h2 : H.φ₀ H.sqrtMinusD ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, Host.sqrtMinusD, H.sqd_sq]
    simp
  have h3 : H.φ₀ H.sqrtMinusD = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) := by
    rw [← h1]
    exact congrArg H.φ₀ (AlgEquiv.congr_fun h H.sqrtMinusD).symm
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h3.symm
  rw [hr] at h2
  have h4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h2
  have h5 : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  nlinarith [sq_nonneg r]

theorem exists_transversal {S : Type} [Fintype S] (c : S → S) (hc : ∀ x, c (c x) = x) (hne : ∀ x, c x ≠ x)
    {n : ℕ} (hn : Fintype.card S = 2 * n) :
    ∃ e : Fin n → S, Function.Injective e ∧ ∀ i j, c (e i) ≠ e j := by
  classical
  letI : LinearOrder S := LinearOrder.lift' (Fintype.equivFin S) (Fintype.equivFin S).injective
  let T : Finset S := Finset.univ.filter fun x => x < c x
  have h1 : T.card = Tᶜ.card := by
    refine Finset.card_bij (fun x _ => c x) ?_ ?_ ?_
    · intro x hx
      simp only [T, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, hc] at hx ⊢
      exact not_lt.2 hx.le
    · intro x _ y _ h
      rw [← hc x, h, hc]
    · intro y hy
      refine ⟨c y, ?_, hc y⟩
      simp only [T, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, hc] at hy ⊢
      exact lt_of_le_of_ne (not_lt.1 hy) (hne y)
  have h2 := Finset.card_add_card_compl T
  have h3 : T.card = n := by omega
  let e := (T.equivFinOfCardEq h3).symm
  refine ⟨fun i => (e i : S), Subtype.val_injective.comp e.injective, fun i j h => ?_⟩
  have hi : (e i : S) < c (e i) := (Finset.mem_filter.1 (e i).2).2
  have hj : (e j : S) < c (e j) := (Finset.mem_filter.1 (e j).2).2
  have h' : c (e i) = e j := h
  rw [← h', hc] at hj
  exact lt_asymm hi hj

theorem exists_places (H : Host R) {p : ℕ} (hp : p.Prime)
    (hs : (placesOver H.E p).ncard = Module.finrank ℚ H.E) :
    ∃ e : Fin R.f → PlE H, (∀ i, e i ∈ placesOver H.E p) ∧ Function.Injective e ∧
      ∀ i j, ¬ IsConjPl H (e i) (e j) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hG : IsGalois ℚ H.E := H.galois
  have := Formalism.FrobeniusOrbits.SplitK.span_prime p
  have : IsGaloisGroup (H.E ≃ₐ[ℚ] H.E) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  obtain ⟨⟨P, hP1, hP2⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E)))
  have hr : Set.range (fun σ : H.E ≃ₐ[ℚ] H.E => σ • P) = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨inferInstance, inferInstance⟩
    · rintro ⟨hQ1, hQ2⟩
      exact Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (H.E ≃ₐ[ℚ] H.E)
  have hinj : Function.Injective (fun σ : H.E ≃ₐ[ℚ] H.E => σ • P) := by
    rw [GlobalTheory.HostSplit.ncard_placesOver H.E hp, ← hr, ← IsGalois.card_aut_eq_finrank, ← Set.image_univ,
      ← Set.ncard_univ] at hs
    exact Set.injOn_univ.1 (Set.injOn_of_ncard_image_eq hs)
  have hcard : Fintype.card (H.E ≃ₐ[ℚ] H.E) = 2 * R.f := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      H.finrank_cmField, Ranks.f, Ranks.n]
    ring
  obtain ⟨e, he, he'⟩ := exists_transversal (fun σ => H.conj * σ)
    (fun σ => by rw [← mul_assoc, conj_mul_conj, one_mul])
    (fun σ h => conj_ne_one H (mul_eq_right.1 h)) hcard
  refine ⟨fun i => ⟨e i • P, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 _⟩, fun i => ?_,
    fun i j h => he (hinj (congrArg HeightOneSpectrum.asIdeal h)), fun i j h => he' i j (hinj ?_)⟩
  · have h3 : (p : ℤ) ∈ (e i • P).under ℤ := by
      rw [← Ideal.over_def (e i • P) (Ideal.span {(p : ℤ)})]
      exact Ideal.mem_span_singleton_self _
    have h4 : algebraMap ℤ (𝓞 H.E) ((p : ℕ) : ℤ) ∈ e i • P := h3
    rw [map_natCast] at h4
    exact h4
  · ext y
    show y ∈ (H.conj * e i) • P ↔ y ∈ e j • P
    have := h (H.conj⁻¹ • y) y (by
      rw [← Formalism.TwoAdicCyclotomicDecomposition.odd_coe_smul, smul_inv_smul])
    rw [mul_smul, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact this

theorem finrank_K (H : Host R) : Module.finrank ℚ H.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)

theorem discr_K (H : Host R) : NumberField.discr H.K = -(H.d : ℤ) :=
  discr_eq_neg_of_sq_eq (finrank_K H) H.hyp.2.1.squarefree (by have := H.hyp.2.2.2.1; omega)
    (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))

theorem split_K (H : Host R) {p : ℕ} (hp : p.Prime) (hc : p % (H.QS * H.q * H.d) = 1) :
    (placesOver H.K p).ncard = Module.finrank ℚ H.K := by
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hmod : ∀ m : ℕ, 1 < m → m ∣ H.QS * H.q * H.d → p % m = 1 := by
    intro m hm hdv
    rw [← Nat.mod_mod_of_dvd p hdv, hc]
    exact Nat.mod_eq_of_lt hm
  have h4 : p % 4 = 1 := hmod 4 (by norm_num)
    ((((pow_dvd_pow 2 (Nat.le_add_left 2 R.e)).trans H.tower_dvd).mul_right _).mul_right _)
  have hd : p % H.d = 1 := hmod _ (by omega) (dvd_mul_left _ _)
  rw [finrank_K, GlobalTheory.HostSplit.ncard_placesOver H.K hp]
  exact (Formalism.FrobeniusOrbits.SplitK.clause H.hyp.2.1 (by omega) (H.sqd_sq) p hp).2
    (Or.inr ⟨by omega, GlobalTheory.HostSplit.jacobiSym_neg_eq_one (by omega) h4 hd⟩)

theorem exists_teichC (g : ℕ) [Fact g.Prime] : ∃ t : Formalism.CyclotomicNorms.Fbar g →* ℂ,
    ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y := by
  obtain ⟨j⟩ := GlobalTheory.WittFracComplex.nonempty_ringHom_complex g
  let W := WittVector g (AlgebraicClosure (ZMod g))
  let i : W →+* FractionRing W := algebraMap W (FractionRing W)
  have j' : FractionRing W →+* ℂ := j
  refine ⟨(j'.comp i).toMonoidHom.comp (WittVector.teichmuller g), fun x y _ _ h => ?_⟩
  have h1 : j' (i (WittVector.teichmuller g x)) = j' (i (WittVector.teichmuller g y)) := h
  have h2 := IsFractionRing.injective W (FractionRing W) (j'.injective h1)
  have h3 := congrArg (fun w : W => w.coeff 0) h2
  simpa using h3

theorem isOfFinOrder_fbar (g : ℕ) [Fact g.Prime] {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) : IsOfFinOrder x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have := IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 : IsOfFinOrder (Units.mk0 y hy) := isOfFinOrder_of_finite _
  exact ((IntermediateField.adjoin (ZMod g) {x}).val.toMonoidHom.comp (Units.coeHom _)).isOfFinOrder h1

theorem nonempty_reduction (l : ℕ) [hl : Fact l.Prime] :
    Nonempty (integralClosure ℤ ℂ →+* Formalism.CyclotomicNorms.Fbar l) :=
  _root_.GlobalTheory.RingHomOfIsIntegral.nonempty_ringHom l

theorem exists_iota (g l : ℕ) [Fact g.Prime] [hl : Fact l.Prime] : ∃ ι : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar l,
    ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime l → (orderOf y).Coprime l →
      ι x = ι y → x = y := by
  obtain ⟨t, ht⟩ := exists_teichC g
  obtain ⟨ρ⟩ := nonempty_reduction l
  have hint : ∀ x, t x ∈ integralClosure ℤ ℂ := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · have h : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
      rcases eq_or_ne (t 0) 0 with h0 | h0
      · rw [h0]; exact zero_mem _
      · rw [(mul_eq_left₀ h0).1 h]; exact one_mem _
    · refine IsIntegral.of_pow (isOfFinOrder_fbar g hx).orderOf_pos ?_
      rw [← map_pow, pow_orderOf_eq_one, map_one]
      exact isIntegral_one
  let t' : Formalism.CyclotomicNorms.Fbar g →* integralClosure ℤ ℂ := t.codRestrict (integralClosure ℤ ℂ) hint
  refine ⟨ρ.toMonoidHom.comp t', fun x y hx hy cx cy h => ?_⟩
  have hz : x * y⁻¹ ≠ 0 := mul_ne_zero hx (inv_ne_zero hy)
  set n := orderOf (x * y⁻¹) with hn
  have hnpos : 0 < n := (isOfFinOrder_fbar g hz).orderOf_pos
  have hcop : n.Coprime l := by
    refine Nat.Coprime.coprime_dvd_left ?_ (Nat.Coprime.mul_left cx cy)
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [mul_pow, inv_pow, pow_mul, pow_orderOf_eq_one, mul_comm (orderOf x), pow_mul, pow_orderOf_eq_one]
    simp
  have hprim : IsPrimitiveRoot (t' (x * y⁻¹)) n := by
    refine ⟨by rw [← map_pow, hn, pow_orderOf_eq_one, map_one], fun m hm => orderOf_dvd_of_pow_eq_one ?_⟩
    refine ht _ _ (pow_ne_zero _ hz) one_ne_zero ?_
    rw [map_pow, map_one]
    exact congrArg Subtype.val hm
  have : NeZero ((n : ℕ) : Formalism.CyclotomicNorms.Fbar l) := ⟨fun h0 =>
    (Nat.Prime.coprime_iff_not_dvd hl.out).1 hcop.symm ((CharP.cast_eq_zero_iff _ l n).1 h0)⟩
  have h1 : ρ (t' (x * y⁻¹)) = 1 := by
    have h2 : ρ (t' x) = ρ (t' y) := h
    rw [map_mul, map_mul, h2, ← map_mul, ← map_mul, mul_inv_cancel₀ hy, map_one, map_one]
  have h3 : IsPrimitiveRoot (1 : Formalism.CyclotomicNorms.Fbar l) n := by
    rw [← isRoot_cyclotomic_iff, ← h1, ← map_cyclotomic n ρ]
    exact (hprim.isRoot_cyclotomic hnpos).map
  have h4 : n = 1 := h3.unique IsPrimitiveRoot.one
  exact (mul_inv_eq_one₀ hy).1 (orderOf_eq_one_iff.1 h4)

section Records

variable {H : Host R} {what₂ : Rows.Data R}

theorem two_le_r (R : Ranks) : 2 ≤ R.r := by
  have := R.two_le_m
  have := R.m_add_three_le_k
  unfold Ranks.r
  omega

theorem f_pos (R : Ranks) : 0 < R.f := by
  unfold Ranks.f Ranks.n
  positivity

def lData (H : Host R) (p : ℕ) [Fact p.Prime] : Formalism.GaloisCohomology.LData H.E (AlgebraicClosure H.E) p :=
  (nonempty_lData H.E (AlgebraicClosure H.E) p).some

def shaTrue (H : Host R) (p e : ℕ) : ℚ :=
  if hp : p.Prime then haveI : Fact p.Prime := ⟨hp⟩; ((Formalism.GaloisCohomology.shaLen (lData H p) (e : ℤ)).toNat : ℚ) else 0

theorem shaTrue_nonneg (H : Host R) (p e : ℕ) : 0 ≤ shaTrue H p e := by
  unfold shaTrue
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_rfl

theorem monic_unip {K : Type} [CommRing K] [Nontrivial K] (n : ℕ) :
    ((X - 1 : K[X]) ^ n).Monic ∧ ((X - 1 : K[X]) ^ n).natDegree = n := by
  have h : (X - 1 : K[X]).Monic := by simpa using monic_X_sub_C (1 : K)
  have h' : (X - 1 : K[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : K)
  exact ⟨h.pow n, by rw [h.natDegree_pow, h', mul_one]⟩

set_option synthInstance.maxHeartbeats 400000 in

def nData (H : Host R) (what₂ : Rows.Data R) (hsha : ∀ p e, what₂.shaLen p e = shaTrue H p e)
    (hs : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (hc : what₂.restRowsFiniteGroupCard = ∏ k : Fin 2, (Nat.card (GL (Fin R.r) (ZMod (H.g k)))) ^ R.f) : NData R H what₂ where
  Om := AlgebraicClosure H.E
  plOm := ⟨placeOf _, isPlaceOver_placeOf _⟩
  ldat := lData H
  sha_eq := fun p hp e _ _ n h => by
    rw [hsha, shaTrue, dif_pos hp.out]
    show ((Formalism.GaloisCohomology.shaLen (lData H p) (e : ℤ)).toNat : ℚ) = n
    rw [h, ENat.toNat_natCast]
  Loc := Empty
  locs := fun _ _ => ∅
  locs_mem := fun _ _ i => i.elim
  g_split := hs
  PlG := fun _ => Fin R.f
  card_PlG := fun _ => Fintype.card_fin _
  lab := fun _ _ _ => (X - 1) ^ R.r
  lab_monic := fun k _ _ => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; monic_unip _
  chiT := fun _ _ _ => 1
  restN_card_levelGroup_eq := hc
  l := fun i => i.elim
  lPrime := fun i => i.elim
  j := fun i => i.elim
  j_range := fun i => i.elim
  mu := fun i => i.elim
  w := fun i => i.elim
  w_l := fun i => i.elim
  mu_w := fun i => i.elim
  w_tw := fun i => i.elim
  O := fun i => i.elim
  instO := fun i => i.elim
  domO := fun i => i.elim
  dvrO := fun i => i.elim
  algO := fun i => i.elim
  finO := fun i => i.elim
  topO := fun i => i.elim
  trO := fun i => i.elim
  O_adic := fun i => i.elim
  O_complete := fun i => i.elim
  embK := fun i => i.elim
  embK_w := fun i => i.elim
  X := fun i => i.elim
  finX := fun i => i.elim
  neX := fun i => i.elim
  T := fun i => i.elim
  T_local := fun i => i.elim
  T_sep := fun i => i.elim
  Mt := fun i => i.elim
  acgMt := fun i => i.elim
  modMt := fun i => i.elim
  freeMt := fun i => i.elim
  finMt := fun i => i.elim
  act := fun i => i.elim
  act_inj := fun i => i.elim
  prMt := fun i => i.elim
  prMt_span := fun i => i.elim
  prMt_lat := fun i => i.elim
  eig_ne := fun i => i.elim
  chi := fun i => i.elim
  chi_cont := fun i => i.elim
  chi_def := fun i => i.elim
  Z := fun i => i.elim
  Zgood := fun i => i.elim
  s0 := fun i => i.elim
  restNLevelExponent_of_odd := fun i => i.elim
  restNLevelExponent_of_two := fun i => i.elim
  S := fun i => i.elim
  Q := fun i => i.elim
  SQ_split := fun i => i.elim
  SQ_disj := fun i => i.elim
  SQ_l := fun i => i.elim
  S_def := fun i => i.elim
  hT := fun i => i.elim
  T_gen := fun i => i.elim
  gam0 := fun i => i.elim
  locNd_chebotarevPlace_mem := fun i => i.elim
  restN_tameGenerator_generates := fun i => i.elim
  chi_ram_Q := fun i => i.elim
  Bj := fun i => i.elim
  acgBj := fun i => i.elim
  modBj := fun i => i.elim
  freeBj := fun i => i.elim
  finBj := fun i => i.elim

abbrev UnrPar : Type := {m : Multiset ℂ // (0 : ℂ) ∉ m}

def UnrPar.scale (a : UnrPar) (c : ℂ) (hc : c ≠ 0) : UnrPar :=
  ⟨a.1.map (· * c), fun h => by
    obtain ⟨x, hx, h0⟩ := Multiset.mem_map.1 h
    exact a.2 ((mul_eq_zero.1 h0).resolve_right hc ▸ hx)⟩

def UnrPar.add (a b : UnrPar) : UnrPar :=
  ⟨a.1 + b.1, fun h => (Multiset.mem_add.1 h).elim a.2 b.2⟩

theorem normV_cpow_ne_zero (w : PlE H) (s : ℂ) : ((normV w : ℕ) : ℂ) ^ s ≠ 0 := by
  have : Finite (𝓞 H.E ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  have h : normV w ≠ 0 := Nat.card_pos.ne'
  exact fun h0 => h (by exact_mod_cast ((Complex.cpow_eq_zero_iff _ _).1 h0).1)

theorem normV_ne_zero (w : PlE H) : ((normV w : ℕ) : ℂ) ≠ 0 := by
  simpa using normV_cpow_ne_zero w 1

abbrev UnrFam (H : Host R) (a : ℕ) : Type :=
  {p : (PlE H → UnrPar) × ((H.E →+* ℂ) → Multiset ℂ) //
    (∀ w, Multiset.card (p.1 w).1 = a) ∧ ∀ τ, Multiset.card (p.2 τ) = a}

def negOneFam (H : Host R) : UnrFam H 1 :=
  ⟨(fun _ => ⟨{-1}, by simp⟩, fun _ => {0}), fun _ => rfl, fun _ => rfl⟩

set_option synthInstance.maxHeartbeats 400000 in

def nAut (N : NData R H what₂) [IsEmpty N.Loc] (pl : ∀ k, N.PlG k → PlE H)
    (h1 : ∀ k v, pl k v ∈ placesOver H.E (H.g k)) (h2 : ∀ k, Function.Injective (pl k))
    (h3 : ∀ k v v', ¬ IsConjPl H (pl k v) (pl k v')) : NAut N where
  LP := fun _ => UnrPar
  lpDim := fun a => Multiset.card a.1
  lpZero := fun _ => ⟨0, by simp⟩
  lpSum := UnrPar.add
  lpTw := fun {w} a s => a.scale (((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) (normV_cpow_ne_zero w _)
  lpChar := fun a χ => a.scale χ.1.prod (Multiset.prod_ne_zero χ.2)
  lpUnr := fun _ m => open Classical in ⟨m.filter (· ≠ 0), by simp⟩
  mono0 := fun _ => True
  unr := fun _ => True
  frobEig := fun a => a.1
  tempered := fun a => ∀ α ∈ a.1, ‖α‖ = 1
  inePol := fun a _ => (X - 1) ^ Multiset.card a.1
  items₂ := fun _ _ a => (X - 1) ^ Multiset.card a.1
  lpDim_zero := fun _ => rfl
  lpDim_sum := fun a b => Multiset.card_add _ _
  lpDim_tw := fun a s => Multiset.card_map _ _
  lpUnr_spec := fun _ m hm => by
    classical
    have h : m.filter (· ≠ 0) = m := Multiset.filter_eq_self.2 fun x hx h0 => hm (h0 ▸ hx)
    exact ⟨trivial, h, congrArg Multiset.card h⟩
  unr_sum := fun _ _ => by simp
  monomial_sum_iff := fun _ _ => by simp
  frobEig_sum := fun _ _ _ _ => rfl
  unr_tw := fun _ _ => Iff.rfl
  monomial_twist_iff := fun _ _ => Iff.rfl
  frobEig_tw := fun _ _ _ => rfl
  frobEig_char := fun a χ c _ _ _ h => by
    show a.1.map (· * χ.1.prod) = _
    rw [show χ.1 = {c} from h, Multiset.prod_singleton]
  lpDim_char := fun _ _ _ => Multiset.card_map _ _
  unr_char := fun _ _ _ _ _ => trivial
  monomial_char_iff := fun _ _ _ => Iff.rfl
  lpZero_unr := fun _ => trivial
  frobEig_zero := fun _ => rfl
  lpSum_zero := fun a => Subtype.ext (add_zero a.1)
  lpSum_comm := fun a b => Subtype.ext (add_comm a.1 b.1)
  lpSum_assoc := fun a b c => Subtype.ext (add_assoc a.1 b.1 c.1)
  lpTw_zero := fun a => Subtype.ext (by simp [UnrPar.scale])
  lpTw_add := fun {w} a s t => Subtype.ext (by
    simp [UnrPar.scale, Complex.cpow_add _ _ (normV_ne_zero w), mul_assoc])
  lpTw_sum := fun a b s => Subtype.ext (Multiset.map_add _ _ _)
  unr_eq_lpUnr := fun a _ => by
    classical
    have h : a.1.filter (· ≠ 0) = a.1 := Multiset.filter_eq_self.2 fun x hx h0 => a.2 (h0 ▸ hx)
    exact Subtype.ext h.symm
  unr_mono0 := fun _ _ => trivial
  frobEig_ne_zero := fun a _ => a.2
  frobEig_card := fun _ _ => rfl
  tempered_unr := fun _ _ => Iff.rfl
  inePol_sum := fun a b _ => by
    show (X - 1 : ℂ[X]) ^ Multiset.card (a.1 + b.1) = _
    rw [Multiset.card_add, pow_add]
  inePol_tw := fun a s _ _ => by
    show (X - 1 : ℂ[X]) ^ Multiset.card (a.1.map _) = _
    rw [Multiset.card_map]
  unr_iff_ine := fun _ => ⟨fun _ => ⟨trivial, fun _ _ => rfl⟩, fun _ => trivial⟩
  inertiaCharpoly_zero := fun _ _ => pow_zero _
  inertiaCharpoly_add := fun k _ a b => by
    show (X - 1 : (ZMod (H.g k))[X]) ^ Multiset.card (a.1 + b.1) = _
    rw [Multiset.card_add, pow_add]
  CG := UnrFam H
  csd := fun π => ∀ w w', IsConjPl H w w' → (π.1.1 w').1 = (π.1.1 w).1.map (·⁻¹)
  ralg := fun {a} π => ∀ τ, (π.1.2 τ).Nodup ∧ ∀ z ∈ π.1.2 τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  locG := fun π w => π.1.1 w
  locG_dim := fun π w => π.2.1 w
  locG_unr_ae := fun _ => Filter.Eventually.of_forall fun _ => trivial
  tw := fun π χ => ⟨(fun w => (π.1.1 w).scale (χ.1.1 w).1.prod (Multiset.prod_ne_zero (χ.1.1 w).2),
    fun τ => (π.1.2 τ).map (· + (χ.1.2 τ).sum)), fun w => (Multiset.card_map _ _).trans (π.2.1 w),
    fun τ => (Multiset.card_map _ _).trans (π.2.2 τ)⟩
  locG_tw := fun _ _ _ => rfl
  infG := fun π τ => π.1.2 τ
  infG_card := fun π τ => π.2.2 τ
  ralg_def := fun _ => Iff.rfl
  infG_tw := fun π χ τ s h => by
    show (π.1.2 τ).map (· + (χ.1.2 τ).sum) = _
    rw [show χ.1.2 τ = {s} from h, Multiset.sum_singleton]
  csd_tw := fun π χ hχ hπ w w' h => by
    show (π.1.1 w').1.map (· * (χ.1.1 w').1.prod) = ((π.1.1 w).1.map (· * (χ.1.1 w).1.prod)).map (·⁻¹)
    rw [hχ w w' h, hπ w w' h, Multiset.prod_map_inv', Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun x _ => (mul_inv _ _).symm
  csd_unr := fun π w w' h hc _ => ⟨trivial, h w w' hc⟩
  etaT := negOneFam H
  etaTinv := negOneFam H
  etaT_unr := fun _ => trivial
  etaT_inert := fun _ _ => rfl
  etaTinv_def := fun _ => ⟨trivial, by simp [negOneFam]⟩
  etaT_split := fun _ _ _ _ a b ha hb => by
    have ha' : (-1 : ℂ) = a := Multiset.singleton_inj.1 ha
    have hb' : (-1 : ℂ) = b := Multiset.singleton_inj.1 hb
    rw [← ha', ← hb']
    norm_num
  plGw := pl
  plGw_over := h1
  plGw_inj := h2
  plGw_nconj := h3
  iotaQ := fun i => isEmptyElim i
  iotaQC := fun i => isEmptyElim i
  iota_LL := fun i => isEmptyElim i
  iotaQ_alg := fun i => isEmptyElim i
  muC := fun i => isEmptyElim i
  muC_csd := fun i => isEmptyElim i
  AV := fun i => isEmptyElim i
  finAV := fun i => isEmptyElim i
  ptV := fun i => isEmptyElim i
  typeV := fun i => isEmptyElim i
  typeV_ne := fun i => isEmptyElim i
  typeV_indep := fun i => isEmptyElim i
  typeV_top := fun i => isEmptyElim i
  pt_surj := fun i => isEmptyElim i
  eig_dim := fun i => isEmptyElim i
  locV := fun i => isEmptyElim i
  satV := fun i => isEmptyElim i
  locV_unr := fun i => isEmptyElim i
  pt_loc := fun i => isEmptyElim i
  infWt := fun i => isEmptyElim i
  locW := fun i => isEmptyElim i
  satW := fun i => isEmptyElim i
  lab_loc := fun i => isEmptyElim i
  wdOf := fun i => isEmptyElim i
  wdOf_dim := fun i => isEmptyElim i
  wdOf_unr := fun i => isEmptyElim i
  wdOf_frob := fun i => isEmptyElim i
  wdOf_ine := fun i => isEmptyElim i
  wdOf_mono0 := fun i => isEmptyElim i
  IsCrysW := fun i => isEmptyElim i
  IsPotCrysW := fun i => isEmptyElim i
  IsdRW := fun i => isEmptyElim i
  jumpsW := fun i => isEmptyElim i
  wdOf_unrL := fun i => isEmptyElim i
  wdOf_mono0L := fun i => isEmptyElim i
  jumpsInf := fun i => isEmptyElim i
  locAutHodgeTateWeightsLevelZero := fun i => isEmptyElim i
  jumpsInf_def := fun i => isEmptyElim i
  locAut_hodgeTateWeightsLevelZero_def := fun i => isEmptyElim i
  chi_mu := fun i => isEmptyElim i
  kFbar := fun i => isEmptyElim i

def nBC {N : NData R H what₂} [IsEmpty N.Loc] (A : NAut N) : NBC A where
  AU := fun _ => Empty
  multAU := fun _ x => x.elim
  sphAU := fun _ x => x.elim
  locAU := fun _ x => x.elim
  satAU := fun _ x => x.elim
  satAU_card := fun _ x => x.elim
  Wt := fun _ => Empty
  infW := fun _ x => x.elim
  infW_card := fun _ x => x.elim
  wtAU := fun _ x => x.elim
  infW_alg := fun _ x => x.elim
  embAV := fun i => isEmptyElim i
  embAV_inj := fun i => isEmptyElim i
  embAV_loc := fun i => isEmptyElim i
  embAV_sat := fun i => isEmptyElim i
  embAV_sph := fun i => isEmptyElim i
  embAV_inf := fun i => isEmptyElim i

section Twist

variable [NumberField what₂.LL] [StarRing what₂.LL] (LL0 : IntermediateField ℚ what₂.LL)

set_option synthInstance.maxHeartbeats 400000 in

def nTw (N : NData R H what₂) [IsEmpty N.Loc] : NTw R H what₂ LL0 N where
  cc := (exists_isCMConjOm H N.Om).choose
  cc_cm := (exists_isCMConjOm H N.Om).choose_spec
  Tw := Empty
  l := fun i => isEmptyElim i
  lPrime := fun i => isEmptyElim i
  O0 := fun i => isEmptyElim i
  crO0 := fun i => isEmptyElim i
  twistBaseCoefficientRing_isDomain := fun i => isEmptyElim i
  twistBaseCoefficientRing_isDVR := fun i => isEmptyElim i
  algO0 := fun i => isEmptyElim i
  twistBaseCoefficientRing_finite_padic := fun i => isEmptyElim i
  twistBaseCoefficientRing_residueField_finite := fun i => isEmptyElim i
  topO0 := fun i => isEmptyElim i
  twistBaseCoefficientRing_topologicalRing := fun i => isEmptyElim i
  twistBaseCoefficientRing_isAdic := fun i => isEmptyElim i
  emb0 := fun i => isEmptyElim i
  emb0b := fun i => isEmptyElim i
  restX_coefficientEmbedding_conj := fun i => isEmptyElim i
  O := fun i => isEmptyElim i
  crO := fun i => isEmptyElim i
  domO := fun i => isEmptyElim i
  dvrO := fun i => isEmptyElim i
  algO := fun i => isEmptyElim i
  O_inj := fun i => isEmptyElim i
  O_l := fun i => isEmptyElim i
  topO := fun i => isEmptyElim i
  trO := fun i => isEmptyElim i
  O_adic := fun i => isEmptyElim i
  resO_ac := fun i => isEmptyElim i
  O_complete := fun i => isEmptyElim i
  Ok := fun i => isEmptyElim i
  crOk := fun i => isEmptyElim i
  domOk := fun i => isEmptyElim i
  dvrOk := fun i => isEmptyElim i
  algOk := fun i => isEmptyElim i
  Ok_inj := fun i => isEmptyElim i
  Ok_fin := fun i => isEmptyElim i
  zk := fun i => isEmptyElim i
  zk_prim := fun i => isEmptyElim i
  Ok_gen := fun i => isEmptyElim i
  pD := fun i => isEmptyElim i
  pD_eq := fun i => isEmptyElim i
  delta := fun i => isEmptyElim i
  delta_open := fun i => isEmptyElim i
  delta_anti := fun i => isEmptyElim i
  delta_ram := fun i => isEmptyElim i
  delta_15 := fun i => isEmptyElim i
  delta_tame := fun i => isEmptyElim i
  chi1 := fun i => isEmptyElim i
  twistCharacterFamily_continuous := fun i => isEmptyElim i
  twistCharacterFamily_unramified := fun i => isEmptyElim i
  twistCharacterFamily_at_auxiliaryPlaces := fun i => isEmptyElim i
  twistCharacterFamily_tame := fun i => isEmptyElim i
  Sig := fun i => isEmptyElim i
  finSig := fun i => isEmptyElim i
  jS := fun i => isEmptyElim i
  jS_range := fun i => isEmptyElim i
  side := fun i => isEmptyElim i
  rhoS := fun i => isEmptyElim i
  rhoS_cont := fun i => isEmptyElim i
  S0 := fun i => isEmptyElim i
  twistExcludedPlaces_contains_residueChar := fun i => isEmptyElim i
  placesOver_subset_exceptional := fun i => isEmptyElim i
  primes_subset_exceptional := fun i => isEmptyElim i
  B := fun i => isEmptyElim i
  acgB := fun i => isEmptyElim i
  modB := fun i => isEmptyElim i
  freeB := fun i => isEmptyElim i
  finB := fun i => isEmptyElim i
  Theta := fun i => isEmptyElim i
  ThetaPsi := fun i => isEmptyElim i
  ThetaPsi_one := fun i => isEmptyElim i
  hk := fun i => isEmptyElim i
  hk_zero := fun i => isEmptyElim i
  hEig := fun i => isEmptyElim i
  abelian₂ := fun i => isEmptyElim i
  finLam := fun i => isEmptyElim i
  jL := fun i => isEmptyElim i
  sideL := fun i => isEmptyElim i
  s2 := fun i => isEmptyElim i
  jL_range := fun i => isEmptyElim i
  lamG := fun i => isEmptyElim i
  lamG_cont := fun i => isEmptyElim i
  lamG_unr := fun i => isEmptyElim i
  lamG_pD := fun i => isEmptyElim i
  lamG_anti := fun i => isEmptyElim i
  Xv := fun i => isEmptyElim i
  Xv_def := fun i => isEmptyElim i
  qs := fun i => isEmptyElim i
  qs_sq := fun i => isEmptyElim i
  qs_conj := fun i => isEmptyElim i
  RCG := fun i => isEmptyElim i
  grpRCG := fun i => isEmptyElim i
  finRCG := fun i => isEmptyElim i
  RCG_l := fun i => isEmptyElim i
  art := fun i => isEmptyElim i
  art_surj := fun i => isEmptyElim i
  art_cont := fun i => isEmptyElim i
  art_anti := fun i => isEmptyElim i
  art_unr := fun i => isEmptyElim i
  art_univ := fun i => isEmptyElim i
  res := fun i => isEmptyElim i
  res_art := fun i => isEmptyElim i
  th := fun i => isEmptyElim i
  twOf := fun i => isEmptyElim i
  twSide := fun i => isEmptyElim i
  twOf_l := fun i => isEmptyElim i
  twist₂ := fun i => isEmptyElim i
  twO_emb := fun i => isEmptyElim i
  psiL := fun i => isEmptyElim i
  psiL_ord := fun i => isEmptyElim i
  psiL_open := fun i => isEmptyElim i
  psiL_anti := fun i => isEmptyElim i
  psiL_ram := fun i => isEmptyElim i
  psiL_l := fun i => isEmptyElim i
  chi_tw := fun i => isEmptyElim i

variable {LL0}

set_option synthInstance.maxHeartbeats 400000 in

def nExp {N : NData R H what₂} (tw : NTw R H what₂ LL0 N) [IsEmpty tw.Tw] : NExp R H what₂ LL0 N tw where
  U := ⊥
  eLL0 := fun _ => 0
  Fm := fun i => isEmptyElim i
  acgFm := fun i => isEmptyElim i
  modFmK := fun i => isEmptyElim i
  modFmO := fun i => isEmptyElim i
  towFm := fun i => isEmptyElim i
  fdFm := fun i => isEmptyElim i
  actG := fun i => isEmptyElim i
  psiU := fun i => isEmptyElim i
  eAlg := fun i => isEmptyElim i
  eAlg_def := fun i => isEmptyElim i
  eAlg_idem := fun i => isEmptyElim i
  eAlg_central := fun i => isEmptyElim i
  Bsup := fun i => isEmptyElim i
  Dat := fun i => isEmptyElim i
  th := fun i => isEmptyElim i
  lev := fun i => isEmptyElim i
  thPsi := fun i => isEmptyElim i
  thPsi_one := fun i => isEmptyElim i
  thU := fun i => isEmptyElim i
  twPsi := fun i => isEmptyElim i
  twPsi_one := fun i => isEmptyElim i
  twDel := fun i => isEmptyElim i
  delU := fun i => isEmptyElim i
  delU_unr := fun i => isEmptyElim i
  delU_l := fun i => isEmptyElim i
  delU_anti := fun i => isEmptyElim i
  delU_open := fun i => isEmptyElim i
  delU_res := fun i => isEmptyElim i
  delU_conj := fun i => isEmptyElim i
  MtV := fun i => isEmptyElim i
  acgMt := fun i => isEmptyElim i
  modMtK := fun i => isEmptyElim i
  modMtO := fun i => isEmptyElim i
  towMt := fun i => isEmptyElim i
  fdMt := fun i => isEmptyElim i
  MtLat := fun i => isEmptyElim i
  MtLat_fg := fun i => isEmptyElim i
  MtLat_span := fun i => isEmptyElim i
  thP := fun i => isEmptyElim i
  hkF := fun i => isEmptyElim i
  embB := fun i => isEmptyElim i
  embB_inj := fun i => isEmptyElim i
  eH := fun i => isEmptyElim i
  eH_idem := fun i => isEmptyElim i

set_option synthInstance.maxHeartbeats 400000 in

def nTh {N : NData R H what₂} {tw : NTw R H what₂ LL0 N} [IsEmpty tw.Tw] (ex : NExp R H what₂ LL0 N tw) :
    NTh R H what₂ LL0 N tw ex where
  iC := fun i => isEmptyElim i
  iC_int := fun i => isEmptyElim i
  aL := fun i => isEmptyElim i
  aL_g := fun i => isEmptyElim i
  aL_off := fun i => isEmptyElim i
  Pt := fun i => isEmptyElim i
  ev := fun i => isEmptyElim i
  ev_smul := fun i => isEmptyElim i
  ev_inj := fun i => isEmptyElim i
  Lt := fun i => isEmptyElim i
  acgLt := fun i => isEmptyElim i
  modLt := fun i => isEmptyElim i
  freeLt := fun i => isEmptyElim i
  finLt := fun i => isEmptyElim i
  Let := fun i => isEmptyElim i
  finLet := fun i => isEmptyElim i
  Harm := fun i => isEmptyElim i
  Ctr := fun i => isEmptyElim i
  ctrC := fun i => isEmptyElim i
  Harm_def := fun i => isEmptyElim i
  thV := fun i => isEmptyElim i
  thV_add := fun i => isEmptyElim i
  thV_smul := fun i => isEmptyElim i
  thV_addP := fun i => isEmptyElim i
  thV_smulP := fun i => isEmptyElim i
  datPhi := fun i => isEmptyElim i
  datP := fun i => isEmptyElim i
  recDet := fun i => isEmptyElim i
  Kq := fun i => isEmptyElim i
  grpKq := fun i => isEmptyElim i
  actK := fun i => isEmptyElim i
  actK_one := fun i => isEmptyElim i
  actK_mul := fun i => isEmptyElim i
  recDetq := fun i => isEmptyElim i
  recDetq_mem := fun i => isEmptyElim i
  recDet_act := fun i => isEmptyElim i
  recDetq_act := fun i => isEmptyElim i
  hkIdx := fun i => isEmptyElim i
  finHk := fun i => isEmptyElim i
  hkMove := fun i => isEmptyElim i
  hkU := fun i => isEmptyElim i
  hk_ev := fun i => isEmptyElim i
  MaximalUnramifiedExtension := fun i => isEmptyElim i
  FmUr := fun i => isEmptyElim i
  FmUr_smul := fun i => isEmptyElim i
  FmUr_span := fun i => isEmptyElim i
  Bsup_def := fun i => isEmptyElim i

end Twist

end Records

section Types

variable {H : Host R} {what₂ : Rows.Data R}

open Classical in

def unipSer (K : Type) [Field K] (r : ℕ) (A : Type) [Ring A] (f : K[X]) : A :=
  if f = (X - 1) ^ r then 1 else 0

theorem unip_coeff_zero (K : Type) [Field K] (r : ℕ) : ((X - 1 : K[X]) ^ r).coeff 0 ≠ 0 := by
  rw [coeff_zero_eq_eval_zero]
  simp

theorem unipSer_sum (K : Type) [Field K] [Finite K] (r : ℕ) (A : Type) [Ring A] :
    ∃ S : Finset K[X], (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0) ∧
      ∑ f ∈ S, unipSer K r A f = 1 := by
  classical
  have hfin : {f : K[X] | f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0}.Finite :=
    (Set.finite_range (Formalism.CyclotomicNorms.monicOf (K := K) (N := r))).subset fun f hf =>
      ⟨_, Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f hf.1 hf.2.1⟩
  refine ⟨hfin.toFinset, fun f => hfin.mem_toFinset, ?_⟩
  unfold unipSer
  rw [Finset.sum_ite_eq', if_pos]
  exact hfin.mem_toFinset.2 ⟨(monic_unip r).1, (monic_unip r).2, unip_coeff_zero K r⟩

theorem unipSer_of_squarefree {K : Type} [Field K] {r : ℕ} (hr : 2 ≤ r) (A : Type) [Ring A] {f : K[X]}
    (hf : Squarefree f) : unipSer K r A f = 0 := by
  refine if_neg fun h => ?_
  have h1 : IsUnit (X - 1 : K[X]) := hf _ (by rw [h, ← sq]; exact pow_dvd_pow _ hr)
  have h2 := natDegree_eq_zero_of_isUnit h1
  have h3 := (monic_unip (K := K) 1).2
  rw [pow_one] at h3
  omega

theorem rootsBar_unip (g : ℕ) [Fact g.Prime] (n : ℕ) :
    Formalism.CyclotomicNorms.rootsBar ((X - 1 : (ZMod g)[X]) ^ n) = Multiset.replicate n 1 := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_pow, Polynomial.map_sub, map_X, Polynomial.map_one, roots_pow, ← C_1, roots_X_sub_C,
    Multiset.nsmul_singleton]

def cenTriv (Γ : Type) [Group Γ] (V : Type) [AddCommGroup V] [Module ℂ V] :
    Subalgebra.center ℂ (MonoidAlgebra ℂ Γ) →ₐ[ℂ] Module.End ℂ V :=
  (MonoidAlgebra.lift ℂ (Module.End ℂ V) Γ 1).comp (Subalgebra.val _)

set_option synthInstance.maxHeartbeats 400000 in

def nTypes (N : NData R H what₂) [IsEmpty N.Loc] (pl : ∀ k, N.PlG k → PlE H)
    (h1 : ∀ k v, pl k v ∈ placesOver H.E (H.g k)) (h2 : ∀ k, Function.Injective (pl k))
    (h3 : ∀ k v v', ¬ IsConjPl H (pl k v) (pl k v'))
    (hc : ∀ k, H.g k % (H.QS * H.q * H.d) = 1)
    (hB : Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)))
    (tg : ∀ k, N.PlG k → G H.E N.Om) (htg : ∀ k v, TameGenAt (N.plOm.1 (pl k v)) (tg k v)) :
    NTypes (nAut N pl h1 h2 h3) where
  Mray := H.K
  Mray_gal := inferInstance
  Mray_ab := fun σ τ => Subsingleton.elim _ _
  Mray_unr := fun p _ h => by
    rw [discr_K, dvd_neg] at h
    exact Dvd.dvd.mul_left (by exact_mod_cast h) _
  g_Mray := fun k => split_K H (H.g_prime k) (hc k)
  g_cond := hc
  BB_disj := hB
  bc := fun _ => {(R.r, 1)}
  bc_pos := fun _ p hp => by
    have := two_le_r R
    rw [Multiset.mem_singleton.1 hp]
    exact ⟨by show 0 < R.r; omega, one_pos⟩
  bc_sum := fun _ => by simp
  rbar := fun _ _ => 1
  rbar_open := fun _ _ => by
    rw [MonoidHom.ker_one]
    exact isOpen_univ
  tg := tg
  tg_mem := fun k v => (htg k v).1
  tg_gen := htg
  iota := fun k _ w => (@exists_iota (H.g k) _ ⟨H.g_prime k⟩ ⟨what₂.places.resChar_prime w⟩).choose
  iota_inj := fun k _ w => (@exists_iota (H.g k) _ ⟨H.g_prime k⟩ ⟨what₂.places.resChar_prime w⟩).choose_spec
  teichC := fun k => (@exists_teichC (H.g k) ⟨H.g_prime k⟩).choose
  teichC_inj := fun k => (@exists_teichC (H.g k) ⟨H.g_prime k⟩).choose_spec
  inertiaCharpoly_type := fun k v L _ => by
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    show (X - 1 : ℂ[X]) ^ Multiset.card L.1 =
      ((Formalism.CyclotomicNorms.rootsBar ((X - 1 : (ZMod (H.g k))[X]) ^ Multiset.card L.1)).map _).prod
    rw [rootsBar_unip, Multiset.map_replicate, Multiset.prod_replicate, map_one, C_1]
  eSer := fun k => @unipSer (ZMod (H.g k)) (@ZMod.instField _ ⟨H.g_prime k⟩) R.r _ _
  eSer_idem := fun k f => by
    unfold unipSer
    split_ifs <;> simp
  eSer_central := fun k f a => by
    unfold unipSer
    split_ifs <;> simp
  eSer_orth := fun k f f' h => by
    unfold unipSer
    split_ifs with a b
    · exact absurd (a.trans b.symm) h
    all_goals simp
  eSer_zero := fun k f h => by
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    refine if_neg fun h0 => h ?_
    rw [h0]
    exact ⟨(monic_unip _).1, (monic_unip _).2, unip_coeff_zero _ _⟩
  eSer_sum := fun k => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; unipSer_sum _ _ _
  cenAmb := fun _ => cenTriv _ _
  cenMt := fun _ _ => cenTriv _ _
  Par := Unit
  labPar := fun _ _ _ => (X - 1) ^ R.r
  labPar_monic := fun k _ _ => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; monic_unip _
  locPar := fun _ _ => ⟨Multiset.replicate R.r 1, by simp [Multiset.mem_replicate]⟩
  locPar_dim := fun _ _ => Multiset.card_replicate _ _
  labPar_def := fun k _ _ => by
    show _ = (X - 1 : (ZMod (H.g k))[X]) ^ Multiset.card (Multiset.replicate R.r (1 : ℂ))
    rw [Multiset.card_replicate]
  MtPar := fun _ _ _ => ⊤
  AmbPar := fun _ _ => ⊤
  heckeLoc_gamma_places := fun i => isEmptyElim i
  chiT_tg := fun i => isEmptyElim i

theorem idempotent_good_tuples_eq_zero {N : NData R H what₂} {A : NAut N} (T : NTypes A)
    (h : ∀ k f, Squarefree f → T.eSer k f = 0) : T.e0 = 0 := by
  have hne : Nonempty (N.PlG 0) := by
    rw [← Fintype.card_pos_iff, N.card_PlG]
    exact f_pos R
  obtain ⟨v⟩ := hne
  ext g
  simp only [NTypes.e0, Finsupp.equivFunOnFinite_symm_apply_apply, MonoidAlgebra.coeff_ofCoeff]
  refine finsum_eq_zero_of_forall_eq_zero fun a => ?_
  split_ifs with hg
  · refine Finset.prod_eq_zero (Finset.mem_univ ⟨0, v⟩) ?_
    rw [h _ _ ((hg 0).1.2.1 v)]
    rfl
  · rfl

theorem good_tuple_condition_of_idempotent_zero {N : NData R H what₂} {A : NAut N} (T : NTypes A) (h : T.e0 = 0)
    (h1 : ∀ μ, what₂.eOp μ = 0) (h2 : ∀ μ j, what₂.eMt μ j = 0) : T.IdempotentMatchesAction := by
  refine ⟨fun μ => ?_, fun μ j => ?_⟩
  · rw [h, h1, NTypes.onAmb, dif_pos (zero_mem _)]
    exact (map_zero (T.cenAmb μ)).symm
  · rw [h, h2, NTypes.onMt, dif_pos (zero_mem _)]
    exact (map_zero (T.cenMt μ j)).symm

end Types

theorem exists_nStage_of_rows (B : Base) (C : Cols B) (W : RowsRest B C) (L : LocStage)
    (hsha : ∀ p e, W.shaLen p e = shaTrue B.host p e) (heta : ∀ j w, 1 ≤ j → j ≤ B.R.m → W.etaJ j w = 0)
    (hOp : ∀ μ, W.eOp μ = 0) (hMt : ∀ μ j, W.eMt μ j = 0) :
    ∃ N : NStage B C W, N.toLocStage = L := by
  have hsp := fun k => (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ (B.host.g_prime k) (B.g_cond k)).1
  let nd : NData B.R B.host W.what₂ := nData B.host W.what₂ hsha hsp rfl
  haveI : IsEmpty nd.Loc := inferInstanceAs (IsEmpty Empty)
  choose pl h1 h2 h3 using fun k => exists_places B.host (B.host.g_prime k) (hsp k)
  choose tg htg using fun (k : Fin 2) (v : nd.PlG k) =>
    GlobalTheory.TameInertiaGen.exists_tameGenAt B.host.E nd.Om (pl k v) (nd.plOm.1 (pl k v)) (nd.plOm.2 _)
  let tw := nTw B.LL0 nd
  haveI : IsEmpty tw.Tw := inferInstanceAs (IsEmpty Empty)
  let T := nTypes nd pl h1 h2 h3 B.g_cond B.BB_disj tg htg
  have hT : T.e0 = 0 := idempotent_good_tuples_eq_zero T fun k f hf =>
    @unipSer_of_squarefree _ (@ZMod.instField _ ⟨B.host.g_prime k⟩) _ (two_le_r B.R) _ _ f hf
  exact ⟨{
    toLocStage := L
    nd := nd
    ntw := tw
    naut := nAut nd pl h1 h2 h3
    nbc := nBC _
    nexp := nExp tw
    ntypes := T
    nStage_trivialCharacter_compat := good_tuple_condition_of_idempotent_zero T hT hOp hMt
    nStage_trivialCharacter_coeff_eq := fun g => by
      rw [hT]
      exact map_zero B.embLL
    nth := nTh _
    nbr := fun i => i.elim
    nbr_ind := fun i => i.elim
    self_good := fun i => i.elim
    ntwbr := fun i => i.elim
    ntwbr_ind := fun i => i.elim
    loc_tie := fun i => i.elim
    bc_tie := fun i => i.elim
    rbar_tie := fun i => i.elim
    mtpar_tie := fun i => i.elim
    Z_tie := fun i => i.elim
    Zgood_tie := fun i => i.elim
    etaJ_tie := fun j w a b => (heta j w a b).trans Finset.sum_empty.symm }, rfl⟩

def adapt {B : Base} {C : Cols B} (W : RowsRest B C) : RowsRest B C :=
  { W with
    shaLen := shaTrue B.host
    shaLen_nonneg := shaTrue_nonneg B.host
    etaJ := fun _ _ => 0
    etaJ_nonneg := fun _ _ => le_rfl
    eOp := fun _ => 0
    eOp_idem := fun _ => LinearMap.zero_comp _
    eOp_sa := fun _ => LinearMap.IsSymmetric.zero
    eMt := fun _ _ => 0
    eMt_idem := fun _ _ => LinearMap.zero_comp _
    eMt_sa := fun _ _ => LinearMap.IsSymmetric.zero
    eMt_LL := fun μ j _ => ⟨0, map_zero (W.jMt μ j)⟩ }

theorem exists_nStage_adapt (B : Base) (C : Cols B) (W : RowsRest B C) (L : LocStage) :
    ∃ N : NStage B C (adapt W), N.toLocStage = L :=
  exists_nStage_of_rows B C (adapt W) L (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

theorem exists_nStage : ∀ (B : Base) (C : Cols B) (W : RowsRest B C) (L : LocStage),
    ∃ W' : RowsRest B C, W' = adapt W ∧ ∃ N : NStage B C W', N.toLocStage = L :=
  fun B C W L => ⟨adapt W, rfl, exists_nStage_adapt B C W L⟩

end GlobalTheory.Mem.GaloisStage

end
