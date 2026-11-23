import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexSpanMatrixEqValDet

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.AntiRamConj
open scoped TensorProduct

namespace GlobalTheory.TwistDet

variable {D : Formalism.BasicNotions.D7}

theorem finite_placesOver {p : ℕ} (hp : p ≠ 0) : (placesOver D.host.E p).Finite :=
  (Ideal.finite_factors (I := Ideal.span {(p : 𝓞 D.host.E)}) (by simpa using hp)).subset
    fun _ hv => Ideal.dvd_span_singleton.2 hv

theorem prime_normV {v : PlE D.host} (h : v.asIdeal.inertiaDeg ℤ = 1) : (normV v).Prime := by
  have := v.isPrime
  have h1 := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
  rw [h, pow_one] at h1
  have h2 : Ideal.absNorm v.asIdeal = normV v := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (v.asIdeal.under ℤ)).principal
  have ha' : v.asIdeal.under ℤ = Ideal.span {a} := ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [ha', Ideal.span_singleton_zero, Ideal.absNorm_bot] at h1
    exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h1.symm)
  have hpa : Prime a := (Ideal.span_singleton_prime ha0).1 (ha' ▸ inferInstance)
  rw [← h2, ← h1, ha', Ideal.absNorm_span_singleton, Algebra.norm_self]
  exact Int.prime_iff_natAbs_prime.1 hpa

theorem exists_splitK {v : PlE D.host} (h : v.asIdeal.inertiaDeg ℤ = 1) (he : eWL D.host.E v = 1)
    (hodd : Odd (normV v))
    (hq : v ∉ placesOver D.host.E D.host.q) (hd : v ∉ placesOver D.host.E D.host.d) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ v.asIdeal) := by
  have hp := prime_normV h
  have hmem : ((normV v : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := by
    have h2 : Ideal.absNorm v.asIdeal = normV v := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    exact h2 ▸ Ideal.absNorm_mem v.asIdeal
  refine ⟨normV v, hp, hodd, ?_, hmem⟩
  have n2 : normV v ∉ D.host.small := UpperTheory.Small.not_mem_of_ramIdx_one D.host hp v hmem he
  have nq : normV v ≠ D.host.q := fun e => hq (show ((D.host.q : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal from e ▸ hmem)
  have nd : normV v ≠ D.host.d := fun e => hd (show ((D.host.d : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal from e ▸ hmem)
  have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hi : IsIntegral ℤ D.host.sqrtMinusD :=
    IsIntegral.of_pow two_pos (hb ▸ (isIntegral_natCast (R := ℤ) _).neg)
  let b : 𝓞 D.host.E := ⟨_, hi⟩
  have hb' : b * b = -(D.host.d : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    rw [← sq]
    push_cast
    exact hb
  have : Fact (normV v).Prime := ⟨hp⟩
  have : Finite (𝓞 D.host.E ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero hp.ne_zero
  let := Fintype.ofFinite (𝓞 D.host.E ⧸ v.asIdeal)
  let e := ZMod.ringEquivOfPrime (𝓞 D.host.E ⧸ v.asIdeal) hp (Nat.card_eq_fintype_card.symm)
  have hsq : IsSquare (((-(D.host.d : ℤ) : ℤ)) : ZMod (normV v)) :=
    ⟨e.symm (Ideal.Quotient.mk _ b), by rw [← map_mul, ← map_mul, hb']; simp⟩
  have hne : (((-(D.host.d : ℤ) : ℤ)) : ZMod (normV v)) ≠ 0 := by
    rw [Int.cast_neg, neg_ne_zero, Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact fun hdvd => nd ((Nat.prime_dvd_prime_iff_eq hp D.host.hyp.2.1).1 hdvd)
  have hj : jacobiSym (-(D.host.d : ℤ)) (normV v) = 1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    exact (legendreSym.eq_one_iff _ hne).2 hsq
  exact (primeClass_eq_splitK_iff _).2 ⟨n2, nq, nd, hj⟩

variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_subgroup_isUnit (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (z : GE N)
    (hg : ∀ s, goodE Y i s) (h8 : ∀ s, characterTwistExists X Y i s) (h0 : ∀ s P, X.hEig i s 0 P = 1) (hz : IsTameInertiaElementAtTwistPrime X i z) :
    ∃ H : Subgroup (GE N), IsOpen (H : Set (GE N)) ∧ H.Normal ∧ ∀ P P' : PlE D.host, Over P P' →
      IsSplitPl D.host P' → P' ∉ X.S0 i →
      (∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ H) →
      ∀ s, IsUnit (1 + ∑ n ∈ Finset.Icc 1 D.R.r,
        ((-1 : X.O i) ^ n * ((normV P' : ℕ) : X.O i) ^ (n * (n - 1) / 2)) * X.hEig i s n P') := by
  choose η hηc _ hηD hηF using fun s => h8 s (hg s)
  let ρ := IsLocalRing.residue (X.O0 i)
  let W : X.Sig i → GE N → Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) := fun s g =>
    ((η s g : (X.O0 i)ˣ) : X.O0 i) • ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix _ _ (X.O0 i))
  let Wb : X.Sig i → GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (X.O0 i)) := fun s =>
    { toFun := fun g => (W s g).map ρ
      map_one' := by simp [W]
      map_mul' := fun g h => by
        rw [← Matrix.map_mul]
        simp only [W, map_mul, Units.val_mul, smul_mul_smul_comm] }
  have hm : IsOpen (IsLocalRing.maximalIdeal (X.O0 i) : Set (X.O0 i)) := by
    simpa using (isAdic_iff.1 (X.twistBaseCoefficientRing_isAdic i)).1 1
  have hopen : ∀ s, IsOpen ((Wb s).ker : Set (GE N)) := by
    intro s
    have hc : Continuous (W s) := (hηc s).smul (X.rhoS_cont i s)
    have e : ((Wb s).ker : Set (GE N)) = ⋂ a, ⋂ b, (fun g => W s g a b - (1 : Matrix _ _ (X.O0 i)) a b) ⁻¹'
        (IsLocalRing.maximalIdeal (X.O0 i) : Set (X.O0 i)) := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage,
        ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← Matrix.ext_iff]
      refine forall₂_congr fun a b => ?_
      have : (1 : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (X.O0 i))) a b =
          ρ ((1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) a b) := by
        simp [Matrix.one_apply, apply_ite]
      rw [this]
      rfl
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      hm.preimage ((hc.matrix_elem a b).sub continuous_const)
  let H₀ : Subgroup (GE N) := ⨅ s, (Wb s).ker
  have hH₀ : IsOpen (H₀ : Set (GE N)) := by
    rw [Subgroup.coe_iInf]; exact isOpen_iInter_of_finite hopen
  have hn₀ : H₀.Normal := Subgroup.normal_iInf_normal fun s => inferInstance
  refine ⟨H₀ ⊓ H₀.comap (cConj X), hH₀.inter (isOpen_comap_cConj X hH₀), inferInstance, ?_⟩
  intro P P' hPP' hs hS hF s
  obtain ⟨v, hv, A, hA, hzA, hu, -⟩ := hz
  set δ := X.delta i z with hδ
  have hsc : ∀ z' : GE N, (X.delta i z' = δ ∨ X.delta i z' = δ⁻¹) → (∃ v ∈ X.pD i, ∃ A : ValuationSubring N.Om,
      IsPlaceOver A v ∧ z' ∈ Ine (F := D.host.E) A) → ∀ σ g : GE N, g * σ * g⁻¹ * z'⁻¹ ∈ H₀ →
      ∃ c : (X.O0 i)ˣ, (c = δ ∨ c = δ⁻¹) ∧ Wb s σ⁻¹ = ρ c • (1 : Matrix _ _ _) := by
    rintro z' hz' ⟨v, hv, A, hA, hzA⟩ σ g hH
    have h1 : ∃ c : (X.O0 i)ˣ, (c = δ ∨ c = δ⁻¹) ∧ W s z'⁻¹ = (c : X.O0 i) • (1 : Matrix _ _ _) := by
      rcases hηD s v hv A hA with h | h
      · refine ⟨_, ?_, h _ (inv_mem hzA)⟩
        rw [map_inv]
        rcases hz' with e | e
        · exact Or.inr (by rw [e])
        · exact Or.inl (by rw [e, inv_inv])
      · refine ⟨_, ?_, h _ (inv_mem hzA)⟩
        rw [map_inv, inv_inv]; exact hz'
    obtain ⟨c, hc, hW⟩ := h1
    refine ⟨c, hc, ?_⟩
    have h2 : Wb s z'⁻¹ = ρ c • (1 : Matrix _ _ _) := by
      change (W s z'⁻¹).map ρ = _
      rw [hW]
      ext a b
      by_cases hab : a = b
      · subst hab; simp
      · simp [Matrix.one_apply_ne hab]
    have h3 : Wb s (g * σ * g⁻¹ * z'⁻¹)⁻¹ = 1 := Subgroup.mem_iInf.1 (inv_mem hH) s
    have e : σ⁻¹ = g⁻¹ * (z'⁻¹ * (g * σ * g⁻¹ * z'⁻¹)⁻¹) * g := by group
    rw [e, map_mul, map_mul, map_mul, h2, h3, mul_one, mul_smul_comm, mul_one, smul_mul_assoc, ← map_mul,
      inv_mul_cancel, map_one]
  obtain ⟨σ, hσ⟩ := exists_isFrob (F := D.host.E) (N.plOm.2 P')
  have h4 : ∃ c : (X.O0 i)ˣ, (c = δ ∨ c = δ⁻¹) ∧ Wb s σ⁻¹ = ρ c • (1 : Matrix _ _ _) := by
    rcases hPP' with rfl | hPP'
    · obtain ⟨g, hg⟩ := hF σ hσ
      exact hsc z (Or.inl rfl) ⟨v, hv, A, hA, hzA⟩ σ g hg.1
    · obtain ⟨σ₀, g', hσ₀, rfl⟩ := exists_frob_of_conj X hPP' hσ
      obtain ⟨g, hg⟩ := hF σ₀ hσ₀
      obtain ⟨v', hv'⟩ := exists_isConjPl v
      refine hsc (cConj X z) (Or.inr (antiHom_cConj X (X.delta_anti i) z))
        ⟨v', ?_, _, isPlaceOver_moveVal_cc X hv' hA, cConj_mem_ine X hzA⟩ _ (cConj X g * g'⁻¹) ?_
      · rw [← Finset.mem_coe, X.pD_eq] at hv ⊢
        exact mem_placesOver_conj hv' hv
      · have : cConj X (g * σ₀ * g⁻¹ * z⁻¹) ∈ H₀ := hg.2
        rw [map_mul, map_mul, map_mul, map_inv, map_inv] at this
        convert this using 1
        group
  obtain ⟨c, hc, hW⟩ := h4
  have h5 := hηF s P' hS hs σ⁻¹ (by rwa [inv_inv])
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), h0] at h5
  have e6 : Finset.Ico (0 + 1) (D.R.r + 1) = Finset.Icc 1 D.R.r := by
    ext a; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [e6] at h5
  simp only [pow_zero, zero_mul, Nat.zero_div, mul_one] at h5
  rw [h5]
  refine IsUnit.map _ ?_
  have hc1 : IsUnit (1 - (c : X.O0 i)) := by
    have hu1 : IsUnit ((δ : X.O0 i) - 1) :=
      isUnit_of_mul_isUnit_left (y := (δ : X.O0 i) + 1) (by convert hu using 1; ring)
    rcases hc with rfl | rfl
    · simpa using hu1.neg
    · have : 1 - ((δ⁻¹ : (X.O0 i)ˣ) : X.O0 i) = ((δ⁻¹ : (X.O0 i)ˣ) : X.O0 i) * ((δ : X.O0 i) - 1) := by
        rw [mul_sub, Units.inv_mul, mul_one]
      rw [this]
      exact (Units.isUnit _).mul hu1
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, map_sub, map_one]
  have e7 : (IsLocalRing.residue (X.O0 i)).mapMatrix (W s σ⁻¹) = ρ c • (1 : Matrix _ _ _) := hW
  rw [e7]
  have e8 : (1 : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (X.O0 i))) - ρ c • 1 =
      ρ (1 - c) • (1 : Matrix _ _ _) := by rw [map_sub, map_one, sub_smul, one_smul]
  rw [e8, Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ (hc1.map ρ).ne_zero

theorem goodChar_of_over {i : X.Tw} {M : ℕ} {P P' : PlE D.host} (h : Over P P')
    {d d' : GE N →* Multiplicative (ZMod (X.l i ^ M))} (hd : GoodChar X i M P d) (s : ℤˣ)
    (hs : ∀ σ, Multiplicative.toAdd (d' σ) = ((s : ℤ) : ZMod (X.l i ^ M)) * Multiplicative.toAdd (d σ)) :
    GoodChar X i M P' d' := by
  have ho : ∀ v, Over P' v ↔ Over P v := fun v => ⟨over_trans h, over_trans (over_symm h)⟩
  rcases Int.units_eq_one_or s with rfl | rfl
  · obtain rfl : d' = d := MonoidHom.ext fun σ => Multiplicative.toAdd.injective (by simpa using hs σ)
    exact ⟨hd.1, hd.2.1, hd.2.2.1, fun v hv => hd.2.2.2.1 v (mt (ho v).2 hv), fun v hv => hd.2.2.2.2 v ((ho v).1 hv)⟩
  · have e : ∀ σ, d' σ = (d σ)⁻¹ := fun σ => Multiplicative.toAdd.injective (by simpa using hs σ)
    refine ⟨?_, fun g g' hg => by rw [e, e, hd.2.1 g g' hg], fun v hv A hA σ hσ => by
      rw [e, hd.2.2.1 v hv A hA σ hσ, inv_one], fun v hv A hA σ hσ => by
      rw [e, hd.2.2.2.1 v (mt (ho v).2 hv) A hA σ hσ, inv_one], fun v hv A hA c => ?_⟩
    · have : d'.ker = d.ker := by ext σ; simp [MonoidHom.mem_ker, e]
      rw [this]; exact hd.1
    · obtain ⟨σ, hσ, hc⟩ := hd.2.2.2.2 v ((ho v).1 hv) A hA c⁻¹
      exact ⟨σ, hσ, by rw [e, hc, inv_inv]⟩

def IsSub {ι : Type} (P : ι → PlE D.host) (J : Finset ι) (Q : Finset (PlE D.host)) : Prop :=
  ∀ v, v ∈ Q ↔ ∃ q ∈ J, Over (P q) v

theorem exists_isSub {ι : Type} (P : ι → PlE D.host) (J : Finset ι) : ∃ Q, IsSub P J Q := by
  classical
  choose c hc using exists_isConjPl (D := D)
  refine ⟨J.image P ∪ J.image (fun q => c (P q)), fun v => ?_⟩
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    exacts [⟨q, hq, Or.inl rfl⟩, ⟨q, hq, Or.inr (hc _)⟩]
  · rintro ⟨q, hq, rfl | h⟩
    exacts [Or.inl ⟨q, hq, rfl⟩, Or.inr ⟨q, hq, isConjPl_unique (hc _) h⟩]

theorem IsSub.conjCl {ι : Type} {P : ι → PlE D.host} {J : Finset ι} {Q : Finset (PlE D.host)} (h : IsSub P J Q) :
    ConjCl (D := D) Q := fun v hv v' hc => by
  obtain ⟨q, hq, ho⟩ := (h v).1 hv
  exact (h v').2 ⟨q, hq, over_trans ho (Or.inr hc)⟩

theorem IsSub.unique {ι : Type} {P : ι → PlE D.host} {J : Finset ι} {Q Q' : Finset (PlE D.host)} (h : IsSub P J Q)
    (h' : IsSub P J Q') : Q = Q' := Finset.ext fun v => (h v).trans (h' v).symm

theorem IsSub.mem_iff {ι : Type} {P : ι → PlE D.host} {J : Finset ι} {Q : Finset (PlE D.host)} (h : IsSub P J Q)
    (hP : ∀ q q', Over (P q) (P q') → q = q') (q : ι) : P q ∈ Q ↔ q ∈ J := by
  rw [h]
  exact ⟨fun ⟨q', hq', ho⟩ => hP _ _ ho ▸ hq', fun hq => ⟨q, hq, over_refl _⟩⟩

open Classical in
theorem IsSub.erase {ι : Type} {P : ι → PlE D.host} {J : Finset ι} {Q : Finset (PlE D.host)} {q : ι} (hq : q ∉ J)
    (h : IsSub P (insert q J) Q) (hP : ∀ q q', Over (P q) (P q') → q = q') {v v' : PlE D.host} (hv : Over (P q) v)
    (hc : IsConjPl D.host v v') : IsSub P J ((Q.erase v).erase v') := by
  intro w
  rw [Finset.mem_erase, Finset.mem_erase, h]
  constructor
  · rintro ⟨h1, h2, q', hq', ho⟩
    rcases Finset.mem_insert.1 hq' with rfl | hq'
    · rcases over_trans (over_symm hv) ho with e | e
      exacts [absurd e h2, absurd (isConjPl_unique e hc) h1]
    · exact ⟨q', hq', ho⟩
  · rintro ⟨q', hq', ho⟩
    have hn : ¬ Over (P q) w := fun h' => hq (hP _ _ (over_trans h' (over_symm ho)) ▸ hq')
    exact ⟨fun e => hn (e ▸ over_trans hv (Or.inr hc)), fun e => hn (e ▸ hv), q', Finset.mem_insert_of_mem hq', ho⟩

variable (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem IsSub.admissible {ι : Type} {i : X.Tw} {M : ℕ} {A : Finset (PlE D.host)} {P : ι → PlE D.host}
    {d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))} (hd : IsCoord Y i M d)
    (hA : SlopeTestRemainingChoices X i M A P fun q => d (P q)) (hq : placesOver D.host.E D.host.q ⊆ A)
    (hd' : placesOver D.host.E D.host.d ⊆ A) {J : Finset ι} {Q : Finset (PlE D.host)} (h : IsSub P J Q) :
    QOk X i Q ∧ Formalism.MainNotions.IntegralHeckeForms.ClsQ (D := D) Q ∧ Disjoint Q A ∧
      ∀ v ∈ Q, GoodChar X i M v (d v) ∧ normV v % (2 * X.l i ^ M) = 1 := by
  have h1 := fun v hv => ((h v).1 hv).elim fun q hq => hA.1 q v hq.2
  refine ⟨⟨fun v hv => (h1 v hv).1, Finset.disjoint_left.2 fun v hv => (h1 v hv).2.2.2.1, h.conjCl⟩, fun v hv => ?_,
    Finset.disjoint_left.2 fun v hv => (h1 v hv).2.2.2.2.1, fun v hv => ⟨?_, (h1 v hv).2.2.2.2.2⟩⟩
  · refine exists_splitK (h1 v hv).2.1 (h1 v hv).2.2.1 ?_ (fun e => (h1 v hv).2.2.2.2.1 (hq e)) fun e => (h1 v hv).2.2.2.2.1 (hd' e)
    rw [Nat.odd_iff, ← Nat.mod_mod_of_dvd _ (Dvd.intro (X.l i ^ M) rfl), (h1 v hv).2.2.2.2.2]
  · obtain ⟨q, hq, ho⟩ := (h v).1 hv
    rcases ho with rfl | hc
    · exact hA.2.2 q
    · have hP : P q ∈ Q := (h _).2 ⟨q, hq, over_refl _⟩
      obtain ⟨s, hs⟩ := Y.delU_conj i Q M (P q) hP v hv hc
      refine goodChar_of_over (Or.inr hc) (hA.2.2 q) s fun σ => ?_
      rw [← hd Q h.conjCl v hv, ← hd Q h.conjCl _ hP, hs]

end GlobalTheory.TwistDet

end
