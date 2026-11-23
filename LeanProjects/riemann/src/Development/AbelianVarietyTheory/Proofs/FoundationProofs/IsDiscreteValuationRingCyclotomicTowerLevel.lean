import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatementStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPowStatement

noncomputable section

namespace GlobalTheory.K5.OnDVR

open Polynomial GlobalTheory.K5

theorem dvr_of_span_maximal {S : Type*} [CommRing S] [IsNoetherianRing S] (π : S)
    (hmax : (Ideal.span {π}).IsMaximal) (hall : ∀ M : Ideal S, M.IsMaximal → π ∈ M)
    (hnil : ¬ IsNilpotent π) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  have huniq : ∀ M : Ideal S, M.IsMaximal → M = Ideal.span {π} := fun M hM =>
    (hmax.eq_of_le hM.ne_top ((Ideal.span_singleton_le_iff_mem _).2 (hall M hM))).symm
  haveI : IsLocalRing S := IsLocalRing.of_unique_max_ideal ⟨_, hmax, huniq⟩
  have hm : IsLocalRing.maximalIdeal S = Ideal.span {π} := huniq _ inferInstance
  have hfac : ∀ a : S, a ≠ 0 → ∃ (k : ℕ) (u : S), IsUnit u ∧ a = π ^ k * u := by
    intro a ha
    classical
    have hex : ∃ k : ℕ, ¬ π ^ k ∣ a := by
      by_contra hcon
      push_neg at hcon
      have hb := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {π}) hmax.ne_top
      have : a ∈ (⨅ i : ℕ, (Ideal.span {π}) ^ i) := by
        rw [Ideal.mem_iInf]
        intro i
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        exact hcon i
      rw [hb] at this
      exact ha this
    have h0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h] at this
      simp at this
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have h1 : π ^ k ∣ a := by
      by_contra h
      have := Nat.find_min' hex h
      omega
    have h2 : ¬ π ^ (k + 1) ∣ a := by
      have := Nat.find_spec hex
      rwa [hk] at this
    obtain ⟨u, rfl⟩ := h1
    refine ⟨k, u, ?_, rfl⟩
    by_contra hu
    have : u ∈ IsLocalRing.maximalIdeal S := hu
    rw [hm, Ideal.mem_span_singleton] at this
    exact h2 (by rw [pow_succ]; exact mul_dvd_mul_left _ this)
  haveI : NoZeroDivisors S := ⟨fun {a b} hab => by
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, u, hu, rfl⟩ := hfac a hcon.1
    obtain ⟨l, v, hv, rfl⟩ := hfac b hcon.2
    apply hnil
    refine ⟨k + l, ?_⟩
    have : π ^ (k + l) * (u * v) = 0 := by rw [← hab]; ring
    exact ((hu.mul hv).mul_left_eq_zero).1 this⟩
  haveI : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := fun h => hnil (h ▸ IsNilpotent.zero)
  have hnf : ¬ IsField S := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot]
    exact hπ0
  have hp : (IsLocalRing.maximalIdeal S).IsPrincipal := ⟨⟨π, hm⟩⟩
  haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnf).out 0 4).2 hp
  exact ⟨inferInstance, inferInstance, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 hm⟩

theorem irreducible_X_pow_sub_param (K : Type*) [Field K] (N : ℕ) (hN : 1 ≤ N) :
    Irreducible (X ^ N - C (HahnSeries.single (1 : ℤ) (1 : K)) : Polynomial (LaurentSeries K)) := by
  have hmon : (X ^ N - C (PowerSeries.X : PowerSeries K)).Monic := monic_X_pow_sub_C _ (by omega)
  have hP : (Ideal.span {(PowerSeries.X : PowerSeries K)}).IsPrime := PowerSeries.span_X_isPrime
  have hirr : Irreducible (X ^ N - C (PowerSeries.X : PowerSeries K)) := by
    refine irreducible_of_eisenstein_criterion hP ?_ ?_ ?_ ?_ hmon.isPrimitive
    · rw [hmon.leadingCoeff]
      exact (Ideal.ne_top_iff_one _).1 hP.ne_top
    · intro i hi
      rw [degree_X_pow_sub_C (by omega)] at hi
      have hi' : i ≠ N := by
        have : i < N := by exact_mod_cast hi
        omega
      rw [coeff_sub, coeff_X_pow, if_neg hi', coeff_C]
      split_ifs
      · simp
      · simp
    · rw [degree_X_pow_sub_C (by omega)]
      exact_mod_cast hN
    · rw [coeff_sub, coeff_X_pow, if_neg (by omega), coeff_C, if_pos rfl, zero_sub, neg_mem_iff,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
      intro h
      have := h 1 (by norm_num)
      simp at this
  have := (hmon.irreducible_iff_irreducible_map_fraction_map (K := LaurentSeries K)).1 hirr
  simpa using this

variable (p : ℕ) [Fact p.Prime]

def redLau : Lau p →+* LaurentSeries (ZMod p) where
  toFun x := x.map (PadicInt.toZMod (p := p))
  map_one' := by
    ext i
    by_cases h : i = 0 <;> simp [h]
  map_mul' x y := HahnSeries.map_mul (PadicInt.toZMod (p := p) : ℤ_[p] →ₙ+* ZMod p)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

theorem exists_red : ∃ φ : O0 p →+* LaurentSeries (ZMod p),
    φ (qO p) = HahnSeries.single (1 : ℤ) (1 : ZMod p) ∧ φ p = 0 := by
  have hp : ((p : ℕ) : LaurentSeries (ZMod p)) = 0 := by
    rw [← map_natCast (HahnSeries.C : ZMod p →+* LaurentSeries (ZMod p))]
    simp
  have hker : ∀ a ∈ pI p, redLau p a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, map_natCast, hp, zero_mul]
  refine ⟨(Ideal.Quotient.lift (pI p) (redLau p) hker).comp
    (AdicCompletion.evalOneₐ (pI p)).toRingHom, ?_, by rw [map_natCast, hp]⟩
  have : AdicCompletion.evalOneₐ (pI p) (qO p) =
      Ideal.Quotient.mk (pI p) (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) :=
    (AdicCompletion.evalOneₐ (pI p)).commutes _
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, this,
    Ideal.Quotient.lift_mk]
  ext i
  show PadicInt.toZMod ((HahnSeries.single (1 : ℤ) (1 : ℤ_[p])).coeff i) = _
  by_cases h : i = 1 <;> simp [h]

theorem dvr_of_generators {R S F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] [Field F] (ℓ m N : ℕ) [Fact ℓ.Prime]
    (hp : Irreducible (ℓ : R)) (hinj : Function.Injective (algebraMap R S)) (x y : S) (q : R)
    (hx : aeval x (cyclotomic (ℓ ^ (m + 1)) R) = 0) (hy : y ^ N = algebraMap R S q)
    (hgen : Algebra.adjoin R {x, y} = ⊤) (φ : R →+* F) (hφ : φ ℓ = 0) (hN : N ≠ 0)
    (hirr : Irreducible (X ^ N - C (φ q))) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible (x - 1) := by
  haveI : Nontrivial S := hinj.nontrivial
  haveI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {(ℓ : R)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hp
  have hdvd : (x - 1) ∣ (ℓ : S) := by
    have h1 := sub_dvd_eval_sub x 1 ((cyclotomic (ℓ ^ (m + 1)) R).map (algebraMap R S))
    rw [eval_map_algebraMap, hx, map_cyclotomic, eval_one_cyclotomic_prime_pow, zero_sub,
      dvd_neg] at h1
    exact h1
  have hx1 : x ^ (ℓ ^ (m + 1)) = 1 := by
    obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one (ℓ ^ (m + 1)) R
    have := congrArg (aeval x) hg
    rw [map_mul, hx, zero_mul] at this
    simpa [sub_eq_zero] using this
  have hall : ∀ M : Ideal S, M.IsMaximal → x - 1 ∈ M := by
    intro M hM
    have hc : M.comap (algebraMap R S) = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
    have hpM : (ℓ : S) ∈ M := by
      have : (ℓ : R) ∈ M.comap (algebraMap R S) := by
        rw [hc, hm]; exact Ideal.mem_span_singleton_self _
      simpa using this
    haveI : IsDomain (S ⧸ M) := Ideal.Quotient.isDomain M
    haveI : CharP (S ⧸ M) ℓ := by
      refine (CharP.charP_iff_prime_eq_zero Fact.out).2 ?_
      rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]
      exact hpM
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply eq_zero_of_pow_eq_zero (n := ℓ ^ (m + 1))
    rw [map_sub, map_one, sub_pow_char_pow, ← map_pow, hx1, map_one, one_pow, sub_self]
  have hnil : ¬ IsNilpotent (x - 1) := by
    intro h
    obtain ⟨c, hc⟩ := hdvd
    have : IsNilpotent (ℓ : S) := by
      rw [hc]; exact (Commute.all _ _).isNilpotent_mul_right h
    obtain ⟨k, hk⟩ := this
    have h2 : algebraMap R S ((ℓ : R) ^ k) = algebraMap R S 0 := by simpa using hk
    exact hp.ne_zero (eq_zero_of_pow_eq_zero (hinj h2))
  refine dvr_of_span_maximal (x - 1) ?_ hall hnil
  obtain ⟨M, hM⟩ := Ideal.exists_maximal S
  have hne : Ideal.span {x - 1} ≠ ⊤ := fun h =>
    hM.ne_top (top_le_iff.1 (h ▸ (Ideal.span_singleton_le_iff_mem _).2 (hall M hM)))
  set J : Ideal S := Ideal.span {x - 1} with hJ
  haveI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hne
  have hkF : ∀ a ∈ IsLocalRing.maximalIdeal R, φ a = 0 := by
    intro a ha
    rw [hm] at ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, hφ, zero_mul]
  have hkS : ∀ a ∈ IsLocalRing.maximalIdeal R,
      ((Ideal.Quotient.mk J).comp (algebraMap R S)) a = 0 := by
    intro a ha
    rw [hm] at ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 ha
    have : ((Ideal.Quotient.mk J).comp (algebraMap R S)) (ℓ : R) = 0 := by
      rw [RingHom.comp_apply, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton.2 hdvd
    rw [map_mul, this, zero_mul]
  let φ' : IsLocalRing.ResidueField R →+* F := Ideal.Quotient.lift _ φ hkF
  let ψ : IsLocalRing.ResidueField R →+* S ⧸ J := Ideal.Quotient.lift _ _ hkS
  have hψ : ∀ r, ψ (IsLocalRing.residue R r) = Ideal.Quotient.mk J (algebraMap R S r) :=
    fun r => rfl
  let f : Polynomial (IsLocalRing.ResidueField R) := X ^ N - C (IsLocalRing.residue R q)
  have hf : Irreducible f := by
    refine Monic.irreducible_of_irreducible_map φ' f (monic_X_pow_sub_C _ hN) ?_
    have : φ' (IsLocalRing.residue R q) = φ q := rfl
    simpa [f, this] using hirr
  haveI : Fact (Irreducible f) := ⟨hf⟩
  have hroot : f.eval₂ ψ (Ideal.Quotient.mk J y) = 0 := by
    simp only [f, eval₂_sub, eval₂_pow, eval₂_X_pow, eval₂_X, eval₂_C, hψ]
    rw [← map_pow, hy, sub_self]
  let θ : AdjoinRoot f →+* S ⧸ J := AdjoinRoot.lift ψ _ hroot
  have hsurj : Function.Surjective θ := by
    intro t
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
    have hs : s ∈ Algebra.adjoin R {x, y} := hgen ▸ Algebra.mem_top
    show Ideal.Quotient.mk J s ∈ θ.range
    induction hs using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · have : Ideal.Quotient.mk J z = 1 := by
          rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
          exact Ideal.mem_span_singleton_self _
        rw [this]; exact one_mem _
      · exact ⟨AdjoinRoot.root f, AdjoinRoot.lift_root hroot⟩
    | algebraMap r => exact ⟨AdjoinRoot.of f (IsLocalRing.residue R r), AdjoinRoot.lift_of hroot⟩
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  have hfield : IsField (S ⧸ J) :=
    (RingEquiv.ofBijective θ ⟨θ.injective, hsurj⟩).symm.toMulEquiv.isField (Field.toIsField _)
  exact Ideal.Quotient.maximal_of_isField J hfield

theorem adjoin_eq_top_of_basis {R S ι κ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (b : Module.Basis (ι × κ) R S) (x y : S) (u : ι → ℕ) (v : κ → ℕ)
    (hb : ∀ i j, b (i, j) = x ^ u i * y ^ v j) : Algebra.adjoin R {x, y} = ⊤ := by
  rw [eq_top_iff]
  intro s _
  have hs : s ∈ Submodule.span R (Set.range b) := b.span_eq ▸ Submodule.mem_top
  refine (Submodule.span_le (p := (Algebra.adjoin R {x, y}).toSubmodule)).2 ?_ hs
  rintro _ ⟨⟨i, j⟩, rfl⟩
  rw [hb]
  show _ ∈ Algebra.adjoin R {x, y}
  have hx : x ∈ Algebra.adjoin R {x, y} := Algebra.subset_adjoin (by simp)
  have hy : y ∈ Algebra.adjoin R {x, y} := Algebra.subset_adjoin (by simp)
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hx _) (Subalgebra.pow_mem _ hy _)

theorem aeval_xn (n : ℕ) (g : Polynomial (O0 p)) :
    aeval (xn p n) g = Ideal.Quotient.mk (towerIdeal p n) (C g) := by
  have : aeval (xn p n) g =
      ((Ideal.Quotient.mkₐ (O0 p) (towerIdeal p n)).comp (CAlgHom (R := O0 p))) (aeval X g) := by
    rw [← aeval_algHom_apply]; rfl
  rw [this, aeval_X_left_apply]; rfl

theorem isDVR_On : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n →
    ∃ _ : IsDomain (On p n), IsDiscreteValuationRing (On p n) ∧ Irreducible (xn p n - 1) := by
  intro p hpr n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨_, hdvr, hp⟩ := GlobalTheory.T.completed_laurent_isDVR_statement p
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_basis_On_zeta_pow_mul_q_pow p (m + 1)
  obtain ⟨φ, hφq, hφp⟩ := exists_red p
  have hpos : 0 < p ^ (m + 1) := pow_pos hpr.out.pos _
  haveI : Module.Finite (O0 p) (On p (m + 1)) := Module.Finite.of_basis b
  haveI : Module.Free (O0 p) (On p (m + 1)) := Module.Free.of_basis b
  haveI : Nontrivial (On p (m + 1)) :=
    nontrivial_of_ne _ _ (b.ne_zero (⟨0, Nat.totient_pos.2 hpos⟩, ⟨0, hpos⟩))
  refine dvr_of_generators (R := O0 p) p m (p ^ (m + 1)) hp
    (FaithfulSMul.algebraMap_injective _ _) (xn p (m + 1)) (yn p (m + 1)) (qO p) ?_ ?_ ?_ φ hφp
    hpos.ne' ?_
  · rw [aeval_xn, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_insert _ _)
  · have : algebraMap (O0 p) (On p (m + 1)) (qO p) =
        Ideal.Quotient.mk (towerIdeal p (m + 1)) (C (C (qO p))) := rfl
    rw [this, yn, ← map_pow, Ideal.Quotient.eq]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  · exact adjoin_eq_top_of_basis b _ _ (fun i => (i : ℕ)) (fun j => (j : ℕ)) hb
  · rw [hφq]
    exact irreducible_X_pow_sub_param _ _ hpos

end GlobalTheory.K5.OnDVR
