import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.LocalRingCardinality.DataNChTie
import Formalism.SharpRestriction.LevelLetterCocycles.VKEqOfFrac
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemZpowersOfTameGen

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CondTieChoice

open Formalism.MainNotions.BlochKatoReduction.Gen (nval)

theorem lenUnit_quot_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) (x : O) :
    ((lenUnit (O := O) l (O ⧸ Ideal.span {x}) : ℚ) : ℝ) = Formalism.MainNotions.BlochKatoReduction.Gen.nval O l x := by
  unfold lenUnit Formalism.MainNotions.BlochKatoReduction.Gen.nval
  rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]
  push_cast
  rfl

theorem normVal_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) :
    Formalism.MainNotions.BlochKatoReduction.Gen.nval O l 0 = 0 := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  simp

theorem normVal_unit_mul {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ) (v : Rˣ) (x : R) :
    Formalism.MainNotions.BlochKatoReduction.Gen.nval R l ((v : R) * x) = Formalism.MainNotions.BlochKatoReduction.Gen.nval R l x := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]

theorem normVal_sub_one_le_zpow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) (u : Oˣ)
    (m : ℤ) (hm : u ^ m ≠ 1) :
    Formalism.MainNotions.BlochKatoReduction.Gen.nval O l ((u : O) - 1) ≤ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (((u ^ m : Oˣ) : O) - 1) := by
  have hdvd : ((u : O) - 1) ∣ (((u ^ m : Oˣ) : O) - 1) := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · rw [zpow_natCast, Units.val_pow_eq_pow_val, ← geom_sum_mul]
      exact Dvd.intro_left _ rfl
    · refine ⟨-((u ^ n)⁻¹ : Oˣ) * ∑ i ∈ Finset.range n, (u : O) ^ i, ?_⟩
      have h1 : (((u ^ (-(n : ℤ)) : Oˣ) : O) - 1) = -(((u ^ n)⁻¹ : Oˣ) : O) * (((u ^ n : Oˣ) : O) - 1) := by
        rw [zpow_neg, zpow_natCast, mul_sub, neg_mul, Units.inv_mul, mul_one]
        ring
      rw [h1, Units.val_pow_eq_pow_val, ← geom_sum_mul]
      ring
  have hne : (((u ^ m : Oˣ) : O) - 1) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hm (Units.ext (by rw [h, Units.val_one]))
  have hle := (IsDiscreteValuationRing.addVal_le_iff_dvd).2 hdvd
  have hfin : IsDiscreteValuationRing.addVal O (((u ^ m : Oˣ) : O) - 1) ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact hne
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast ENat.toNat_le_toNat hle hfin

section Tame

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}

theorem normVal_le_tameVal {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ)
    (φ : Formalism.MainNotions.BlochKatoReduction.Gen.GE N →* Rˣ) (A : ValuationSubring N.Om) (γ : Formalism.MainNotions.BlochKatoReduction.Gen.GE N)
    (hγ : γ ∈ Ine (F := D.host.E) A) (hcyc : ∀ σ ∈ Ine (F := D.host.E) A, ∃ m : ℤ, φ σ = φ γ ^ m) :
    Formalism.MainNotions.BlochKatoReduction.Gen.nval R l ((φ γ : R) - 1) ≤ Formalism.MainNotions.BlochKatoReduction.Gen.tameVal l φ A := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.tameVal
  by_cases h1 : φ γ = 1
  · have hS : {x : ℝ | ∃ σ ∈ Ine (F := D.host.E) A, φ σ ≠ 1 ∧ x = Formalism.MainNotions.BlochKatoReduction.Gen.nval R l ((φ σ : R) - 1)} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨σ, hσ, hne, -⟩
      obtain ⟨m, hm⟩ := hcyc σ hσ
      exact hne (by rw [hm, h1, one_zpow])
    rw [hS, Real.sInf_empty, h1, Units.val_one, sub_self, normVal_zero]
  · refine le_csInf ⟨_, γ, hγ, h1, rfl⟩ ?_
    rintro x ⟨σ, hσ, hne, rfl⟩
    obtain ⟨m, hm⟩ := hcyc σ hσ
    rw [hm] at hne ⊢
    exact normVal_sub_one_le_zpow l (φ γ) m hne

theorem tameVal_inv_eq {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ)
    (φ : Formalism.MainNotions.BlochKatoReduction.Gen.GE N →* Rˣ) (A : ValuationSubring N.Om) :
    Formalism.MainNotions.BlochKatoReduction.Gen.tameVal l φ⁻¹ A = Formalism.MainNotions.BlochKatoReduction.Gen.tameVal l φ A := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.tameVal
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, MonoidHom.inv_apply, ne_eq, inv_eq_one]
  have key : ∀ u : Rˣ, Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (((u⁻¹ : Rˣ) : R) - 1) = Formalism.MainNotions.BlochKatoReduction.Gen.nval R l ((u : R) - 1) := by
    intro u
    have h1 : (((u⁻¹ : Rˣ) : R) - 1) = ((-u⁻¹ : Rˣ) : R) * ((u : R) - 1) := by
      rw [Units.val_neg, neg_mul, mul_sub, Units.inv_mul, mul_one]
      ring
    rw [h1, normVal_unit_mul]
  constructor
  · rintro ⟨σ, hσ, hne, rfl⟩
    exact ⟨σ, hσ, hne, key _⟩
  · rintro ⟨σ, hσ, hne, rfl⟩
    exact ⟨σ, hσ, hne, (key _).symm⟩

end Tame

theorem normVal_eq_of_places {LL : Type} [Field LL] (vw : AddValuation LL (WithTop ℤ))
    {R1 R2 : Type} [CommRing R1] [IsDomain R1] [IsDiscreteValuationRing R1]
    [CommRing R2] [IsDomain R2] [IsDiscreteValuationRing R2]
    (e1 : LL →+* FractionRing R1) (e2 : LL →+* FractionRing R2)
    (h1 : ∀ y, 0 ≤ vw y ↔ e1 y ∈ (algebraMap R1 (FractionRing R1)).range)
    (h2 : ∀ y, 0 ≤ vw y ↔ e2 y ∈ (algebraMap R2 (FractionRing R2)).range)
    (l : ℕ) (hl1 : ((l : ℕ) : R1) ∈ IsLocalRing.maximalIdeal R1) (hl2 : ((l : ℕ) : R2) ∈ IsLocalRing.maximalIdeal R2)
    (hl10 : ((l : ℕ) : R1) ≠ 0) (hl20 : ((l : ℕ) : R2) ≠ 0)
    (x : LL) (a : R1) (b : R2) (ha : e1 x = algebraMap R1 _ a) (hb : e2 x = algebraMap R2 _ b) :
    nval R1 l a = nval R2 l b := by

  have mem : ∀ {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (e : LL →+* FractionRing R)
      (c : R), ((l : ℕ) : R) ≠ 0 → e x = algebraMap R _ c → ∀ p q : ℕ,
      (e (x ^ p * ((l : LL) ^ q)⁻¹) ∈ (algebraMap R (FractionRing R)).range ↔ ((l : ℕ) : R) ^ q ∣ c ^ p) := by
    intro R _ _ _ e c hl0 hc p q
    have hlK : (algebraMap R (FractionRing R)) (((l : ℕ) : R) ^ q) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (pow_ne_zero q hl0)
    have he : e (x ^ p * ((l : LL) ^ q)⁻¹) =
        algebraMap R (FractionRing R) (c ^ p) * (algebraMap R (FractionRing R) (((l : ℕ) : R) ^ q))⁻¹ := by
      rw [map_mul, map_pow, map_inv₀, map_pow, map_natCast, hc, map_pow, map_pow, map_natCast]
    rw [he, RingHom.mem_range]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, IsFractionRing.injective R (FractionRing R) ?_⟩
      rw [map_mul, hd, mul_comm, mul_assoc, inv_mul_cancel₀ hlK, mul_one]
    · rintro ⟨d, hd⟩
      refine ⟨d, ?_⟩
      rw [hd, map_mul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hlK, one_mul]
  have key : ∀ p q : ℕ, ((l : ℕ) : R1) ^ q ∣ a ^ p ↔ ((l : ℕ) : R2) ^ q ∣ b ^ p := by
    intro p q
    rw [← mem e1 a hl10 ha p q, ← mem e2 b hl20 hb p q, ← h1, ← h2]
  by_cases ha0 : a = 0
  · have hx : x = 0 := by
      have : e1 x = 0 := by rw [ha, ha0, map_zero]
      exact (map_eq_zero_iff e1 e1.injective).1 this
    have hb0 : b = 0 := by
      have : algebraMap R2 (FractionRing R2) b = 0 := by rw [← hb, hx, map_zero]
      exact (map_eq_zero_iff _ (IsFractionRing.injective R2 (FractionRing R2))).1 this
    rw [ha0, hb0, normVal_zero, normVal_zero]
  have hb0 : b ≠ 0 := by
    intro hb0
    apply ha0
    have hx : x = 0 := by
      have : e2 x = 0 := by rw [hb, hb0, map_zero]
      exact (map_eq_zero_iff e2 e2.injective).1 this
    have : algebraMap R1 (FractionRing R1) a = 0 := by rw [← ha, hx, map_zero]
    exact (map_eq_zero_iff _ (IsFractionRing.injective R1 (FractionRing R1))).1 this

  obtain ⟨A1, hA1⟩ : ∃ n : ℕ, IsDiscreteValuationRing.addVal R1 ((l : ℕ) : R1) = n :=
    ENat.ne_top_iff_exists.mp (by rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hl10) |>.imp fun _ h => h.symm
  obtain ⟨A2, hA2⟩ : ∃ n : ℕ, IsDiscreteValuationRing.addVal R2 ((l : ℕ) : R2) = n :=
    ENat.ne_top_iff_exists.mp (by rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hl20) |>.imp fun _ h => h.symm
  obtain ⟨B1, hB1⟩ : ∃ n : ℕ, IsDiscreteValuationRing.addVal R1 a = n :=
    ENat.ne_top_iff_exists.mp (by rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact ha0) |>.imp fun _ h => h.symm
  obtain ⟨B2, hB2⟩ : ∃ n : ℕ, IsDiscreteValuationRing.addVal R2 b = n :=
    ENat.ne_top_iff_exists.mp (by rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hb0) |>.imp fun _ h => h.symm
  have hdiv : ∀ {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (c : R) (A B : ℕ),
      IsDiscreteValuationRing.addVal R ((l : ℕ) : R) = A → IsDiscreteValuationRing.addVal R c = B →
      ∀ p q : ℕ, (((l : ℕ) : R) ^ q ∣ c ^ p ↔ q * A ≤ p * B) := by
    intro R _ _ _ c A B hA hB p q
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_pow, hA, hB, nsmul_eq_mul, nsmul_eq_mul]
    exact_mod_cast Iff.rfl
  have k2 : ∀ p q : ℕ, q * A1 ≤ p * B1 ↔ q * A2 ≤ p * B2 := by
    intro p q
    rw [← hdiv a A1 B1 hA1 hB1, ← hdiv b A2 B2 hA2 hB2]
    exact key p q
  have e1' := (k2 A1 B1).1 (by rw [mul_comm])
  have e2' := (k2 A2 B2).2 (by rw [mul_comm])
  have hA10 : A1 ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, IsDiscreteValuationRing.addVal_eq_zero_iff] at hA1
    exact (IsLocalRing.mem_maximalIdeal _).1 hl1 hA1
  have hA20 : A2 ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, IsDiscreteValuationRing.addVal_eq_zero_iff] at hA2
    exact (IsLocalRing.mem_maximalIdeal _).1 hl2 hA2
  have heq : B1 * A2 = B2 * A1 := by
    apply le_antisymm
    · linarith
    · linarith
  unfold nval
  rw [hA1, hB1, hA2, hB2, ENat.toNat_coe, ENat.toNat_coe, ENat.toNat_coe, ENat.toNat_coe,
    div_eq_div_iff (by exact_mod_cast hA10) (by exact_mod_cast hA20)]
  exact_mod_cast heq

theorem l_mem_maximalIdeal {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
    (i : X.Tw) (k' : ℕ) :
    ((X.l i : ℕ) : X.Ok i k') ∈ IsLocalRing.maximalIdeal (X.Ok i k') := by
  have : Module.Finite (X.O i) (X.Ok i k') := X.Ok_fin i k'
  obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := X.Ok i k')
    (IsLocalRing.maximalIdeal (X.O i))
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (X.Ok_inj i k')]; exact bot_le)
  rw [← IsLocalRing.eq_maximalIdeal hP, ← map_natCast (algebraMap (X.O i) (X.Ok i k')), ← Ideal.mem_comap, hPc]
  exact X.O_l i

section Main

variable {D : D7}

theorem firstTwistFactor_tameGenerator_eq_one (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ D.nd.Q i) :
    D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) (D.nd.gam0 i v) = 1 := by
  have hl : D.ntw.l (D.ntw.twOf i) = D.nd.l i := D.ntw.twOf_l i
  have hvl : v ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i v (Or.inr hv)
  have hvS : v ∉ D.nd.S i := fun h => Finset.disjoint_left.mp (D.nd.SQ_disj i) h hv
  refine D.ntw.twistCharacterFamily_unramified _ _ _ v (by rw [hl]; exact hvl) (fun k hk => ?_) (fun hp => ?_) _ (D.nd.plOm.2 v) _
    (D.nd.locNd_chebotarevPlace_mem i v)
  · apply hvS
    rw [D.nd.S_def]
    refine ⟨?_, hvl⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  · apply hvS
    rw [D.nd.S_def]
    refine ⟨Or.inr (Or.inr ?_), hvl⟩
    have h1 : v ∈ (D.ntw.pD (D.ntw.twOf i) : Set (HeightOneSpectrum (𝓞 D.host.E))) := hp
    rw [D.ntw.pD_eq, hl] at h1
    exact h1

theorem zeta_eq_locChar (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ D.nd.Q i) :
    D.nd.zeta i v = ((D.ntw.psiL i (D.nd.gam0 i v) : (D.nd.O i)ˣ) : D.nd.O i) := by
  show ((D.nd.chi i 1 (D.nd.gam0 i v) : (D.nd.O i)ˣ) : D.nd.O i) = _
  rw [D.ntw.chi_tw i, MonoidHom.mul_apply, MonoidHom.comp_apply, firstTwistFactor_tameGenerator_eq_one i v hv, map_one, one_mul]

end Main

theorem conductor_le_tameVal : ∀ (D : D7) (C : NChoice D), NChTie D C → ∀ i : D.nd.Loc, ∀ v ∈ D.nd.Q i,
    ((lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) : ℚ) : ℝ) ≤
      BlochKatoReduction.Gen.tameVal (D.ntw.l (C.twI (D.nd.w i))) (KillingConditions.psiW C (D.nd.w i)) (D.nd.plOm.1 v) := by
  intro D C hT i v hv
  obtain ⟨ψ0, -, hW, hK⟩ := hT.psi_eq
  have hl' : D.ntw.l (C.twI (D.nd.w i)) = D.nd.l i := by rw [C.twI_l, D.nd.w_l]
  have hl10 : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_ne_zero D.nd i
  have hl1 : ((D.nd.l i : ℕ) : D.nd.O i) ∈ IsLocalRing.maximalIdeal (D.nd.O i) :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_not_unit D.nd i))
  have hl2k : ((D.nd.l i : ℕ) : D.ntw.Ok (C.twI (D.nd.w i)) (C.k' (D.nd.w i))) ∈
      IsLocalRing.maximalIdeal (D.ntw.Ok (C.twI (D.nd.w i)) (C.k' (D.nd.w i))) := by
    rw [← hl']
    exact l_mem_maximalIdeal (C.twI (D.nd.w i)) (C.k' (D.nd.w i))
  haveI := C.Oe_loc (D.nd.w i)
  haveI := C.Oe_fin (D.nd.w i)
  have hl2 : ((D.nd.l i : ℕ) : C.Oe (D.nd.w i)) ∈ IsLocalRing.maximalIdeal (C.Oe (D.nd.w i)) := by
    rw [← map_natCast (algebraMap (D.ntw.Ok (C.twI (D.nd.w i)) (C.k' (D.nd.w i))) (C.Oe (D.nd.w i)))]
    refine (IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_
    exact (IsLocalRing.mem_maximalIdeal _).1 hl2k (isUnit_of_map_unit _ _ hu)
  have hlO : ((D.nd.l i : ℕ) : D.ntw.O (C.twI (D.nd.w i))) ≠ 0 := by
    intro h0
    have h1 : ((D.nd.l i : ℕ) : FractionRing (D.ntw.O (C.twI (D.nd.w i)))) = 0 := by
      rw [← map_natCast (algebraMap (D.ntw.O (C.twI (D.nd.w i))) (FractionRing (D.ntw.O (C.twI (D.nd.w i))))), h0,
        map_zero]
    exact (Nat.cast_ne_zero.2 (D.nd.lPrime i).out.ne_zero) h1
  have hl20k : ((D.nd.l i : ℕ) : D.ntw.Ok (C.twI (D.nd.w i)) (C.k' (D.nd.w i))) ≠ 0 := by
    rw [← map_natCast (algebraMap (D.ntw.O (C.twI (D.nd.w i))) (D.ntw.Ok (C.twI (D.nd.w i)) (C.k' (D.nd.w i))))]
    exact (map_ne_zero_iff _ (D.ntw.Ok_inj _ _)).2 hlO
  have hl20 : ((D.nd.l i : ℕ) : C.Oe (D.nd.w i)) ≠ 0 := by
    rw [← map_natCast (algebraMap (D.ntw.Ok (C.twI (D.nd.w i)) (C.k' (D.nd.w i))) (C.Oe (D.nd.w i)))]
    exact (map_ne_zero_iff _ (C.Oe_inj _)).2 hl20k
  set γ := D.nd.gam0 i v with hγ
  set φ := (C.psi' (D.nd.w i)).comp (D.ntw.art (C.twI (D.nd.w i)) (C.Q (D.nd.w i))) with hφ
  have hx1 : D.nd.embK i (((ψ0 (D.nd.w i) γ : (D.what₂.LL)ˣ) : D.what₂.LL) - 1) =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (((D.ntw.psiL i γ : (D.nd.O i)ˣ) : D.nd.O i) - 1) := by
    rw [map_sub, map_one, hK i γ, map_sub, map_one]
  have hx2 : C.embW (D.nd.w i) (((ψ0 (D.nd.w i) γ : (D.what₂.LL)ˣ) : D.what₂.LL) - 1) =
      algebraMap (C.Oe (D.nd.w i)) (FractionRing (C.Oe (D.nd.w i)))
        (algebraMap (D.ntw.Ok (C.twI (D.nd.w i)) (C.k' (D.nd.w i))) (C.Oe (D.nd.w i))
          (((φ γ : (D.ntw.Ok _ _)ˣ)) - 1)) := by
    rw [map_sub, map_one, hW (D.nd.w i) γ, map_sub (algebraMap (D.ntw.Ok (C.twI (D.nd.w i)) (C.k' (D.nd.w i))) (C.Oe (D.nd.w i))),
      map_one (algebraMap (D.ntw.Ok (C.twI (D.nd.w i)) (C.k' (D.nd.w i))) (C.Oe (D.nd.w i))),
      map_sub (algebraMap (C.Oe (D.nd.w i)) (FractionRing (C.Oe (D.nd.w i)))),
      map_one (algebraMap (C.Oe (D.nd.w i)) (FractionRing (C.Oe (D.nd.w i))))]
    rfl
  have htr0 := normVal_eq_of_places (D.what₂.places.val (D.nd.w i)) (D.nd.embK i) (C.embW (D.nd.w i))
    (D.nd.embK_w i) (C.embW_w (D.nd.w i)) (D.nd.l i) hl1 hl2 hl10 hl20 _ _ _ hx1 hx2
  have htr := htr0.trans (Formalism.MainNotions.TwOe.nval_map (C.Oe_inj (D.nd.w i)) (D.nd.l i) _)
  have htame : Formalism.MainNotions.BlochKatoReduction.Gen.tameVal (D.nd.l i) (KillingConditions.psiW C (D.nd.w i)) (D.nd.plOm.1 v) =
      Formalism.MainNotions.BlochKatoReduction.Gen.tameVal (D.nd.l i) φ (D.nd.plOm.1 v) := by
    unfold KillingConditions.psiW Formalism.MainNotions.BlochKatoReduction.Gen.psiAt
    split_ifs
    · rfl
    · have : (C.psi' (D.nd.w i))⁻¹.comp (D.ntw.art (C.twI (D.nd.w i)) (C.Q (D.nd.w i))) = φ⁻¹ := by
        ext g
        rfl
      rw [this, tameVal_inv_eq]
  have hcyc : ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∃ m : ℤ, φ σ = φ γ ^ m :=
    fun σ hσ => GlobalTheory.TameCycChoice.tameCyc D C hT i v hv σ hσ
  rw [lenUnit_quot_eq, zeta_eq_locChar i v hv, htr, hl', htame]
  exact normVal_le_tameVal (D.nd.l i) φ (D.nd.plOm.1 v) γ (D.nd.locNd_chebotarevPlace_mem i v) hcyc

end GlobalTheory.CondTieChoice

end
