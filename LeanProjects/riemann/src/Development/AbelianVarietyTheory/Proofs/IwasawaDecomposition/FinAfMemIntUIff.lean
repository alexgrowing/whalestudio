import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPowUnitsOfUnderEq

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open scoped TensorProduct

namespace GlobalTheory.Mem.ReadTwist

section General

open Formalism.L2.DIV GlobalTheory.Mem.LocTriv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem afIso_finAf_apply (a : Ideles E) (P : HeightOneSpectrum (𝓞 E)) :
    afIso F E (finAf F E a : AfE F E) P = ev P (a : AdeleRing (𝓞 E) E) := by
  rw [afIso_finAf]
  rfl

theorem mem_above {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} :
    P ∈ aboveF (L := E) F v ↔ P.under (𝓞 F) = v := by
  unfold aboveF
  rw [Set.Finite.mem_toFinset]
  rfl

theorem finAf_mem_intU_iff (a : Ideles E) : finAf F E a ∈ intU F E ↔ a ∈ unitIdl E := by
  unfold intU
  rw [Submonoid.mem_units_iff, ← map_inv]
  change (finAf F E a : AfE F E) ∈ RInt F E ∧ (finAf F E a⁻¹ : AfE F E) ∈ RInt F E ↔ _
  simp only [mem_rInt_iff, afIso_finAf]
  refine ⟨fun h P => le_antisymm (h.1 P) ?_, fun h => ⟨fun P => (h P).le, fun P => ((unitIdl E).inv_mem h P).le⟩⟩
  have h1 : (a : AdeleRing (𝓞 E) E).2 P * ((a⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2 P = 1 :=
    congrArg (fun z : AdeleRing (𝓞 E) E => z.2 P) a.mul_inv
  have h2 := congrArg (Valued.v : Valuation (P.adicCompletion E) _) h1
  rw [map_mul, map_one] at h2
  rw [← h2]
  exact mul_le_of_le_one_right' (h.2 P)

theorem local_mem_suppAt (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) :
    finAf F E (localIdele E P x) ∈ suppAt E (P.under (𝓞 F)) := by
  rw [mem_suppAt_iff]
  intro Q hQ
  rw [afIso_finAf_apply]
  exact ev_local_ne (fun e => hQ (by rw [e])) x

theorem local_mem_unitIdl {P : HeightOneSpectrum (𝓞 E)} {x : (P.adicCompletion E)ˣ} (hx : IsUnitAt P x) :
    localIdele E P x ∈ unitIdl E := fun Q => by
  change Valued.v (ev Q (localIdele E P x : AdeleRing (𝓞 E) E)) = 1
  by_cases h : Q = P
  · subst h
    rw [ev_local_self]
    exact hx
  · rw [ev_local_ne h, map_one]

theorem finAf_part {v : HeightOneSpectrum (𝓞 F)} {a : Ideles E} (ha : finAf F E a ∈ suppAt E v) :
    finAf F E (part a (aboveF (L := E) F v)) = finAf F E a := by
  refine Units.ext ((afIso F E).injective (FiniteAdeleRing.ext _ fun P => ?_))
  rw [afIso_finAf_apply]
  by_cases h : P ∈ aboveF (L := E) F v
  · rw [ev_part_mem a h, afIso_finAf_apply]
  · rw [ev_part_not_mem a h]
    exact ((mem_suppAt_iff F E v _).1 ha P fun e => h (mem_above.2 e)).symm

theorem plc_dvd_iff (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Formalism.EigenvalueLevelCeiling.plc v ∣ n ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]

theorem plc_ne_zero (v : HeightOneSpectrum (𝓞 F)) : Formalism.EigenvalueLevelCeiling.plc v ≠ 0 := fun h => by
  have h1 := (plc_dvd_iff v _).2 (Ideal.absNorm_mem v.asIdeal)
  rw [h, zero_dvd_iff] at h1
  exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h1)

theorem plc_under_eq_iff (P : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime) :
    Formalism.EigenvalueLevelCeiling.plc (P.under (𝓞 F)) = p ↔ (p : 𝓞 E) ∈ P.asIdeal := by
  have h1 : (p : 𝓞 E) ∈ P.asIdeal ↔ (p : 𝓞 F) ∈ (P.under (𝓞 F)).asIdeal := by
    rw [← map_natCast (algebraMap (𝓞 F) (𝓞 E))]
    rfl
  rw [h1, ← plc_dvd_iff, Nat.dvd_prime hp]
  refine ⟨Or.inr, fun h => h.resolve_left fun e => ?_⟩
  have h2 := (plc_dvd_iff (P.under (𝓞 F)) 1).1 (by rw [e])
  rw [Nat.cast_one] at h2
  exact (P.under (𝓞 F)).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

theorem exists_under_eq (v : HeightOneSpectrum (𝓞 F)) : ∃ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 E)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

theorem local_mem_wildAt {P : HeightOneSpectrum (𝓞 E)} {x : (P.adicCompletion E)ˣ} (hx : IsUnitAt P x)
    (h1 : Valued.v ((x : P.adicCompletion E) - 1) ≤ WithZero.exp (-1 : ℤ)) :
    finAf F E (localIdele E P x) ∈ wildAt E (P.under (𝓞 F)) := by
  refine ⟨?_, local_mem_suppAt P x⟩
  have hu := (finAf_mem_intU_iff (F := F) _).2 (local_mem_unitIdl hx)
  set y := finAf F E (localIdele E P x) with hy
  have hu1 : (y : AfE F E) ∈ RInt F E := hu.1
  have hu2 : ((y⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E := hu.2
  refine ⟨⟨⟨_, hu1⟩, ⟨_, hu2⟩, Subtype.ext y.mul_inv, Subtype.ext y.inv_mul⟩, ?_, Units.ext rfl⟩
  rw [SetLike.mem_coe, mem_kerRed]
  set p := Formalism.EigenvalueLevelCeiling.plc (P.under (𝓞 F)) with hp
  have hp0 : (p : E) ≠ 0 := Nat.cast_ne_zero.2 (plc_ne_zero _)
  have hv0 : Valued.v (algebraMap E (P.adicCompletion E) (p : E)⁻¹) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((map_ne_zero _).2 (inv_ne_zero hp0))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Valued.v (algebraMap E (P.adicCompletion E) (p : E)⁻¹) ≤ WithZero.exp (m : ℤ) := by
    refine ⟨(WithZero.log (Valued.v (algebraMap E (P.adicCompletion E) (p : E)⁻¹))).toNat, ?_⟩
    conv_lhs => rw [← WithZero.exp_log hv0]
    exact WithZero.exp_le_exp.2 (Int.self_le_toNat _)
  have hw : (p : E)⁻¹ ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) * ((y : AfE F E) - 1) ^ (m + 1) ∈ RInt F E := by
    rw [mem_rInt_iff]
    intro Q
    rw [map_mul, map_pow, map_sub, map_one, afIso_tmul_one]
    change Valued.v (algebraMap E (Q.adicCompletion E) (p : E)⁻¹ * (afIso F E (y : AfE F E) Q - 1) ^ (m + 1)) ≤ 1
    rw [hy, afIso_finAf_apply]
    by_cases h : Q = P
    · subst h
      rw [ev_local_self, map_mul, map_pow]
      refine (mul_le_mul' hm (pow_le_pow_left' h1 _)).trans ?_
      rw [← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      simp
    · rw [ev_local_ne h]
      simp
  refine ⟨m + 1, Ideal.mem_span_singleton'.2 ⟨⟨_, hw⟩, Subtype.ext ?_⟩⟩
  change (p : E)⁻¹ ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) * ((y : AfE F E) - 1) ^ (m + 1) * ((p : RInt F E) : AfE F E) =
    ((y : AfE F E) - 1) ^ (m + 1)
  have e : ((p : RInt F E) : AfE F E) = (p : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) :=
    (SubringClass.coe_natCast _ _).trans (map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E)
      (B := FiniteAdeleRing (𝓞 F) F)) p).symm
  rw [e, mul_right_comm, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hp0, mul_one,
    ← Algebra.TensorProduct.one_def, one_mul]

theorem afIso_one_tmul (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E))
    (h : a (P.under (𝓞 F)) = algebraMap F _ k) :
    afIso F E (1 ⊗ₜ[F] a) P = algebraMap E _ (algebraMap F E k) := by
  have h4 := (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2 a k P
  change ∀ n : ℕ, _ → Valued.v (afIso F E (1 ⊗ₜ[F] a) P - _) ≤ _ at h4
  by_contra hne
  have h0 := (Valuation.ne_zero_iff (Valued.v : Valuation (P.adicCompletion E) _)).2 (sub_ne_zero.2 hne)
  have h5 := h4 ((-WithZero.log (Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)))).toNat + 1)
    (by rw [h, sub_self, map_zero]; exact zero_le')
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp, WithZero.log_exp] at h5
  omega

theorem finAf_locF_mem (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    finAf F E (locF F v k) ∈ (idF F E).range := by
  refine ⟨Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom (localIdele F v (atFin v k)), Units.ext ((afIso F E).injective (FiniteAdeleRing.ext _ fun P => ?_))⟩
  rw [afIso_finAf_apply, locF, Units.coe_prod, map_prod]
  change afIso F E (1 ⊗ₜ[F] ((localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F).2) P = _
  by_cases h : P ∈ aboveF (L := E) F v
  · rw [Finset.prod_eq_single_of_mem P h (fun Q _ hQ => ev_local_ne hQ.symm _), ev_local_self]
    obtain rfl := mem_above.1 h
    exact afIso_one_tmul _ (k : F) P (ev_local_self (P.under (𝓞 F)) (atFin _ k))
  · rw [Finset.prod_eq_one fun Q hQ => ev_local_ne (fun e : P = Q => h (e ▸ hQ)) _,
      afIso_one_tmul _ 1 P ((ev_local_ne (fun e => h (mem_above.2 e)) (atFin v k)).trans (map_one _).symm),
      map_one, map_one]

variable {K : Type} [Field K] {σ : K →+* ℂ} {μ : Chr F E K} {ξ : HChar E}

theorem pow_eq_one_iff (h : Reads σ μ ξ) (a : Ideles E) (n : ℕ) : ξ.1 a ^ n = 1 ↔ μ (finAf F E a) ^ n = 1 := by
  rw [Units.ext_iff, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h a, ← map_pow, Units.val_one,
    Units.val_one, map_eq_one_iff σ σ.injective]

theorem eq_one_iff (h : Reads σ μ ξ) (a : Ideles E) : ξ.1 a = 1 ↔ μ (finAf F E a) = 1 := by
  simpa using pow_eq_one_iff h a 1

theorem inert_pow_iff (h : Reads σ μ ξ) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    (∀ y ∈ inertAt E v, μ y ^ n = 1) ↔
      ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → ∀ x, IsUnitAt P x → ξ.loc P x ^ n = 1 := by
  constructor
  · rintro hy P rfl x hx
    exact (pow_eq_one_iff h _ n).2
      (hy _ ⟨(finAf_mem_intU_iff _).2 (local_mem_unitIdl hx), local_mem_suppAt P x⟩)
  · intro hP y hy
    obtain ⟨a, rfl⟩ := finAf_surjective F E y
    rw [← finAf_part hy.2, ← pow_eq_one_iff h, part, map_prod, ← Finset.prod_pow]
    exact Finset.prod_eq_one fun P hPv => hP P (mem_above.1 hPv) _ ((finAf_mem_intU_iff a).1 hy.1 P)

theorem mem_qprime_iff (h : Reads σ μ ξ) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ Qprime μ ↔ ∃ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v ∧ ¬ ξ.UnrAt P := by
  have h1 := inert_pow_iff h v 1
  simp only [pow_one] at h1
  refine (not_congr h1).trans ?_
  simp only [not_forall, exists_prop, HChar.UnrAt]

theorem tameAt (h : Reads σ μ ξ) (hw : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ μ.ker)
    (P : HeightOneSpectrum (𝓞 E)) : ξ.TameAt P := fun x hx h1 =>
  (eq_one_iff h _).2 (hw _ (local_mem_wildAt hx (by simpa using h1)))

theorem trivOn (h : Reads σ μ ξ) (hF : (idF F E).range ≤ μ.ker) : ξ.TrivOn F := by
  constructor
  · intro v k
    have h1 := (eq_one_iff h _).2 (hF (finAf_locF_mem v k))
    rw [locF, map_prod] at h1
    rw [HChar.resFin, MonoidHom.finsetProd_apply]
    exact h1
  · intro w k
    rw [HChar.resInf, MonoidHom.finsetProd_apply]
    refine Finset.prod_eq_one fun w' _ => (eq_one_iff h (infIdele E w' (atInf w' (upF F k)))).2 ?_
    have e : finAf F E (infIdele E w' (atInf w' (upF F k))) = 1 :=
      Units.ext ((afIso F E).injective (by rw [afIso_finAf, Units.val_one, map_one]; rfl))
    rw [e, map_one]

end General

theorem isTwist_of_reads : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (K : Type) [Field K] (σ : K →+* ℂ) (S : Set ℕ) (μ : Formalism.L2.DIV.Tup H.F H.E K S) (ξ : HChar H.E), Reads σ (μ.1 : Formalism.L2.DIV.Chr H.F H.E K) ξ → IsTwist H S ξ ∧ (∀ v : HeightOneSpectrum (𝓞 H.F), v ∈ Formalism.L2.DIV.Qprime (μ.1 : Formalism.L2.DIV.Chr H.F H.E K) ↔ ∃ P : HeightOneSpectrum (𝓞 H.E), P.under (𝓞 H.F) = v ∧ ¬ ξ.UnrAt P) ∧ ∀ p : ℕ, p.Prime → (Formalism.L2.DIV.IsBaseChar p (μ.1 : Formalism.L2.DIV.Chr H.F H.E K) ↔ IsDelta (H := H) p ξ) := by
  intro R H K _ σ S μ ξ h
  obtain ⟨⟨⟨⟨-, hfin⟩, hF⟩, hw⟩, hg⟩ := μ.2
  have htw : IsTwist H S ξ := by
    refine ⟨?_, trivOn h hF, tameAt h fun v => Subgroup.mem_iInf.1 hw v, fun P hP => ?_⟩
    · obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
      exact ⟨n, hn, h.orderDvd e⟩
    · rw [← GlobalTheory.Mem.GoodPlace.goodPl_under_iff]
      by_contra hn
      exact (mem_qprime_iff h _).2 ⟨P, rfl, hP⟩ (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg _) hn)
  refine ⟨htw, mem_qprime_iff h, fun p hp => ⟨fun hb => ⟨htw.1, htw.2.1, htw.2.2.1, fun P hP => ?_, fun P hP n => ?_⟩,
    fun hd => ⟨hp, fun v => ⟨fun hv n => ?_, fun hv hq => ?_⟩⟩⟩⟩
  · by_contra hn
    exact (hb.2 _).2 (fun e => hP ((plc_under_eq_iff P hp).1 e)) ((mem_qprime_iff h _).2 ⟨P, rfl, hn⟩)
  · rw [← (hb.2 _).1 ((plc_under_eq_iff (F := H.F) P hp).2 hP) n, inert_pow_iff h]
    exact ⟨fun hx Q hQ => twist_pow_units_of_under_eq R H S ξ htw Q P hQ n hx, fun hx => hx P rfl⟩
  · rw [inert_pow_iff h]
    obtain ⟨P, rfl⟩ := exists_under_eq (E := H.E) v
    exact ⟨fun hx => (hd.ine P ((plc_under_eq_iff P hp).1 hv) n).1 (hx P rfl),
      fun hn Q hQ => (hd.ine Q ((plc_under_eq_iff (F := H.F) Q hp).1 (hQ ▸ hv)) n).2 hn⟩
  · obtain ⟨P, rfl, hP⟩ := (mem_qprime_iff h _).1 hq
    exact hP (hd.unr P fun e => hv ((plc_under_eq_iff P hp).2 e))

end GlobalTheory.Mem.ReadTwist

end
