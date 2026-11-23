import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix

namespace GlobalTheory.PrimeOrderScalar

open scoped TensorProduct

section Generic

variable {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] {T : ℕ}

theorem zsmul_eq_zero_iff (hT : T.Prime) (hM : Nat.card M = T) (n : ℤ) :
    (∀ m : M, n • m = 0) ↔ (T : ℤ) ∣ n := by
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; exact hT.ne_zero)
  constructor
  · intro h
    haveI : Nontrivial M :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hM]; exact hT.one_lt)
    obtain ⟨a, ha⟩ := exists_ne (0 : M)
    have hord : addOrderOf a = T := by
      have hdvd := addOrderOf_dvd_natCard a
      rw [hM] at hdvd
      rcases (Nat.dvd_prime hT).mp hdvd with h1 | h1
      · exfalso
        apply ha
        have := addOrderOf_nsmul_eq_zero a
        rwa [h1, one_smul] at this
      · exact h1
    rw [← hord]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr (h a)
  · rintro ⟨c, rfl⟩ m
    have hT0 : (T : ℤ) • m = 0 := by
      rw [natCast_zsmul, ← hM]
      exact card_nsmul_eq_zero'
    rw [mul_comm, mul_smul, hT0, smul_zero]

theorem exists_int_smul (hT : T.Prime) (hM : Nat.card M = T) (s : S) :
    ∃ k : ℤ, ∀ m : M, s • m = k • m := by
  haveI : Fact T.Prime := ⟨hT⟩
  haveI : IsAddCyclic M := isAddCyclic_of_prime_card hM
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := M)
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg (s • g))
  refine ⟨k, fun m => ?_⟩
  obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg m)
  rw [smul_comm s j g, ← hk, smul_comm k j g]

theorem not_isUnit_of_kills (hT : T.Prime) (hM : Nat.card M = T) {u : S}
    (hu : ∀ m : M, u • m = 0) : ¬ IsUnit u := by
  intro h
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; exact hT.ne_zero)
  haveI : Nontrivial M :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hM]; exact hT.one_lt)
  obtain ⟨a, ha⟩ := exists_ne (0 : M)
  exact ha ((h.smul_eq_zero).mp (hu a))

theorem int_dvd_of_mem {R : Type} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤) (hT : T.Prime)
    (hTI : (T : R) ∈ I) {n : ℤ} (hn : (n : R) ∈ I) : (T : ℤ) ∣ n := by
  by_contra h
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.mp hT).coprime_iff_not_dvd).mpr h
  apply hI
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a * (T : ℤ) + b * n : ℤ) : R) = 1 := by rw [hab]; simp
  rw [← h1]
  push_cast
  exact I.add_mem (I.mul_mem_left _ hTI) (I.mul_mem_left _ hn)

variable {A B : Type} [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]

theorem same_int_of_local {O : Type} [CommRing O] [IsLocalRing O] (ψ : O →+* S)
    (hT : T.Prime) (hA : Nat.card A = T) (hB : Nat.card B = T) (y : O) :
    ∃ k : ℤ, (∀ m : A, ψ y • m = k • m) ∧ ∀ m : B, ψ y • m = k • m := by
  obtain ⟨kA, hkA⟩ := exists_int_smul hT hA (ψ y)
  obtain ⟨kB, hkB⟩ := exists_int_smul hT hB (ψ y)
  have memA : y - (kA : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine not_isUnit_of_kills hT hA (u := ψ (y - kA)) (fun m => ?_) (hu.map ψ)
    rw [map_sub, map_intCast, sub_smul, hkA, Int.cast_smul_eq_zsmul, sub_self]
  have memB : y - (kB : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine not_isUnit_of_kills hT hB (u := ψ (y - kB)) (fun m => ?_) (hu.map ψ)
    rw [map_sub, map_intCast, sub_smul, hkB, Int.cast_smul_eq_zsmul, sub_self]
  have hTm : (T : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine not_isUnit_of_kills hT hB (u := ψ (T : O)) (fun m => ?_) (hu.map ψ)
    rw [map_natCast, Nat.cast_smul_eq_nsmul, ← hB]
    exact card_nsmul_eq_zero'
  have hd : ((kB - kA : ℤ) : O) ∈ IsLocalRing.maximalIdeal O := by
    have he : ((kB - kA : ℤ) : O) = (y - kA) - (y - kB) := by push_cast; ring
    rw [he]
    exact sub_mem memA memB
  have hdvd := int_dvd_of_mem (IsLocalRing.maximalIdeal.isMaximal O).ne_top hT hTm hd
  refine ⟨kA, hkA, fun m => ?_⟩
  have h0 := (zsmul_eq_zero_iff hT hB (kB - kA)).mpr hdvd m
  rw [sub_smul, sub_eq_zero] at h0
  rw [hkB, h0]

theorem same_int_of_mul (hT : T.Prime) (hA : Nat.card A = T) (hB : Nat.card B = T)
    (X C D : S) (δ γ : ℤ) (hDA : ∀ m : A, D • m = δ • m) (hDB : ∀ m : B, D • m = δ • m)
    (hCA : ∀ m : A, C • m = γ • m) (hCB : ∀ m : B, C • m = γ • m)
    (hXA : ∀ m : A, D • X • m = C • m) (hXB : ∀ m : B, D • X • m = C • m)
    (hδ : ¬ (T : ℤ) ∣ δ) :
    ∃ k : ℤ, (∀ m : A, X • m = k • m) ∧ ∀ m : B, X • m = k • m := by
  obtain ⟨kA, hkA⟩ := exists_int_smul hT hA X
  obtain ⟨kB, hkB⟩ := exists_int_smul hT hB X
  have h1 : (T : ℤ) ∣ δ * kA - γ := by
    refine (zsmul_eq_zero_iff hT hA _).mp fun m => ?_
    have := hXA m
    rw [hkA, hDA, hCA, smul_smul] at this
    rw [sub_smul, this, sub_self]
  have h2 : (T : ℤ) ∣ δ * kB - γ := by
    refine (zsmul_eq_zero_iff hT hB _).mp fun m => ?_
    have := hXB m
    rw [hkB, hDB, hCB, smul_smul] at this
    rw [sub_smul, this, sub_self]
  have h3 : (T : ℤ) ∣ δ * (kB - kA) := by
    have he : δ * (kB - kA) = (δ * kB - γ) - (δ * kA - γ) := by ring
    rw [he]
    exact dvd_sub h2 h1
  have h4 : (T : ℤ) ∣ kB - kA :=
    ((Nat.prime_iff_prime_int.mp hT).dvd_or_dvd h3).resolve_left hδ
  refine ⟨kA, hkA, fun m => ?_⟩
  have h0 := (zsmul_eq_zero_iff hT hB (kB - kA)).mpr h4 m
  rw [sub_smul, sub_eq_zero] at h0
  rw [hkB, h0]

end Generic

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

noncomputable def inclW (w : HeightOneSpectrum (𝓞 F)) :
    w.adicCompletionIntegers F →+* intV E w :=
  ((Algebra.TensorProduct.includeRight (R := F) (A := E)
      (B := w.adicCompletion F)).toRingHom.comp
    (w.adicCompletionIntegers F).subtype).codRestrict (intV E w)
    (fun y => Subring.subset_closure (Or.inr ⟨⟨y.1, y.2⟩, rfl⟩))

noncomputable def inclO (w : HeightOneSpectrum (𝓞 F)) : 𝓞 E →+* intV E w :=
  ((Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E)
      (B := w.adicCompletion F)).comp (algebraMap (𝓞 E) E)).codRestrict (intV E w)
    (fun o => Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E o, ⟨o, rfl⟩⟩, rfl⟩))

theorem coe_inclW (w : HeightOneSpectrum (𝓞 F)) (y : w.adicCompletionIntegers F) :
    ((inclW (E := E) w y : intV E w) : E ⊗[F] w.adicCompletion F) = (1 : E) ⊗ₜ (y : w.adicCompletion F) :=
  rfl

theorem coe_inclO (w : HeightOneSpectrum (𝓞 F)) (o : 𝓞 E) :
    ((inclO w o : intV E w) : E ⊗[F] w.adicCompletion F) = (o : E) ⊗ₜ (1 : w.adicCompletion F) :=
  rfl

theorem inclW_algebraMap (w : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) :
    ((inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d) : intV E w) :
      E ⊗[F] w.adicCompletion F) = algebraMap F E (d : F) ⊗ₜ (1 : w.adicCompletion F) := by
  rw [coe_inclW, ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  rfl

theorem isUnit_algebraMap (w : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) (hd : d ∉ w.asIdeal) :
    IsUnit (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
    HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact hd

end Local

section Main

theorem sub_kill_eq {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] (P P' X X' : S)
    (hP : ∀ m : M, P • m = 0) (m : M) : ((P + P') * X) • m = (X * P' + X' * P) • m := by
  simp only [add_mul, add_smul, mul_smul, hP, smul_zero, zero_add, add_zero]
  exact smul_comm _ _ _

theorem acts_by_same_integer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)), (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → ∀ (T : ℕ), T.Prime → (T : 𝓞 F) ∈ w.asIdeal → ∀ (p : 𝓞 E), (∀ d : 𝓞 F, algebraMap F E (d : F) = (p : E) + σ (p : E) → d ∉ w.asIdeal) → ∀ (A B : Type) [AddCommGroup A] [Module (intV E w) A] [AddCommGroup B] [Module (intV E w) B], Nat.card A = T → Nat.card B = T → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : A, a • m = 0) → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : B, a • m = 0) → ∀ s : intV E w, ∃ k : ℤ, (∀ m : A, s • m = k • m) ∧ ∀ m : B, s • m = k • m := by
  intro F E _ _ _ _ _ σ w hinv hfix T hT hTw p hd A B _ _ _ _ hA hB hpA hpB s
  let Q : intV E w → Prop := fun s =>
    ∃ k : ℤ, (∀ m : A, s • m = k • m) ∧ ∀ m : B, s • m = k • m
  have hadd : ∀ a b, Q a → Q b → Q (a + b) := by
    rintro a b ⟨k1, h1A, h1B⟩ ⟨k2, h2A, h2B⟩
    exact ⟨k1 + k2, fun m => by rw [add_smul, add_smul, h1A, h2A],
      fun m => by rw [add_smul, add_smul, h1B, h2B]⟩
  have hmul : ∀ a b, Q a → Q b → Q (a * b) := by
    rintro a b ⟨k1, h1A, h1B⟩ ⟨k2, h2A, h2B⟩
    refine ⟨k1 * k2, fun m => ?_, fun m => ?_⟩
    · rw [mul_smul, h2A, smul_comm, h1A, smul_smul, mul_comm]
    · rw [mul_smul, h2B, smul_comm, h1B, smul_smul, mul_comm]
  have hneg : ∀ a, Q a → Q (-a) := by
    rintro a ⟨k, hkA, hkB⟩
    exact ⟨-k, fun m => by rw [neg_smul, neg_smul, hkA], fun m => by rw [neg_smul, neg_smul, hkB]⟩
  have h0 : Q 0 := ⟨0, fun m => by simp, fun m => by simp⟩
  have h1 : Q 1 := ⟨1, fun m => by simp, fun m => by simp⟩
  have hW : ∀ y, Q (inclW w y) := fun y => same_int_of_local (inclW w) hT hA hB y
  have hσint : ∀ o : 𝓞 E, IsIntegral ℤ (σ (o : E)) := fun o => map_isIntegral_int σ o.2
  let σO : 𝓞 E → 𝓞 E := fun o => ⟨σ (o : E), hσint o⟩
  have hdesc : ∀ e : E, IsIntegral ℤ e → σ e = e → ∃ f : 𝓞 F, algebraMap F E (f : F) = e := by
    intro e he hσe
    obtain ⟨f, hf⟩ := hfix e hσe
    have hfi : IsIntegral ℤ f :=
      (isIntegral_algebraMap_iff (algebraMap F E).injective).mp (hf ▸ he)
    exact ⟨⟨f, hfi⟩, hf⟩
  have hE : ∀ o : 𝓞 E, Q (inclO w o) := by
    intro o
    obtain ⟨d', hd'⟩ := hdesc ((p : E) + σ p) (IsIntegral.add p.2 (hσint p))
      (by rw [map_add, hinv, add_comm])
    obtain ⟨c', hc'⟩ := hdesc ((o : E) * σ p + σ o * p)
      (IsIntegral.add (IsIntegral.mul o.2 (hσint p)) (IsIntegral.mul (hσint o) p.2))
      (by rw [map_add, map_mul, map_mul, hinv, hinv]; ring)
    obtain ⟨δ, hδA, hδB⟩ := hW (algebraMap (𝓞 F) _ d')
    obtain ⟨γ, hγA, hγB⟩ := hW (algebraMap (𝓞 F) _ c')
    have hD : inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d') =
        inclO w p + inclO w (σO p) := by
      rw [← map_add]
      apply Subtype.ext
      rw [inclW_algebraMap, coe_inclO, hd']
      rfl
    have hC : inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) c') =
        inclO w o * inclO w (σO p) + inclO w (σO o) * inclO w p := by
      rw [← map_mul, ← map_mul, ← map_add]
      apply Subtype.ext
      rw [inclW_algebraMap, coe_inclO, hc']
      rfl
    have hPA : ∀ m : A, inclO w p • m = 0 := hpA _ rfl
    have hPB : ∀ m : B, inclO w p • m = 0 := hpB _ rfl
    have hXA : ∀ m : A, inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d') • inclO w o • m =
        inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) c') • m := by
      intro m
      rw [← mul_smul, hD, hC]
      exact sub_kill_eq _ _ _ _ hPA m
    have hXB : ∀ m : B, inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d') • inclO w o • m =
        inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) c') • m := by
      intro m
      rw [← mul_smul, hD, hC]
      exact sub_kill_eq _ _ _ _ hPB m
    have hδ : ¬ (T : ℤ) ∣ δ := fun h =>
      not_isUnit_of_kills hT hA (u := inclW w (algebraMap (𝓞 F) _ d'))
        (fun m => by rw [hδA]; exact (zsmul_eq_zero_iff hT hA δ).mpr h m)
        ((isUnit_algebraMap w d' (hd d' hd')).map _)
    exact same_int_of_mul hT hA hB _ _ _ δ γ hδA hδB hγA hγB hXA hXB hδ
  have key : ∀ z (hz : z ∈ intV E w), Q ⟨z, hz⟩ := by
    intro z hz
    refine Subring.closure_induction (p := fun z hz => Q ⟨z, hz⟩) ?_ h0 h1
      (fun x y hx hy qx qy => hadd _ _ qx qy) (fun x hx qx => hneg _ qx)
      (fun x y hx hy qx qy => hmul _ _ qx qy) hz
    rintro x (⟨⟨_, o, rfl⟩, rfl⟩ | ⟨y, rfl⟩)
    · exact hE o
    · exact hW ⟨y.1, y.2⟩
  exact key s.1 s.2

end Main

end GlobalTheory.PrimeOrderScalar
