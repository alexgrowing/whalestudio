import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentIsUnitOneAddOrSubAdele
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Hilbert90AdeleRingTensorQuadratic

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Formalism.L2.DIV (AfE RInt h90 U1 conjId)
open Formalism.UG (sigR)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.DetClass

section Quadratic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigR_tmul (σ : E →ₐ[F] E) (x : E) (a : FiniteAdeleRing (𝓞 F) F) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (x ⊗ₜ[F] a) = σ x ⊗ₜ[F] a := rfl

theorem conj_conj (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) : c (c x) = x := by
  rcases GlobalTheory.AdLat.aut_eq_one_or_of_finrank_two c h2 hc (c * c) with h | h
  · simpa using congrArg (fun g : E ≃ₐ[F] E => g x) h
  · exact absurd (by simpa using h) hc

theorem exists_trace (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) :
    ∃ t : F, x + c x = algebraMap F E t := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have : x + c x ∈ Set.range (algebraMap F E) := by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro g
    rcases GlobalTheory.AdLat.aut_eq_one_or_of_finrank_two c h2 hc g with rfl | rfl
    · rfl
    · rw [map_add, conj_conj g h2 hc, add_comm]
  obtain ⟨t, ht⟩ := this
  exact ⟨t, ht.symm⟩

variable {σ : E →ₐ[F] E}

theorem sigR_sigR (hσ : ∀ x, σ (σ x) = x) (z : AfE F E) :
    sigR σ _ (sigR σ _ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => rw [sigR_tmul, sigR_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem exists_half_trace (htr : ∀ x, ∃ t : F, x + σ x = algebraMap F E t) (z : AfE F E) :
    ∃ t : FiniteAdeleRing (𝓞 F) F, z + sigR σ _ z = 2 * (1 : E) ⊗ₜ[F] t := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x a =>
    obtain ⟨t, ht⟩ := htr x
    refine ⟨(t / 2) • a, ?_⟩
    rw [sigR_tmul, ← TensorProduct.add_tmul, ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      two_mul, ← TensorProduct.tmul_add, ← add_smul, add_halves]
  | add x y hx hy =>
    obtain ⟨t, ht⟩ := hx
    obtain ⟨t', ht'⟩ := hy
    refine ⟨t + t', ?_⟩
    rw [map_add, TensorProduct.tmul_add, mul_add, ← ht, ← ht']; ring

theorem isUnit_two : IsUnit (2 : AfE F E) := by
  have := (IsUnit.mk0 (2 : E) two_ne_zero).map
    (Algebra.TensorProduct.includeLeftRingHom : E →+* AfE F E)
  rwa [map_ofNat] at this

theorem exists_eq_tmul_of_fixed (htr : ∀ x, ∃ t : F, x + σ x = algebraMap F E t) (z : AfE F E)
    (hz : sigR σ _ z = z) : ∃ t : FiniteAdeleRing (𝓞 F) F, z = (1 : E) ⊗ₜ[F] t := by
  obtain ⟨t, ht⟩ := exists_half_trace htr z
  refine ⟨t, isUnit_two.mul_left_cancel ?_⟩
  rw [← ht, hz, two_mul]

theorem h90_range_eq_normOne_of_isQuad (hσ : ∀ x, σ (σ x) = x) (htr : ∀ x, ∃ t : F, x + σ x = algebraMap F E t)
    (hne : ∃ y, σ y ≠ y) : (h90 σ).range = U1 σ := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have h : conjId σ (conjId σ x) = x := Units.ext (sigR_sigR hσ _)
    change x / conjId σ x * conjId σ (x / conjId σ x) = 1
    rw [map_div, h, div_mul_div_cancel, div_self']
  · intro u hu
    have hu' : (u : AfE F E) * sigR σ _ (u : AfE F E) = 1 := congrArg Units.val hu
    obtain ⟨y, hy⟩ := hne
    obtain ⟨t, ht⟩ := exists_half_trace htr (u : AfE F E)
    obtain ⟨e, he, hun⟩ := GlobalTheory.AdIdem.finite_part (𝓞 F) F t
    let κ : E →+* AfE F E := Algebra.TensorProduct.includeLeftRingHom
    let j : FiniteAdeleRing (𝓞 F) F →ₐ[F] AfE F E := Algebra.TensorProduct.includeRight
    obtain ⟨x, hx⟩ := GlobalTheory.AdLat.hilbert90_involution_of_idempotent_unit (sigR σ (FiniteAdeleRing (𝓞 F) F)) (sigR_sigR hσ) u
      (κ (y - σ y)) (j e) (j t) hu' (by
        rw [← map_neg]
        change sigR σ _ ((y - σ y) ⊗ₜ 1) = (-(y - σ y)) ⊗ₜ 1
        rw [sigR_tmul, map_sub, hσ, neg_sub])
      ((IsUnit.mk0 _ (sub_ne_zero.2 hy.symm)).map κ) isUnit_two (by rw [← map_mul, he])
      (by
        change sigR σ _ (1 ⊗ₜ e) = 1 ⊗ₜ e
        rw [sigR_tmul, map_one]) ht
      (by simpa only [map_add, map_mul, map_sub, map_one] using hun.map j)
    refine ⟨x, ?_⟩
    change x / conjId σ x = u
    rw [div_eq_iff_eq_mul]
    exact Units.ext hx

end Quadratic

section Approx

variable {L : Type} [Field L] [NumberField L]

theorem valued_natCast_le (P : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    Valued.v (n : P.adicCompletion L) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (natCast_mem (P.adicCompletionIntegers L) n)

theorem exists_nat_valued_lt (P : HeightOneSpectrum (𝓞 L)) {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ Valued.v (N : P.adicCompletion L) < γ := by
  have h1 : Valued.v ((Ideal.absNorm P.asIdeal : ℕ) : P.adicCompletion L) < 1 := by
    have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) P _).2 (Ideal.absNorm_mem P.asIdeal)
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    have e : ((algebraMap (𝓞 L) L (Ideal.absNorm P.asIdeal : ℕ) : L) : P.adicCompletion L) =
        ((Ideal.absNorm P.asIdeal : ℕ) : P.adicCompletion L) := by
      rw [map_natCast]
      exact map_natCast (algebraMap L (P.adicCompletion L)) _
    exact e ▸ h
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h1 (Units.mk0 γ hγ)
  refine ⟨Ideal.absNorm P.asIdeal ^ n, pow_pos (Nat.pos_of_ne_zero ?_) _, ?_⟩
  · exact fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · rw [Nat.cast_pow, map_pow]; exact hn

theorem exists_nat_valued_lt_finset (T : Finset (HeightOneSpectrum (𝓞 L)))
    (γ : HeightOneSpectrum (𝓞 L) → WithZero (Multiplicative ℤ)) (hγ : ∀ P, γ P ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ P ∈ T, Valued.v (N : P.adicCompletion L) < γ P := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert Q T _ ih =>
    obtain ⟨N, hN, h⟩ := ih
    obtain ⟨M, hM, h'⟩ := exists_nat_valued_lt Q (hγ Q)
    refine ⟨M * N, Nat.mul_pos hM hN, fun P hP => ?_⟩
    rw [Nat.cast_mul, map_mul]
    rcases Finset.mem_insert.1 hP with rfl | hP
    · exact (mul_le_of_le_one_right' (valued_natCast_le _ N)).trans_lt h'
    · exact (mul_le_of_le_one_left' (valued_natCast_le _ M)).trans_lt (h P hP)

def compAt (P : HeightOneSpectrum (𝓞 L)) : Ideles L →* P.adicCompletion L where
  toFun a := (a : AdeleRing (𝓞 L) L).2 P
  map_one' := rfl
  map_mul' _ _ := rfl

theorem compAt_ne_zero (P : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : compAt P a ≠ 0 :=
  ((Group.isUnit a).map (compAt P)).ne_zero

open Classical in
theorem compAt_localIdele (P Q : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    compAt P (localIdele L Q (atFin Q k)) = if Q = P then algebraMap L _ (k : L) else 1 := by
  change Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) Q
    (algebraMap L _ (k : L)) P = _
  split_ifs with h
  · subst h; simp
  · exact Function.update_of_ne (Ne.symm h) _ _

variable {F : Type} [Field F] [NumberField F] [Algebra F L]

open Classical in
theorem compAt_locF (P : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    compAt P (locF F v k) = if v = P.under (𝓞 F) then algebraMap L _ (algebraMap F L k) else 1 := by
  rw [locF, map_prod]
  simp only [compAt_localIdele, Finset.prod_ite_eq', aboveF, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    eq_comm (a := v)]
  rfl

open Classical in
theorem compAt_prod_locF (P : HeightOneSpectrum (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 F))) (k : Fˣ) :
    compAt P (∏ v ∈ S, locF F v k) =
      if P.under (𝓞 F) ∈ S then algebraMap L _ (algebraMap F L k) else 1 := by
  rw [map_prod]
  simp only [compAt_locF, Finset.prod_ite_eq']

theorem div_sub_one_lt {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {x y : K}
    (h : w (x - y) < w x) : y ≠ 0 ∧ w (x / y - 1) < 1 := by
  have hy : y ≠ 0 := by
    rintro rfl
    simp at h
  have hv : w y = w x := Valuation.map_eq_of_sub_lt _ (by rwa [Valuation.map_sub_swap])
  refine ⟨hy, ?_⟩
  rw [div_sub_one hy, map_div₀, div_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hy)), hv]
  exact h

theorem finite_compAt_ne_one (a : Ideles L) :
    {P : HeightOneSpectrum (𝓞 L) | Valued.v (compAt P a) ≠ 1}.Finite := by
  have hu : IsUnit ((a : AdeleRing (𝓞 L) L).2) :=
    a.isUnit.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
  exact (FiniteAdeleRing.isUnit_iff.1 hu).2

theorem exists_locF_approx (a : Ideles L) (T₀ : Set (HeightOneSpectrum (𝓞 L))) (hT₀ : T₀.Finite)
    (ha : ∀ N : ℕ, 0 < N → ∃ k : F, ∀ P, Valued.v (compAt P a - algebraMap L _ (algebraMap F L k)) ≤
      Valued.v (N : P.adicCompletion L)) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (k : Fˣ) (b : Ideles L), a = b * ∏ v ∈ S, locF F v k ∧
      b ∈ unitIdl L ∧ ∀ P ∈ T₀, Valued.v (compAt P b - 1) < 1 := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ P, P ∈ T₀ ∨ Valued.v (compAt P a) ≠ 1 → P.under (𝓞 F) ∈ S :=
    ⟨(hT₀.union (finite_compAt_ne_one a)).toFinset.image fun P => P.under (𝓞 F), fun P hP =>
      Finset.mem_image.2 ⟨P, (Set.Finite.mem_toFinset _).2 hP, rfl⟩⟩
  obtain ⟨N, hN, hlt⟩ := exists_nat_valued_lt_finset (S.biUnion (aboveF (L := L) F))
    (fun P => Valued.v (compAt P a)) fun P => (Valuation.ne_zero_iff _).2 (compAt_ne_zero P a)
  obtain ⟨k, hk⟩ := ha N hN
  have h1 : ∀ P, P.under (𝓞 F) ∈ S →
      Valued.v (compAt P a - algebraMap L _ (algebraMap F L k)) < Valued.v (compAt P a) := fun P hP =>
    (hk P).trans_lt (hlt P (Finset.mem_biUnion.2 ⟨_, hP, (Set.Finite.mem_toFinset _).2 rfl⟩))
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, k ≠ 0 → (u : F) = k := by
    by_cases h : k = 0
    · exact ⟨1, fun h' => absurd h h'⟩
    · exact ⟨Units.mk0 k h, fun _ => rfl⟩
  have h2 : ∀ P, P.under (𝓞 F) ∈ S → Valued.v (compAt P (a / ∏ v ∈ S, locF F v u) - 1) < 1 := by
    intro P hP
    obtain ⟨h, h'⟩ := div_sub_one_lt _ (h1 P hP)
    have hk0 : k ≠ 0 := fun h0 => h (by rw [h0, map_zero, map_zero])
    rw [map_div, compAt_prod_locF, if_pos hP, hu hk0]
    exact h'
  have h3 : ∀ P, Valued.v (compAt P (a / ∏ v ∈ S, locF F v u)) = 1 := by
    intro P
    by_cases hP : P.under (𝓞 F) ∈ S
    · have := Valuation.map_one_add_of_lt _ (h2 P hP)
      rwa [add_sub_cancel] at this
    · rw [map_div, compAt_prod_locF, if_neg hP, div_one]
      by_contra h
      exact hP (hS P (Or.inr h))
  exact ⟨S, u, a / ∏ v ∈ S, locF F v u, (div_mul_cancel _ _).symm, h3,
    fun P hP => h2 P (hS P (Or.inl hP))⟩

theorem exists_approx_of_eq_tmul (ι : AfE F L ≃+* FiniteAdeleRing (𝓞 L) L)
    (h1 : ∀ x : L, ι (x ⊗ₜ[F] 1) = algebraMap L _ x)
    (h2 : ∀ z, z ∈ RInt F L ↔ ∀ Q : HeightOneSpectrum (𝓞 L), Valued.v (ι z Q) ≤ 1)
    (a : Ideles L) (t : FiniteAdeleRing (𝓞 F) F)
    (ha : (a : AdeleRing (𝓞 L) L).2 = ι (1 ⊗ₜ[F] t)) (N : ℕ) (hN : 0 < N) :
    ∃ k : F, ∀ P, Valued.v (compAt P a - algebraMap L _ (algebraMap F L k)) ≤
      Valued.v (N : P.adicCompletion L) := by
  obtain ⟨k, r, hr, rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 t
  refine ⟨k, fun P => ?_⟩
  have hr' : (1 : L) ⊗ₜ[F] r ∈ RInt F L := Subring.subset_closure (Or.inr ⟨⟨r, hr⟩, rfl⟩)
  have e : (a : AdeleRing (𝓞 L) L).2 = algebraMap L _ (algebraMap F L k) +
      (N : FiniteAdeleRing (𝓞 L) L) * ι (1 ⊗ₜ[F] r) := by
    rw [ha, TensorProduct.tmul_add, map_add, TensorProduct.tmul_smul, map_nsmul, nsmul_eq_mul, ← h1,
      Algebra.algebraMap_eq_smul_one k, Algebra.algebraMap_eq_smul_one k, TensorProduct.smul_tmul]
  have e2 : compAt P a = algebraMap L (P.adicCompletion L) (algebraMap F L k) +
      (N : P.adicCompletion L) * ι (1 ⊗ₜ[F] r) P := by
    change (a : AdeleRing (𝓞 L) L).2 P = _
    rw [e]
    rfl
  rw [e2, add_sub_cancel_left, map_mul]
  exact mul_le_of_le_one_right' ((h2 _).1 hr' P)

theorem exists_lift {σ : L →ₐ[F] L} (htr : ∀ x, ∃ t : F, x + σ x = algebraMap F L t) (hrange : (h90 σ).range = U1 σ)
    (ι : AfE F L ≃+* FiniteAdeleRing (𝓞 L) L) (K : Subgroup (Ideles L))
    (hK : ∀ (a : Ideles L) (t : FiniteAdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 L) L).2 = ι (1 ⊗ₜ[F] t) → a ∈ K) :
    ∃ f : U1 σ →* Ideles L ⧸ K, Function.Surjective f ∧ ∀ (x : (AfE F L)ˣ) (h : h90 σ x ∈ U1 σ) (a : Ideles L),
      (a : AdeleRing (𝓞 L) L).2 = ι (x : AfE F L) → f ⟨_, h⟩ = QuotientGroup.mk a := by
  let j : (AfE F L)ˣ →* Ideles L :=
    Units.map ((MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp
      ι.toRingHom.toMonoidHom)
  have hj : ∀ x, (j x : AdeleRing (𝓞 L) L).2 = ι (x : AfE F L) := fun _ => rfl
  let g : (AfE F L)ˣ →* Ideles L ⧸ K := (QuotientGroup.mk' K).comp j
  have hg : ∀ (x : (AfE F L)ˣ) (a : Ideles L), (a : AdeleRing (𝓞 L) L).2 = ι (x : AfE F L) →
      g x = QuotientGroup.mk a := by
    intro x a ha
    refine QuotientGroup.eq.2 (hK _ 1 ?_)
    change ι ((x⁻¹ : (AfE F L)ˣ) : AfE F L) * (a : AdeleRing (𝓞 L) L).2 = _
    rw [ha, ← map_mul, Units.inv_mul]
    rfl
  let p : (AfE F L)ˣ →* U1 σ := (h90 σ).codRestrict (U1 σ) fun x => hrange ▸ ⟨x, rfl⟩
  have hp : Function.Surjective p := by
    rintro ⟨u, hu⟩
    rw [← hrange] at hu
    obtain ⟨x, rfl⟩ := hu
    exact ⟨x, rfl⟩
  have hker : p.ker ≤ g.ker := by
    intro x hx
    have hx1 : x / conjId σ x = 1 := congrArg Subtype.val hx
    have hx2 : sigR σ _ (x : AfE F L) = x := (congrArg Units.val (div_eq_one.1 hx1)).symm
    obtain ⟨t, ht⟩ := exists_eq_tmul_of_fixed htr _ hx2
    exact (QuotientGroup.eq_one_iff _).2 (hK _ t (by rw [hj, ht]))
  have hf : ∀ x, p.liftOfSurjective hp ⟨g, hker⟩ (p x) = g x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine ⟨p.liftOfSurjective hp ⟨g, hker⟩, fun d => ?_, fun x h a ha => (hf x).trans (hg x a ha)⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective d
  exact ⟨p (Units.map ((ι.symm.toRingHom.toMonoidHom).comp
    (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))) a),
    (hf _).trans (hg _ a (ι.apply_symm_apply _).symm)⟩

end Approx

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem mem_KD_of_approx (a : Ideles H.E)
    (ha : ∀ N : ℕ, 0 < N → ∃ k : H.F, ∀ P, Valued.v (compAt P a - algebraMap H.E _ (algebraMap H.F H.E k)) ≤
      Valued.v (N : P.adicCompletion H.E)) : a ∈ KD H := by
  have hfin : (⋃ k, {v | OverP H (H.g k) v}).Finite := Set.finite_iUnion fun k => by
    have h0 : Ideal.span {((H.g k : ℕ) : 𝓞 H.E)} ≠ 0 := by
      simpa using (H.g_prime k).ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  obtain ⟨S, k, b, rfl, hb, hb'⟩ := exists_locF_approx (F := H.F) a _ hfin ha
  exact mul_mem (mem_KD_of_congG H ⟨hb, fun k v hv => hb' v (Set.mem_iUnion.2 ⟨k, hv⟩)⟩)
    (prod_mem fun v _ => locF_mem_KD H v k)

open Classical in

theorem exists_detClass : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (σ : H.E →ₐ[H.F] H.E), (∀ x, σ x = H.conj x) → ∀ (ι : Formalism.L2.DIV.AfE H.F H.E ≃+* FiniteAdeleRing (𝓞 H.E) H.E), (∀ x : H.E, ι (TensorProduct.tmul H.F x 1) = algebraMap H.E _ x) → (∀ z, z ∈ Formalism.L2.DIV.RInt H.F H.E ↔ ∀ Q : HeightOneSpectrum (𝓞 H.E), Valued.v (ι z Q) ≤ 1) → (Formalism.L2.DIV.h90 σ).range = Formalism.L2.DIV.U1 σ ∧ ∃ f : Formalism.L2.DIV.U1 σ →* DtT H, Function.Surjective f ∧ ∀ (x : (Formalism.L2.DIV.AfE H.F H.E)ˣ) (h : Formalism.L2.DIV.h90 σ x ∈ Formalism.L2.DIV.U1 σ) (a : Ideles H.E), (a : AdeleRing (𝓞 H.E) H.E).2 = ι (x : Formalism.L2.DIV.AfE H.F H.E) → f ⟨_, h⟩ = QuotientGroup.mk a := by
  intro R H σ hσ ι h1 h2
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hσc : ∀ x, σ x = c x := fun x => (hσ x).trans (hc x).symm
  have hσσ : ∀ x, σ (σ x) = x := fun x => by rw [hσc, hσc, conj_conj c hcm.rank hcm.ne]
  have htr : ∀ x, ∃ t : H.F, x + σ x = algebraMap H.F H.E t := fun x => by
    rw [hσc]; exact exists_trace c hcm.rank hcm.ne x
  have hne : ∃ y, σ y ≠ y := by
    by_contra h
    push Not at h
    exact hcm.ne (AlgEquiv.ext fun y => (hσc y).symm.trans (h y))
  have hrange := h90_range_eq_normOne_of_isQuad hσσ htr hne
  exact ⟨hrange, exists_lift htr hrange ι (KD H) fun a t ha =>
    mem_KD_of_approx H a (exists_approx_of_eq_tmul ι h1 h2 a t ha)⟩

end GlobalTheory.Mem.DetClass
