import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLocF
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinPartOneMulInvMemHeckeSplitCongruence

noncomputable section

namespace GlobalTheory.HeckeSplitGen.FinF

section Ports

open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GlobalTheory.CMPrimeIdele
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E}

theorem ev_sub (a b : AE F E) (Q : HeightOneSpectrum (𝓞 E)) : Φ (a - b) Q = Φ a Q - Φ b Q := by
  rw [map_sub]; rfl

theorem ev_one (Q : HeightOneSpectrum (𝓞 E)) : Φ 1 Q = 1 := by rw [map_one]; rfl

theorem ev_inc (hΦ : Comp Φ) (y : E) (Q : HeightOneSpectrum (𝓞 E)) :
    Φ (incA F E y) Q = algebraMap E (Q.adicCompletion E) y := by rw [hΦ.2.2.1]; rfl

theorem isSplitIdem_of_delta (hσ : IsCMExt F E σ) (hΦ : Comp Φ) {P : HeightOneSpectrum (𝓞 E)}
    (hc : cP hσ P ≠ P) {e : AE F E} (he : IsDelta Φ P e) : IsSplitIdem σ e := by
  obtain ⟨ε, hε⟩ := exists_placeIdem (F := F) (P.under (𝓞 F))
  obtain ⟨h0, h1, h2⟩ := place_comp (E := E) hΦ hε
  have he' := delta_conj hΦ hσ he
  refine ⟨delta_idem hΦ he, ?_, _, ε, hε, ?_⟩
  · refine hΦ.ext' (by rw [RingHom.map_mul, he.1, zero_mul, RingHom.map_zero]) fun Q => ?_
    rw [ev_mul, ev_zero]
    by_cases hQ : Q = P
    · subst hQ
      rw [he'.2.2 Q (Ne.symm hc), mul_zero]
    · rw [he.2.2 Q hQ, zero_mul]
  · refine hΦ.ext' (by rw [RingHom.map_add, he.1, he'.1, add_zero, h0]) fun Q => ?_
    rw [ev_add]
    by_cases hQ : Q = P
    · subst hQ
      rw [he.2.1, he'.2.2 Q (Ne.symm hc), add_zero, h1 Q rfl]
    · by_cases hQ' : Q = cP hσ P
      · subst hQ'
        rw [he.2.2 _ hQ, he'.2.1, zero_add, h1 _ (under_cP hσ P)]
      · rw [he.2.2 Q hQ, he'.2.2 Q hQ', add_zero, h2 Q fun h => (eq_or_eq_cP hσ h).elim hQ hQ']

theorem mem_modSet (hΦ : Comp Φ) {N : ℕ} (hN : 0 < N) (x : (AE F E)ˣ) (h0 : infPart F E (x : AE F E) = 1)
    (h : ∀ Q, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion E)) :
    x ∈ modSetF F E N := by
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  refine ⟨h0, ⟨finPart F E (((x : AE F E) - 1) * incA F E (N : E)⁻¹), (hΦ.2.2.2.1 _).2 fun Q => ?_, ?_⟩,
    (hΦ.2.2.2.1 _).2 fun Q => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ev_mul, ev_sub, ev_one, ev_inc hΦ, map_inv₀, map_natCast,
      Valuation.map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ (h Q).2 zero_le
  · have e : (N : AE F E) * incA F E (N : E)⁻¹ = 1 := by
      rw [← map_natCast (incA F E), ← map_mul, mul_inv_cancel₀ hN', map_one]
    have e2 : (x : AE F E) - 1 = N * (((x : AE F E) - 1) * incA F E (N : E)⁻¹) := by
      linear_combination (1 - (x : AE F E)) * e
    have e3 := congrArg (finPart F E) e2
    rwa [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, map_natCast] at e3
  · have e : Φ x Q * Φ (x⁻¹ : (AE F E)ˣ) Q = 1 := by rw [← ev_mul, Units.mul_inv, ev_one]
    have e2 := congrArg Valued.v e
    rw [Valuation.map_mul, (h Q).1, one_mul, Valuation.map_one] at e2
    exact e2.le

theorem mem_grpH_of_good (hσ : IsCMExt F E σ) (hΦ : Comp Φ) {N : ℕ} (hN : 0 < N)
    {B : Set (HeightOneSpectrum (𝓞 E))} (hB : B.Finite) : (∀ P ∈ B, cP hσ P ≠ P) → ∀ x : (AE F E)ˣ,
      infPart F E (x : AE F E) = 1 →
      (∀ Q ∉ B, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion E)) →
      x ∈ grpHF σ N := by
  induction B, hB using Set.Finite.induction_on with
  | empty =>
    exact fun _ x h0 h => Subgroup.subset_closure (Or.inr (mem_modSet hΦ hN x h0 fun Q => h Q (Set.notMem_empty Q)))
  | @insert P B _ _ ih =>
    intro hB x h0 h
    obtain ⟨e, he⟩ := exists_delta hΦ P
    have hs := isSplitIdem_of_delta hσ hΦ (hB P (Set.mem_insert _ _)) he
    have h1 : GlobalTheory.HeckeSplitAll.Fin.part hs.1 x ∈ grpHF σ N := by
      refine Subgroup.subset_closure (Or.inl (Or.inr ⟨e, hs, ?_⟩))
      change (e + cA σ e) * (e * x + (1 - e) - 1) = e * x + (1 - e) - 1
      linear_combination ((x : AE F E) - 1) * hs.1 + ((x : AE F E) - 1) * hs.2.1
    have h2 : x * (GlobalTheory.HeckeSplitAll.Fin.part hs.1 x)⁻¹ ∈ grpHF σ N := by
      refine ih (fun Q hQ => hB Q (Set.mem_insert_of_mem _ hQ)) _ ?_ fun Q hQ => ?_
      · rw [GlobalTheory.HeckeSplitAll.Fin.mul_part_inv, RingHom.map_add, RingHom.map_mul, RingHom.map_sub,
          RingHom.map_one, he.1, h0]
        simp
      · rw [GlobalTheory.HeckeSplitAll.Fin.mul_part_inv, ev_add, ev_mul, ev_sub, ev_one]
        by_cases hQP : Q = P
        · subst hQP
          rw [he.2.1]
          simp
        · rw [he.2.2 Q hQP, zero_add, sub_zero, one_mul]
          exact h Q fun h' => h'.elim hQP hQ
    simpa using mul_mem h2 h1

theorem exists_fin_idem (hΦ : Comp Φ) :
    ∃ f : AE F E, f * f = f ∧ infPart F E f = 0 ∧ finPart F E f = 1 ∧ Φ f = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have he1 : ∀ z, (e z).1 = infPart F E z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart F E z := fun z => (he z).2
  obtain ⟨f, hf⟩ := e.surjective (0, 1)
  have hf0 : infPart F E f = 0 := by rw [← he1, hf]
  have hf1 : finPart F E f = 1 := by rw [← he2, hf]
  have key : ∀ g, infPart F E g = 0 → g * f = g := fun g hg => e.injective (Prod.ext
    (by rw [he1, he1, RingHom.map_mul, hg, zero_mul]) (by rw [he2, he2, RingHom.map_mul, hf1, mul_one]))
  refine ⟨f, key f hf0, hf0, hf1, ?_⟩
  obtain ⟨g, hg0, hg1⟩ := hΦ.2.1 1
  have h4 := congrArg Φ (key g hg0)
  rwa [map_mul, hg1, one_mul] at h4

theorem exists_of_good (hσ : IsCMExt F E σ) (hΦ : Comp Φ) {N : ℕ} (hN : 0 < N)
    {B : Set (HeightOneSpectrum (𝓞 E))} (hB : B.Finite) (hB1 : ∀ P ∈ B, cP hσ P ≠ P) (x : (AE F E)ˣ)
    (h : ∀ Q ∉ B, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion E)) :
    ∃ z : (AE F E)ˣ, finPart F E (z : AE F E) = 1 ∧ x * z⁻¹ ∈ grpHF σ N := by
  obtain ⟨f, hf, hf0, hf1, hf2⟩ := exists_fin_idem hΦ
  have h3 : GlobalTheory.HeckeSplitAll.Fin.part hf x ∈ grpHF σ N := by
    refine mem_grpH_of_good hσ hΦ hN hB hB1 _ (GlobalTheory.HeckeSplitAll.Fin.map_mix_zero _ hf0 _) fun Q hQ => ?_
    have : Φ (GlobalTheory.HeckeSplitAll.Fin.part hf x : (AE F E)ˣ) = Φ x :=
      (GlobalTheory.HeckeSplitAll.Fin.map_mix_one Φ hf2 _).1
    rw [this]
    exact h Q hQ
  refine ⟨x * (GlobalTheory.HeckeSplitAll.Fin.part hf x)⁻¹, ?_, ?_⟩
  · rw [GlobalTheory.HeckeSplitAll.Fin.mul_part_inv]
    exact (GlobalTheory.HeckeSplitAll.Fin.map_mix_one _ hf1 _).2
  · rwa [mul_inv, inv_inv, mul_inv_cancel_left]

theorem exists_not_fixed (hσ : IsCMExt F E σ) : ∃ δ : 𝓞 E, cO σ δ ≠ δ := by
  by_contra h
  push_neg at h
  have hs : Function.Surjective (algebraMap F E) := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) x
    have ha : σ (a : E) = a := congrArg (fun t : 𝓞 E => (t : E)) (h a)
    have hb : σ (b : E) = b := congrArg (fun t : 𝓞 E => (t : E)) (h b)
    exact exists_of_conj_eq hσ (by rw [map_div₀, ha, hb])
  have h1 : Module.finrank F E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap F E).injective, hs⟩
  have h2 := hσ.2.2.1
  omega

theorem exists_finite_part_one_idele_split_congruence_quotient (hσ : IsCMExt F E σ) {N : ℕ} (hN : 0 < N) (x : (AE F E)ˣ) :
    ∃ z : (AE F E)ˣ, finPart F E (z : AE F E) = 1 ∧ x * z⁻¹ ∈ grpHF σ N := by
  obtain ⟨Φ, hΦ⟩ := exists_comp F E
  obtain ⟨δ, hδ⟩ := exists_not_fixed hσ
  obtain ⟨m, hm, hm'⟩ := GlobalTheory.HeckeSplitAll.Fin.exists_den (Φ x)
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hj : ∀ y : E, y ≠ 0 → ∃ u ∈ grpHF σ N, (u : AE F E) = incA F E y := fun y hy =>
    ⟨_, Subgroup.subset_closure (Or.inl (Or.inl ⟨Units.mk0 y hy, rfl⟩)), rfl⟩
  obtain ⟨a, ha, ha'⟩ := hj _ hm0
  have hx₁ : ∀ Q, Valued.v (Φ (a * x : (AE F E)ˣ) Q) ≤ 1 := fun Q => by
    rw [Units.val_mul, ha', ev_mul, ev_inc hΦ, map_natCast]
    exact hm' Q
  obtain ⟨y, hy, B, hB, hB1, hB2⟩ := GlobalTheory.HeckeSplitAll.Fin.approx_int
    ({ cO σ with invFun := cO σ, left_inv := fun t => cO_cO hσ t, right_inv := fun t => cO_cO hσ t } : 𝓞 E ≃+* 𝓞 E)
    (fun t => cO_cO hσ t) δ hδ N hN (Φ (a * x : (AE F E)ˣ))
    (Φ ((a * x)⁻¹ : (AE F E)ˣ)) (by rw [← map_mul, Units.mul_inv, map_one]) hx₁
  obtain ⟨b, hb, hb'⟩ := hj _ (inv_ne_zero hy)
  obtain ⟨z, hz, hz'⟩ := exists_of_good hσ hΦ hN hB
    (fun P hP h => hB1 P hP fun t ht => (mem_cP hσ P t).1 (h.symm ▸ ht)) (a * x * b) fun Q hQ => by
      rw [Units.val_mul, hb', ev_mul, ev_inc hΦ, map_inv₀]
      exact hB2 Q hQ
  exact ⟨z, hz, GlobalTheory.HeckeSplitAll.Fin.mem_of_mul_mem ha hb hz'⟩

end Ports

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct

theorem exists_finPart_eq_one_mul_inv_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ), 0 < N → ∀ x : (AF F ⊗[F] E)ˣ, ∃ z : (AF F ⊗[F] E)ˣ, finPartF F E (z : AF F ⊗[F] E) = 1 ∧ x * z⁻¹ ∈ GlobalTheory.HeckeSplitGen.grpHF σ N := by
  intro F E _ _ _ _ _ σ hσ N hN x
  exact exists_finite_part_one_idele_split_congruence_quotient hσ hN x

end GlobalTheory.HeckeSplitGen.FinF

end
