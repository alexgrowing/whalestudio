import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host
open scoped Matrix Manifold UpperHalfPlane

namespace GlobalTheory.NewLevelInv

open UpperTheory.V.Af.GlobalFixedVectors Matrix

theorem fixed_of_loc {F : Type} [Field F] [NumberField F] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) (v : V) (ho : IsOpen {k | ρ k v = v}) :
    ∀ k ∈ KLev F 2 1, (∀ w, ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) v = v) → ρ k v = v := by
  classical
  have key : ∀ S T : Finset (HeightOneSpectrum (𝓞 F)), (∀ k ∈ KAway 2 1 T, ρ k v = v) → ∀ k ∈ KLev F 2 1,
      (∀ w ∈ T, w ∉ S → GeneralLinearGroup.map (pLoc F w) k = 1) →
      (∀ w, ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) v = v) → ρ k v = v := by
    intro S T hT
    induction S using Finset.induction_on with
    | empty => exact fun k hk h1 _ => hT k (mem_KAway.2 ⟨hk, fun w hw => h1 w hw (by simp)⟩)
    | insert w S hw ih =>
      intro k hk h1 h
      have h2 := ih (k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹) (mul_mem hk (inv_mem (loc_mem w hk)))
        (fun u hu huS => by
          by_cases huw : u = w
          · subst huw; simp [pLoc_locGL]
          · simp [pLoc_locGL_of_ne huw, h1 u hu (by simp [huw, huS])])
        (fun u => by
          by_cases huw : u = w
          · subst huw; simp [pLoc_locGL]
          · simpa [pLoc_locGL_of_ne huw] using h u)
      have h3 := h w
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h2
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) (ho.mem_nhds (by simp))
  exact fun k hk h => key S S (fun k hk => hS hk) k hk (fun w hw hw' => absurd hw hw') h

theorem local_mem_principal_congruence {N : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ)
    (hM : (N : w.adicCompletionIntegers ℚ) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ c)
    {k : GL (Fin 2) (Af ℚ)} (hk : k ∈ K1G N) : GeneralLinearGroup.map (pLoc ℚ w) k ∈ UpperTheory.V.Sd.K1 w c := by
  obtain ⟨g, hg, rfl⟩ := hk
  let p : Ohat ℚ →+* w.adicCompletionIntegers ℚ :=
    ((pLoc ℚ w).comp (Ohat ℚ).subtype).codRestrict (w.adicCompletionIntegers ℚ) fun x => GlobalFixedVectors.mem_Ohat.1 x.2 w
  refine ⟨GeneralLinearGroup.map p g, ?_, Units.ext rfl⟩
  let q := Ideal.quotientMap (I := Ideal.span {(N : ↥(Ohat ℚ))}) (IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ c) p
      ((Ideal.span_singleton_le_iff_mem _).2 (by simpa using hM))
  have h0 : ![0, 1] ᵥ* (g.val.map (Ideal.Quotient.mk (Ideal.span {(N : ↥(Ohat ℚ))}))) = ![0, 1] := hg
  change ![0, 1] ᵥ* ((g.val.map p).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ c))) = ![0, 1]
  funext j
  have h1 := congrArg q (congrFun h0 j)
  have h2 : ∀ x, q (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (p x) := fun x => rfl
  fin_cases j <;> simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, h2] using h1

theorem mem_KLev_one_of_mem_K1G (N : ℕ) {k : GL (Fin 2) (Af ℚ)} (hk : k ∈ K1G N) : k ∈ KLev ℚ 2 1 := by
  obtain ⟨g, -, rfl⟩ := hk
  refine ⟨g, ?_, rfl⟩
  haveI : Subsingleton (↥(Ohat ℚ) ⧸ Ideal.span {((1 : ℕ) : ↥(Ohat ℚ))}) := Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact MonoidHom.mem_ker.2 (Units.ext (Subsingleton.elim _ _))

theorem nat_mem_loc {F : Type} [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F)) (c : ℕ) {N : ℕ}
    (h4 : (N : 𝓞 F) ∈ q.asIdeal ^ c) :
    (N : q.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers F) ^ c := by
  have h5 : q.asIdeal.map (algebraMap (𝓞 F) (q.adicCompletionIntegers F)) ≤ IsLocalRing.maximalIdeal _ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x h1
    refine (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (q.adicCompletion F) _)).2 ?_
    have h2 : Valued.v (algebraMap (𝓞 F) (q.adicCompletion F) x) < 1 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (q.adicCompletion F)]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' q _).trans_lt ((q.valuation_lt_one_iff_mem x).2 h1)
    exact h2
  rw [← map_natCast (algebraMap (𝓞 F) (q.adicCompletionIntegers F))]
  have h6 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (q.adicCompletionIntegers F)) h4
  rw [Ideal.map_pow] at h6
  exact Ideal.pow_right_mono h5 _ h6

theorem nat_mem {M : ℕ} {w q : HeightOneSpectrum (𝓞 ℚ)} (hM : 1 ≤ M) (hd : normV w ∣ M) (hq : q ≠ w) :
    ((M / normV w : ℕ) : q.adicCompletionIntegers ℚ) ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ) ^ lev M q := by
  obtain ⟨N, hN⟩ := hd
  obtain ⟨hp, hw, -, -⟩ := places w
  have e : M / normV w = N := by rw [hN, Nat.mul_div_cancel_left _ hp.pos]
  rw [e]
  have hM0 : Ideal.span {(M : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  have h1 : q.asIdeal ^ lev M q ∣ Ideal.span {(M : 𝓞 ℚ)} := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
      Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hM0) q.associates_irreducible]
    exact le_rfl
  have h2 : Ideal.span {(M : 𝓞 ℚ)} = w.asIdeal * Ideal.span {(N : 𝓞 ℚ)} := by
    rw [hw, Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, ← hN]
  rw [h2] at h1
  have h3 : q.asIdeal ^ lev M q ∣ Ideal.span {(N : 𝓞 ℚ)} :=
    (IsCoprime.pow_left (Ideal.isCoprime_iff_sup_eq.2 (q.isMaximal.coprime_of_ne w.isMaximal
      fun h => hq (HeightOneSpectrum.ext h)))).dvd_of_dvd_mul_left h1
  have h4 : (N : 𝓞 ℚ) ∈ q.asIdeal ^ lev M q := Ideal.dvd_span_singleton.1 h3
  exact nat_mem_loc q _ h4

theorem inv_K1G : ∀ (M : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)), 1 ≤ M → normV w ∣ M → ∀ φ : TR.Sm ℚ 2, IsOpen {u | TR.finRep ℚ 2 u φ = φ} → (∀ q, q ≠ w → φ ∈ Hi.fixd (UpperTheory.V.Sd.locSm ℚ q) (UpperTheory.V.Sd.K1 q (lev M q))) → φ ∈ Hi.fixd (UpperTheory.V.Sd.locSm ℚ w) (UpperTheory.V.Sd.K1 w 0) → ∀ u ∈ K1G (M / normV w), TR.finRep ℚ 2 u φ = φ := by
  intro M w hM hd φ ho hq hw u hu
  refine fixed_of_loc _ φ ho u (mem_KLev_one_of_mem_K1G _ hu) fun q => ?_
  by_cases h : q = w
  · subst h
    exact hw _ (local_mem_principal_congruence q 0 (by simp) hu)
  · exact hq q h _ (local_mem_principal_congruence q _ (nat_mem hM hd h) hu)

end GlobalTheory.NewLevelInv

end
