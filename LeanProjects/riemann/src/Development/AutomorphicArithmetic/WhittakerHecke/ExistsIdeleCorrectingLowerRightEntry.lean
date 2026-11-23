import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem ex_idele (u : ∀ v : H.P ℚ, (H.Kv v)ˣ) (S : Finset (H.P ℚ)) :
    ∃ ζ : (A ℚ)ˣ, (ζ : A ℚ).1 = 1 ∧ ∀ v, H.cp v (ζ : A ℚ) = if v ∈ S then (u v : H.Kv v) else 1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, rfl, fun v => by simp⟩
  | insert w S hw ih =>
    obtain ⟨ζ, h1, h2⟩ := ih
    obtain ⟨g1, g2⟩ := localIdele_isSupportedAt ℚ w (u w)
    refine ⟨H.idl w (u w) * ζ, ?_, fun v => ?_⟩
    · show ((localIdele ℚ w (u w) : (A ℚ)ˣ) : A ℚ).1 * (ζ : A ℚ).1 = 1
      rw [h1, mul_one]
      funext x
      exact g1 x
    · rw [Units.val_mul, map_mul, h2 v]
      by_cases hv : v = w
      · subst hv
        have e : H.cp v ((H.idl v (u v) : (A ℚ)ˣ) : A ℚ) = u v := localIdele_snd_self ℚ v (u v)
        rw [e, if_neg hw, if_pos (Finset.mem_insert_self _ _), mul_one]
      · have e : H.cp v ((H.idl w (u w) : (A ℚ)ˣ) : A ℚ) = 1 := g2 v hv
        rw [e, one_mul]
        simp [hv]

private theorem val_bad {N : ℕ} {v : H.P ℚ} (h : Bad N v) : Valued.v (N : H.Kv v) < 1 := by
  have e : (N : H.Kv v) = FinitePlace.embedding v (algebraMap (𝓞 ℚ) ℚ (N : 𝓞 ℚ)) := by simp
  rw [e]
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 ℚ) ℚ (N : 𝓞 ℚ))
  refine lt_of_eq_of_lt this ?_
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).2 h

private theorem val_unit {N : ℕ} {k : G1 ℚ} (hk : k ∈ KK ℚ) (hs : k ∈ SS N) {v : H.P ℚ} (h : Bad N v) :
    Valued.v (H.cp v (k 1 1)) = 1 := by
  have hi : ∀ i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun i j => hk.2 v i j
  have hd := k.det_coe
  rw [Matrix.det_fin_two] at hd
  have h1 : H.cp v (k 0 0) * H.cp v (k 1 1) = 1 + H.cp v (k 0 1) * H.cp v (k 1 0) := by
    have := congrArg (H.cp v) hd
    rw [map_sub, map_mul, map_mul, map_one] at this
    exact (sub_eq_iff_eq_add.1 this)
  have h2 : Valued.v (H.cp v (k 0 1) * H.cp v (k 1 0)) < 1 := by
    rw [map_mul]
    calc _ ≤ 1 * Valued.v (H.cp v (k 1 0)) := mul_le_mul_left (hi 0 1) _
      _ < 1 := by rw [one_mul]; exact lt_of_le_of_lt (hs v) (val_bad h)
  have h3 : Valued.v (H.cp v (k 0 0)) * Valued.v (H.cp v (k 1 1)) = 1 := by
    rw [← map_mul, h1]
    exact Valuation.map_one_add_of_lt _ h2
  refine le_antisymm (hi 1 1) ?_
  calc 1 = _ := h3.symm
    _ ≤ 1 * Valued.v (H.cp v (k 1 1)) := mul_le_mul_left (hi 0 0) _
    _ = _ := one_mul _

theorem UpperTheory.exists_idele_correcting_lowerRight_entry :
    ∀ N : ℕ, 0 < N → ∀ k ∈ KK ℚ, k ∈ SS N → ∃ ζ : (A ℚ)ˣ, ζ ∈ UU ∧ ∀ v : H.P ℚ, (Bad N v → Dv N v ((ζ : A ℚ) * k 1 1 - 1)) ∧ (¬ Bad N v → H.cp v (ζ : A ℚ) = 1) := by
  intro N hN k hk hs
  have hfin : {v : H.P ℚ | Bad N v}.Finite := by
    have h0 : Ideal.span {(N : 𝓞 ℚ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hN.ne'
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have hne : ∀ v, Bad N v → H.cp v (k 1 1) ≠ 0 := fun v hv h0 => by
    have := val_unit hk hs hv
    rw [h0, map_zero] at this
    exact zero_ne_one this
  obtain ⟨ζ, h1, h2⟩ := ex_idele (fun v => if h : Bad N v then (Units.mk0 _ (hne v h))⁻¹ else 1) hfin.toFinset
  have hb : ∀ v, Bad N v → H.cp v (ζ : A ℚ) = (H.cp v (k 1 1))⁻¹ := fun v hv => by
    rw [h2 v, if_pos (hfin.mem_toFinset.2 hv), dif_pos hv]
    simp
  have hg : ∀ v, ¬ Bad N v → H.cp v (ζ : A ℚ) = 1 := fun v hv => by
    rw [h2 v, if_neg (fun h => hv (hfin.mem_toFinset.1 h))]
  refine ⟨ζ, ⟨h1, fun v => ?_⟩, fun v => ⟨fun hv => ?_, hg v⟩⟩
  · by_cases hv : Bad N v
    · rw [hb v hv, map_inv₀, val_unit hk hs hv, inv_one]
    · rw [hg v hv, map_one]
  · unfold Dv
    rw [map_sub, map_mul, map_one, hb v hv, inv_mul_cancel₀ (hne v hv), sub_self, map_zero]
    exact zero_le
