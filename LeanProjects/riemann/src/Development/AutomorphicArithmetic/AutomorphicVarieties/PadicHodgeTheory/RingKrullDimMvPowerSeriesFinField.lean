import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PiSpanVariable
open IsLocalRing UpperTheory.V.Alg

private theorem dim_ge (E : Type) [Field E] (n : ℕ) :
    ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin n) E) := by
  induction n with
  | zero => simpa using (ringKrullDim_nonneg_of_nontrivial (R := MvPowerSeries (Fin 0) E))
  | succ n ih =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPowerSeries.finSuccEquiv E n).toRingEquiv]
    refine le_trans ?_ ringKrullDim_succ_le_ringKrullDim_powerseries
    push_cast at ih ⊢
    gcongr

private theorem mem_max_iff (E : Type) [Field E] (σ : Type) (g : MvPowerSeries σ E) :
    g ∈ maximalIdeal (MvPowerSeries σ E) ↔ MvPowerSeries.constantCoeff g = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
  simp

open MvPowerSeries in
private theorem pi_span_X {O σ : Type} [CommRing O] (s : Finset σ) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → coeff n f = 0) →
      f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X s

private theorem max_eq_span (E : Type) [Field E] (σ : Type) [Finite σ] :
    maximalIdeal (MvPowerSeries σ E) ≤
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ E)) := by
  intro g hg
  rw [mem_max_iff] at hg
  cases nonempty_fintype σ
  refine pi_span_X Finset.univ g fun n hn => ?_
  have : n = 0 := by ext i; exact hn i (Finset.mem_univ i)
  subst this
  simpa using hg

theorem UpperTheory.ringKrullDim_mvPowerSeries_fin_field :
    ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (S : Type) [CommRing S] [Algebra O S] [IsNoetherianRing S] (x : S →ₐ[O] O) (n : ℕ) (φ : S →ₐ[O] MvPowerSeries (Fin n) E) (t : Fin n → S) (c : O), c ≠ 0 → (∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) → (∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2) → (n : ℕ∞) ≤ (RingHom.ker x).height := by
  intro O E _ _ _ _ _ S _ _ _ x n φ t c hc hx ht
  have hinj := IsFractionRing.injective O E
  letI : Algebra S (MvPowerSeries (Fin n) E) := φ.toRingHom.toAlgebra
  have halg : ∀ a, algebraMap S (MvPowerSeries (Fin n) E) a = φ a := fun _ => rfl
  set m := maximalIdeal (MvPowerSeries (Fin n) E) with hm
  have hker : ∀ a, a ∈ RingHom.ker x ↔ φ a ∈ m := fun a => by
    rw [hm, mem_max_iff, hx, RingHom.mem_ker, map_eq_zero_iff _ hinj]
  haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  haveI : m.LiesOver (RingHom.ker x) := ⟨by
    ext a
    rw [hker, Ideal.under_def, Ideal.mem_comap, halg]⟩
  have hX : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ∈ m := fun i => by
    rw [hm, mem_max_iff]; simp
  have hsm : ∀ g : MvPowerSeries (Fin n) E, c • g = MvPowerSeries.C (algebraMap O E c) * g := by
    intro g
    rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply]
  have hc' : algebraMap O E c ≠ 0 := (map_ne_zero_iff _ hinj).2 hc
  have htm : ∀ i, t i ∈ RingHom.ker x := fun i => by
    rw [hker]
    have h1 : φ (t i) - c • MvPowerSeries.X i ∈ m := Ideal.pow_le_self two_ne_zero (ht i)
    have h2 : c • (MvPowerSeries.X i : MvPowerSeries (Fin n) E) ∈ m := by
      rw [hsm]; exact m.mul_mem_left _ (hX i)
    simpa using m.add_mem h1 h2
  set J := (RingHom.ker x).map (algebraMap S (MvPowerSeries (Fin n) E)) with hJ
  have hle : m ≤ J := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := m) (IsNoetherian.noetherian _) ?_ ?_
    · rw [hm, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    · refine (max_eq_span E (Fin n)).trans ?_
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : φ (t i) ∈ J ⊔ m • m := Submodule.mem_sup_left (Ideal.mem_map_of_mem _ (htm i))
      have h2 : φ (t i) - c • MvPowerSeries.X i ∈ J ⊔ m • m := by
        refine Submodule.mem_sup_right ?_
        rw [smul_eq_mul, ← pow_two]; exact ht i
      have h3 := Ideal.mul_mem_left _ (MvPowerSeries.C (algebraMap O E c)⁻¹) (Submodule.sub_mem _ h1 h2)
      rw [sub_sub_cancel, hsm, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc', map_one, one_mul] at h3
      exact h3
  have h := Ideal.height_le_height_add_of_liesOver (RingHom.ker x) m
  have h0 : m.map (Ideal.Quotient.mk J) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]; exact hle
  have hJm : J ≤ m := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    intro a ha
    exact (hker a).1 ha
  haveI : Nontrivial (MvPowerSeries (Fin n) E ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hJm)
  rw [← hJ, h0, Ideal.height_bot, add_zero] at h
  refine le_trans ?_ h
  have hd := dim_ge E n
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at hd
  exact WithBot.coe_le_coe.1 hd
