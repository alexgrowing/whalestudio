import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Adelise
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UopSum
import GroundTheory.GlobalFields.LocalAtPlace

open NumberField IsDedekindDomain IsLocalRing UpperTheory.V UpperTheory.V.Sd Formalism.L2.Host Formalism.ConjugateSelfDual

section Gen

variable {O K : Type} [CommRing O] [IsLocalRing O] [Field K]

private def KK (φ : O →+* K) (n : ℕ) : Subgroup (GL (Fin 2) K) :=
  ((mirab _).comap (Matrix.GeneralLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)))).map (Matrix.GeneralLinearGroup.map φ)

private theorem mem_KK (φ : O →+* K) (n : ℕ) (g : GL (Fin 2) K) :
    g ∈ KK φ n ↔ ∃ a b c d : O, (g : Matrix (Fin 2) (Fin 2) K) = !![φ a, φ b; φ c, φ d] ∧
      IsUnit (a * d - b * c) ∧ c ∈ maximalIdeal O ^ n ∧ d - 1 ∈ maximalIdeal O ^ n := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h 0 0, h 0 1, h 1 0, h 1 1, ?_, ?_, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> rfl
    · have := (Matrix.GeneralLinearGroup.det h).isUnit
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at this
    · have h0 := congrFun hh 0
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h0
    · have h0 := congrFun hh 1
      rw [← Ideal.Quotient.eq, map_one]
      simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h0
  · rintro ⟨a, b, c, d, hg, hu, hc, hd⟩
    have hu' : IsUnit (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) O) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]; exact hu
    obtain ⟨h, hh⟩ := hu'
    refine ⟨h, ?_, ?_⟩
    · change Matrix.vecMul ![0, 1] ((h : Matrix (Fin 2) (Fin 2) O).map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) = ![0, 1]
      rw [hh]
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hc
      rw [← Ideal.Quotient.eq, map_one] at hd
      ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hc, hd]
    · apply Units.ext
      change (h : Matrix (Fin 2) (Fin 2) O).map φ = g
      rw [hh, hg]
      ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem aff_val (π : Kˣ) (u : K) : (aff π u : Matrix (Fin 2) (Fin 2) K) = !![(π : K), u; 0, 1] := rfl

private theorem le_KK (φ : O →+* K) : KK φ 1 ≤ KK φ 0 := by
  intro g hg
  obtain ⟨a, b, c, d, h, hu, -, -⟩ := (mem_KK _ _ _).1 hg
  exact (mem_KK _ _ _).2 ⟨a, b, c, d, h, hu, by simp, by simp⟩

private theorem conj_mem (φ : O →+* K) (π : Kˣ) (p : O) (hp : φ p = π) (hm : maximalIdeal O = Ideal.span {p})
    (g : GL (Fin 2) K) (hg : g ∈ KK φ 1) : aff π 0 * g * (aff π 0)⁻¹ ∈ KK φ 0 := by
  obtain ⟨a, b, c, d, h, hu, hc, -⟩ := (mem_KK _ _ _).1 hg
  rw [pow_one, hm, Ideal.mem_span_singleton'] at hc
  obtain ⟨e, rfl⟩ := hc
  refine (mem_KK _ _ _).2 ⟨a, p * b, e, d, ?_, ?_, by simp, by simp⟩
  · rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, Units.val_mul, h, aff_val, ← hp]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · convert hu using 1
    ring

private theorem unip_mem (φ : O →+* K) (π : Kˣ) (u : O) : aff π (φ u) * (aff π 0)⁻¹ ∈ KK φ 0 := by
  refine (mem_KK _ _ _).2 ⟨1, u, 0, 1, ?_, by simp, by simp, by simp⟩
  rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, aff_val, aff_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem weyl (φ : O →+* K) (π : Kˣ) : ∃ s ∈ KK φ 0,
    Matrix.GeneralLinearGroup.scalar (Fin 2) π * s = aff π 0 * (s * aff π 0 * s * s) := by
  have hu' : IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]; simp
  obtain ⟨s, hs⟩ := hu'
  refine ⟨s, (mem_KK _ _ _).2 ⟨0, 1, 1, 0, by simp [hs], by simp, by simp, by simp⟩, ?_⟩
  apply Units.ext
  simp only [Units.val_mul, hs, aff_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem scalar_comm (π : Kˣ) (g : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) π * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) π := by
  apply Units.ext
  simp only [Units.val_mul]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem gen (φ : O →+* K) (π : Kˣ) (p : O) (hp : φ p = π) (hm : maximalIdeal O = Ideal.span {p})
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) K) V) (S : Finset O) (hS : S.card ≠ 0)
    (x : V) (a b : ℂ) (hx0 : x ≠ 0) (hx : x ∈ Hi.fixd ρ (KK φ 0))
    (hT : ∑ u ∈ S, ρ (aff π (φ u)) x + ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) π * (aff π 0)⁻¹) x = (a + b) • x)
    (hz : (S.card : ℂ) • ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) π) x = (a * b) • x)
    (hb : b ≠ (S.card : ℂ) * a) :
    ∃ y : V, y ≠ 0 ∧ y ∈ Hi.fixd ρ (KK φ 1) ∧ ∑ u ∈ S, ρ (aff π (φ u)) y = a • y := by
  have hq : (S.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hS
  set q : ℂ := (S.card : ℂ) with hqdef
  have hx' : ∀ k ∈ KK φ 0, ρ k x = x := hx
  have hmul : ∀ g h v, ρ (g * h) v = ρ g (ρ h v) := fun g h v => by rw [map_mul]; rfl
  have hz' : ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) π) x = (a * b / q) • x := by
    rw [div_eq_inv_mul, ← smul_smul, ← hz, smul_smul, inv_mul_cancel₀ hq, one_smul]
  refine ⟨x - (b / q) • ρ (aff π 0)⁻¹ x, ?_, ?_, ?_⟩
  · intro h
    have h1 : x = (b / q) • ρ (aff π 0)⁻¹ x := sub_eq_zero.1 h
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_div, zero_smul] at h1
      exact hx0 h1
    have h2 : ρ (aff π 0) x = (b / q) • x := by
      conv_lhs => rw [h1]
      rw [map_smul, ← hmul, mul_inv_cancel, map_one]; rfl
    obtain ⟨s, hs, he⟩ := weyl φ π
    have h3 := congrArg (fun g => ρ g x) he
    simp only [hmul, hx' s hs, h2, map_smul, hz', smul_smul] at h3
    have h4 := smul_left_injective ℂ hx0 h3
    apply hb
    field_simp at h4
    linear_combination -h4
  · refine Submodule.sub_mem _ (fun k hk => hx' k (le_KK φ hk)) (Submodule.smul_mem _ _ fun k hk => ?_)
    have h1 := hx' _ (conj_mem φ π p hp hm k hk)
    conv_rhs => rw [← h1]
    rw [← hmul, ← hmul]
    congr 2
    group
  · have h1 : ∀ u ∈ S, ρ (aff π (φ u)) (x - (b / q) • ρ (aff π 0)⁻¹ x) = ρ (aff π (φ u)) x - (b / q) • x := by
      intro u _
      rw [map_sub, map_smul, ← hmul, hx' _ (unip_mem φ π u)]
    rw [scalar_comm, hmul, hz', map_smul] at hT
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const, eq_sub_of_add_eq hT,
      ← Nat.cast_smul_eq_nsmul ℂ, ← hqdef, smul_smul, mul_div_cancel₀ _ hq, smul_sub, smul_smul, add_smul, mul_div_assoc]
    abel

end Gen

private theorem span_unif {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (p : w.adicCompletionIntegers F) (hp : Valued.v (p : w.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    maximalIdeal (w.adicCompletionIntegers F) = Ideal.span {p} := by
  have hp0 : (p : w.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  ext x
  rw [Ideal.mem_span_singleton', IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  constructor
  · intro h
    have h1 : Valued.v (x : w.adicCompletion F) < 1 := lt_of_le_of_ne x.2 h
    have h2 : Valued.v (x : w.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) := by
      rcases eq_or_ne (Valued.v (x : w.adicCompletion F)) 0 with h0 | h0
      · rw [h0]; exact zero_le'
      rw [← WithZero.exp_log h0] at h1 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [WithZero.exp_le_exp]
      omega
    refine ⟨⟨(x : w.adicCompletion F) / p, ?_⟩, Subtype.ext (div_mul_cancel₀ _ hp0)⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hp]
    exact div_le_one_of_le₀ h2 zero_le'
  · rintro ⟨z, rfl⟩ h
    have hz : Valued.v (z : w.adicCompletion F) ≤ 1 := z.2
    have h1 : Valued.v ((z : w.adicCompletion F) * p) ≤ WithZero.exp (-1 : ℤ) := by
      rw [map_mul, hp]; exact mul_le_of_le_one_left' hz
    have h' : Valued.v ((z : w.adicCompletion F) * p) = 1 := h
    rw [h', ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega

theorem UpperTheory.V.Sd.pStab :
    UpperTheory.V.Sd.PStab := by
  classical
  intro F _ _ w V _ _ ρ x a b hx0 hx hT hz hb
  have hπ : Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    unif_spec w
  have hmem : ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) ∈ w.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨σ, hσ⟩ := (IsLocalRing.residue_surjective (R := w.adicCompletionIntegers F)).hasRightInverse
  have := Fintype.ofFinite (IsLocalRing.ResidueField (w.adicCompletionIntegers F))
  have hS : Set.BijOn (IsLocalRing.residue _) ((Finset.univ.image σ : Finset _) : Set (w.adicCompletionIntegers F)) Set.univ := by
    refine ⟨fun _ _ => trivial, ?_, fun y _ => ⟨σ y, by simp, hσ y⟩⟩
    intro a ha b hb h
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at ha hb
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    rw [hσ, hσ] at h
    rw [h]
  have hcard : (Finset.univ.image σ).card = normV w := by
    rw [Finset.card_image_of_injective _ hσ.injective, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact (Nat.card_congr (GroundTheory.Global.residueFieldEquiv w).toEquiv).symm
  have hne : (Finset.univ.image σ).card ≠ 0 :=
    Finset.card_ne_zero.2 (Finset.univ_nonempty.image σ)
  have h0 := (uopSum F w V ρ 0 x hx).2 _ hS
  rw [if_pos rfl, hT] at h0
  rw [← hcard] at hz hb
  obtain ⟨y, hy0, hy, hU⟩ := gen (w.adicCompletionIntegers F).subtype (atFin w (unif w)) ⟨_, hmem⟩ rfl
    (span_unif w ⟨_, hmem⟩ hπ) ρ _ hne x a b hx0 hx h0.symm hz hb
  refine ⟨y, hy0, hy, ?_⟩
  rw [(uopSum F w V ρ 1 y hy).2 _ hS, if_neg one_ne_zero, add_zero]
  exact hU
