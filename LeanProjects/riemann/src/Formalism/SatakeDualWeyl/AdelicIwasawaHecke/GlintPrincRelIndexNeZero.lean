import Formalism.SatakeDualWeyl.Statement
import Lemmata.NearbyExistence.ExistsNear

namespace Formalism.UG.P

open Formalism.UG

section Generic

variable {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]

theorem glint_mem_range_of_integral (O : Subring L) (U : GL n L)
    (h1 : (U : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (h2 : ((U⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range) :
    U ∈ (bc (n := n) O.subtype).range := by
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := h2
  have inj : Function.Injective (RingHom.mapMatrix (m := n) O.subtype) := by
    intro X Y h
    ext i j
    simpa using congrFun (congrFun h i) j
  have hAB : A * B = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])
  have hBA : B * A = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  ext : 1
  simp only [bc, Units.coe_map]
  exact hA

theorem glint_conj_integral (O : Subring L) (g : GL n L) (c : O)
    (hg : (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (hg' : (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (h : GL n O) (hh : redGL (n := n) (Ideal.span {c * c}) h = 1) :
    ((g⁻¹ * bc (n := n) O.subtype h * g : GL n L) : Matrix n n L) ∈
      (RingHom.mapMatrix (m := n) O.subtype).range := by
  have hm : RingHom.mapMatrix (m := n) (Ideal.Quotient.mk (Ideal.span {c * c})) (h : Matrix n n O) =
      RingHom.mapMatrix (m := n) (Ideal.Quotient.mk (Ideal.span {c * c})) 1 := by
    rw [map_one]; exact congrArg Units.val hh
  have hent : ∀ a b, (h : Matrix n n O) a b - (1 : Matrix n n O) a b ∈ Ideal.span {c * c} := by
    intro a b
    rw [← Ideal.Quotient.eq]
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun hm a) b
  choose e he using fun a b => Ideal.mem_span_singleton'.1 (hent a b)
  let E : Matrix n n O := Matrix.of e
  have hL : ∀ a b, (((h : Matrix n n O) a b : O) : L) =
      (1 : Matrix n n L) a b + (c : L) * (c : L) * ((e a b : O) : L) := by
    intro a b
    have h1 := he a b
    rw [Matrix.one_apply] at h1 ⊢
    split_ifs at h1 ⊢ with hab
    · have := congrArg Subtype.val h1
      push_cast at this
      linear_combination -this
    · have := congrArg Subtype.val h1
      push_cast at this
      linear_combination -this
  have hkey : ((bc (n := n) O.subtype h : GL n L) : Matrix n n L) =
      1 + ((c : L) * (c : L)) • RingHom.mapMatrix (m := n) O.subtype E := by
    ext a b
    simp only [bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      E, Matrix.of_apply, Subring.coe_subtype]
    exact hL a b
  have hcalc : ((g⁻¹ * bc (n := n) O.subtype h * g : GL n L) : Matrix n n L) =
      1 + ((c : L) • ((g⁻¹ : GL n L) : Matrix n n L)) * RingHom.mapMatrix (m := n) O.subtype E *
        ((c : L) • (g : Matrix n n L)) := by
    rw [Units.val_mul, Units.val_mul, hkey, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [hcalc]
  exact add_mem (one_mem _) (mul_mem (mul_mem hg' ⟨E, rfl⟩) hg)

theorem glint_princ_le_map_conj (O : Subring L) (g : GL n L) (c : O)
    (hg : (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (hg' : (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range) :
    princ (n := n) O.subtype (Ideal.span {c * c}) ≤
      (GLint n O).map (MulAut.conj g).toMonoidHom := by
  intro k hk
  simp only [princ, congPre] at hk
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hk
  have hh' : redGL (n := n) (Ideal.span {c * c}) h = 1 := by
    simpa only [Subgroup.mem_comap, Subgroup.mem_bot] using hh
  have hh'' : redGL (n := n) (Ideal.span {c * c}) h⁻¹ = 1 := by rw [map_inv, hh', inv_one]
  refine Subgroup.mem_map.2 ⟨g⁻¹ * bc (n := n) O.subtype h * g, ?_, ?_⟩
  · apply glint_mem_range_of_integral
    · exact glint_conj_integral O g c hg hg' h hh'
    · have : (g⁻¹ * bc (n := n) O.subtype h * g)⁻¹ = g⁻¹ * bc (n := n) O.subtype h⁻¹ * g := by
        rw [map_inv]; group
      rw [this]
      exact glint_conj_integral O g c hg hg' h⁻¹ hh''
  · simp [MulAut.conj_apply, mul_assoc]

theorem glint_princ_relIndex_ne_zero (O : Subring L) (I : Ideal O) [Finite (O ⧸ I)] :
    (princ (n := n) O.subtype I).relIndex (bc (n := n) O.subtype).range ≠ 0 := by
  classical
  have : Finite (Matrix n n (O ⧸ I)) := inferInstanceAs (Finite (n → n → O ⧸ I))
  have hN : (redGL (n := n) I).ker.index ≠ 0 := by
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  have hsup : ((redGL (n := n) I).ker ⊔ (bc (n := n) O.subtype).ker).index ≠ 0 := by
    intro h
    apply hN
    have hd := Subgroup.index_dvd_of_le
      (le_sup_left : (redGL (n := n) I).ker ≤ (redGL (n := n) I).ker ⊔ (bc (n := n) O.subtype).ker)
    rw [h] at hd
    exact Nat.eq_zero_of_zero_dvd hd
  have hprinc : princ (n := n) O.subtype I = ((redGL (n := n) I).ker).map (bc (n := n) O.subtype) := by
    unfold princ congPre
    rw [MonoidHom.comap_bot]
  rw [hprinc, MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
    Subgroup.relIndex_top_right]
  exact hsup

theorem glint_exists_denom (A : ValuationSubring L) (g : GL n L) :
    ∃ c : A.toSubring, c ≠ 0 ∧
      (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) A.toSubring.subtype).range ∧
      (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈
        (RingHom.mapMatrix (m := n) A.toSubring.subtype).range := by
  classical
  let f : (n × n) ⊕ (n × n) → L := fun i => match i with
    | .inl p => (g : Matrix n n L) p.1 p.2
    | .inr p => ((g⁻¹ : GL n L) : Matrix n n L) p.1 p.2
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) f
  have hmem : ∀ i, (b : L) * f i ∈ A := by
    intro i
    obtain ⟨y, hy⟩ := hb i
    rw [Algebra.smul_def] at hy
    have : (b : L) * f i = (y : L) := hy.symm
    rw [this]; exact y.2
  refine ⟨⟨(b : A), (b : A).2⟩, ?_, ?_, ?_⟩
  · intro h0
    apply nonZeroDivisors.ne_zero b.2
    exact Subtype.ext (congrArg Subtype.val h0)
  · refine ⟨Matrix.of fun i j => ⟨(b : L) * (g : Matrix n n L) i j, hmem (.inl (i, j))⟩, ?_⟩
    ext i j
    simp
  · refine ⟨Matrix.of fun i j => ⟨(b : L) * ((g⁻¹ : GL n L) : Matrix n n L) i j,
      hmem (.inr (i, j))⟩, ?_⟩
    ext i j
    simp

end Generic

section Adic

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem glint_exists_approx (x : v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, Valued.v ((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 := by
  first | exact Bl.NearbyExistence.goal1 .. | (apply Bl.NearbyExistence.goal1 <;> assumption) | (intros; apply Bl.NearbyExistence.goal1 <;> assumption) | (apply @Bl.NearbyExistence.goal1 <;> assumption) | (intros; apply @Bl.NearbyExistence.goal1 <;> assumption) | (apply @Bl.NearbyExistence.goal1 <;> first | assumption | infer_instance)

theorem glint_finite_residueField :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  let φ : 𝓞 F →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
  have hmem : ∀ y : v.adicCompletionIntegers F, Valued.v (y : v.adicCompletion F) < 1 →
      y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := fun y hy =>
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰))).2 hy
  have hker : ∀ r ∈ v.asIdeal, φ r = 0 := by
    intro r hr
    simp only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    apply hmem
    rw [algebraMap_adicCompletionIntegers_apply, adicCompletion.valued_coe (K := F) (v := v),
      valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem v r).2 hr
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, hr⟩ := glint_exists_approx v x
    refine ⟨r, ?_⟩
    simp only [φ, RingHom.comp_apply]
    show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    apply hmem
    have e : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) r - x : v.adicCompletionIntegers F) :
        v.adicCompletion F) = -((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) := by
      rw [AddSubgroupClass.coe_sub, neg_sub, algebraMap_adicCompletionIntegers_apply,
        IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), algebraMap_adicCompletion]
      rfl
    rw [e, Valuation.map_neg]
    exact hr
  have := v.isMaximal
  have hs : Function.Surjective (Ideal.Quotient.lift v.asIdeal φ hker) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  exact Finite.of_surjective _ hs

theorem glint_finite_quotient_of_dvr {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (h : Finite (IsLocalRing.ResidueField R)) (I : Ideal R) (hI : I ≠ ⊥) : Finite (R ⧸ I) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have key : ∀ k : ℕ, Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, Ideal.one_eq_top]
      exact Finite.of_fintype (R ⧸ ⊤)
    | succ k ih =>
      have hle : IsLocalRing.maximalIdeal R ^ (k + 1) ≤ IsLocalRing.maximalIdeal R ^ k :=
        Ideal.pow_le_pow_right (by simp)
      replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE hle).symm.toEquiv
      suffices Finite (Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))
          (IsLocalRing.maximalIdeal R ^ k)) from
        .of_ideal_quotient (.map (Ideal.Quotient.mk _) (IsLocalRing.maximalIdeal R ^ k))
      exact @Finite.of_equiv _ _ h
        ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal _)
          (IsDiscreteValuationRing.not_a_field _) k).trans
          (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ k))
  have : I = IsLocalRing.maximalIdeal R ^ m := by
    rw [hm, hmax, Ideal.span_singleton_pow]
  rw [this]
  exact key m

end Adic

theorem GL_integral_hecke_commute : Formalism.UG.GLintComm := by
  intro F _ _ v n g
  obtain ⟨c, hc0, hg, hg'⟩ := glint_exists_denom (v.adicCompletionIntegers F) g
  have hP := glint_princ_le_map_conj (v.adicCompletionIntegers F).toSubring g c hg hg'
  have hres : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := glint_finite_residueField v
  have hI : Ideal.span {c * c} ≠ (⊥ : Ideal (v.adicCompletionIntegers F).toSubring) := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hc0 hc0
  have hfin : Finite ((v.adicCompletionIntegers F).toSubring ⧸ Ideal.span {c * c}) :=
    glint_finite_quotient_of_dvr hres _ hI
  have hne := glint_princ_relIndex_ne_zero (n := Fin n) (v.adicCompletionIntegers F).toSubring
    (Ideal.span {c * c})
  have hd := Subgroup.relIndex_dvd_of_le_left (bc (n := Fin n) (v.adicCompletionIntegers F).toSubring.subtype).range hP
  intro h0
  apply hne
  unfold GLint at h0 hd
  rw [h0] at hd
  exact Nat.eq_zero_of_zero_dvd hd

end Formalism.UG.P
