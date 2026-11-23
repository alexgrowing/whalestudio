import ReciprocityTheory.Chebotarev.SplitA
import ReciprocityTheory.Chebotarev.SplitD

open NumberField

namespace ReciprocityTheory.Cheb

noncomputable section

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

def splitEH (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) :
    Subgroup (CyclotomicField l E ≃ₐ[E] CyclotomicField l E) :=
  (χ.toUnitHom.comp (IsCyclotomicExtension.autEquivPow (CyclotomicField l E) hirr).toMonoidHom).ker

theorem splitE_autEquivPow_eq (hirr : Irreducible (Polynomial.cyclotomic l E))
    (σ : CyclotomicField l E ≃ₐ[E] CyclotomicField l E) (m : ℕ)
    (hσ : σ (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) =
      IsCyclotomicExtension.zeta l E (CyclotomicField l E) ^ m) :
    ((IsCyclotomicExtension.autEquivPow (CyclotomicField l E) hirr σ : (ZMod l)ˣ) : ZMod l) = (m : ZMod l) := by
  have hζ := IsCyclotomicExtension.zeta_spec l E (CyclotomicField l E)
  rw [IsCyclotomicExtension.autEquivPow_apply]
  have h1 := hζ.autToPow_spec E σ
  rw [hσ] at h1
  have hfin : IsOfFinOrder (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨l, (Fact.out : l.Prime).pos, hζ.pow_eq_one⟩
  have h2 := hfin.pow_eq_pow_iff_modEq.1 h1
  rw [← hζ.eq_orderOf] at h2
  change (((hζ.autToPow E σ : (ZMod l)ˣ) : ZMod l)) = _
  rw [← ZMod.natCast_zmod_val ((hζ.autToPow E σ : (ZMod l)ˣ) : ZMod l)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h2

theorem splitE_mem_H (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (σ : CyclotomicField l E ≃ₐ[E] CyclotomicField l E) (m : ℕ)
    (hσ : σ (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) =
      IsCyclotomicExtension.zeta l E (CyclotomicField l E) ^ m) (hm : χ (m : ZMod l) = 1) :
    σ ∈ splitEH hirr χ := by
  rw [splitEH, MonoidHom.mem_ker]
  apply Units.ext
  rw [MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  simp only [MulEquiv.coe_toMonoidHom, Units.val_one]
  rw [splitE_autEquivPow_eq hirr σ m hσ, hm]

theorem splitE_H_ne_top (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (hχ : χ ≠ 1) : splitEH hirr χ ≠ ⊤ := by
  intro hH
  apply hχ
  apply MulChar.ext
  intro u
  have hm : (IsCyclotomicExtension.autEquivPow (CyclotomicField l E) hirr).symm u ∈ splitEH hirr χ := by
    rw [hH]; exact Subgroup.mem_top _
  rw [splitEH, MonoidHom.mem_ker] at hm
  have := congrArg Units.val hm
  rw [MonoidHom.comp_apply, MulChar.coe_toUnitHom] at this
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, Units.val_one] at this
  rw [this, MulChar.one_apply_coe]

theorem splitE_two_le (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (hχ : χ ≠ 1) : 2 ≤ Module.finrank E (IntermediateField.fixedField (splitEH hirr χ)) := by
  have h0 : 0 < Module.finrank E (IntermediateField.fixedField (splitEH hirr χ)) := Module.finrank_pos
  have h1 : Module.finrank E (IntermediateField.fixedField (splitEH hirr χ)) ≠ 1 := by
    intro h
    rw [IntermediateField.finrank_eq_one_iff] at h
    apply splitE_H_ne_top hirr χ hχ
    rw [← IntermediateField.fixingSubgroup_fixedField (splitEH hirr χ), h,
      IntermediateField.fixingSubgroup_bot]
  omega

theorem splitE_one_lt_Nrm (q : Prm E) : 1 < Nrm q := by
  unfold Nrm
  have h0 : Ideal.absNorm q.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.ne_bot
  have h1 : Ideal.absNorm q.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact q.isPrime.ne_top
  omega

theorem splitE_prime (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (q : Prm E) (hl : ¬ l ∣ Nrm q) (hq : χ ((Nrm q : ℕ) : ZMod l) = 1)
    (K : IntermediateField E (CyclotomicField l E))
    (hK : ∀ x : K, ∀ σ ∈ splitEH hirr χ, σ (x : CyclotomicField l E) = x)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver q.asIdeal] :
    Q.ramificationIdx (𝓞 E) = 1 ∧ Q.inertiaDeg (𝓞 E) = 1 ∧ Ideal.absNorm Q = Nrm q := by
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot q.ne_bot Q
  obtain ⟨⟨P, hPp, hPl⟩⟩ := Q.nonempty_primesOver (S := 𝓞 (CyclotomicField l E))
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hQ0 P
  have hPq : P.LiesOver q.asIdeal := Ideal.LiesOver.trans P Q q.asIdeal
  let P' : Prm (CyclotomicField l E) := ⟨P, hPp, hP0⟩
  have hund : under (E := E) P' = q := by
    ext1; rw [under_asIdeal]; exact (Ideal.over_def P q.asIdeal).symm
  have he : Q.ramificationIdx (𝓞 E) = 1 := by
    have h1 := splitA_unram E l q P' hund hl
    have h2 := Ideal.ramificationIdx_tower (R := 𝓞 E) Q P
    change P.ramificationIdx (𝓞 E) = 1 at h1
    rw [h2] at h1
    exact Nat.eq_one_of_mul_eq_one_right h1
  obtain ⟨σ, hσζ, hσx⟩ := splitD_frob E l q P' hund hl
  have hσH : σ ∈ splitEH hirr χ := splitE_mem_H hirr χ σ _ hσζ hq
  have hfix : ∀ x : 𝓞 K, x - x ^ Nrm q ∈ Q := by
    intro x
    obtain ⟨y, hy, hyP⟩ := hσx (algebraMap (𝓞 K) (𝓞 (CyclotomicField l E)) x)
    have hxy : y = algebraMap (𝓞 K) (𝓞 (CyclotomicField l E)) x := by
      apply RingOfIntegers.ext
      rw [hy]
      have : ((algebraMap (𝓞 K) (𝓞 (CyclotomicField l E)) x : 𝓞 _) : CyclotomicField l E) =
          ((x : K) : CyclotomicField l E) := rfl
      rw [this]
      exact hK (x : K) σ hσH
    rw [hxy] at hyP
    rw [Ideal.over_def P Q]
    simpa [Ideal.under, map_sub, map_pow] using hyP
  have : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
  have : q.asIdeal.IsMaximal := q.isMaximal
  have hN := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver Q q.asIdeal q.isPrime q.ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hN
  have h2 : 1 < Nrm q := splitE_one_lt_Nrm q
  let : Field (𝓞 K ⧸ Q) := Ideal.Quotient.field Q
  let : Fintype (𝓞 K ⧸ Q) := Fintype.ofFinite _
  have hcard : Ideal.absNorm Q ≤ Nrm q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, ← Finset.card_univ]
    rw [← FiniteField.X_pow_card_sub_X_natDegree_eq (𝓞 K ⧸ Q) h2]
    apply Polynomial.card_le_degree_of_subset_roots
    intro z _
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ h2)]
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    have := (Ideal.Quotient.eq_zero_iff_mem).2 (hfix x)
    rw [map_sub, map_pow, sub_eq_zero] at this
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← this, sub_self]
  have hf0 : 0 < Q.inertiaDeg (𝓞 E) := Ideal.inertiaDeg_pos Q (𝓞 E)
  have hf : Q.inertiaDeg (𝓞 E) = 1 := by
    have h3 : Nrm q ^ Q.inertiaDeg (𝓞 E) ≤ Nrm q ^ 1 := by
      rw [pow_one]; unfold Nrm; rw [← hN]; exact hcard
    have := (Nat.pow_le_pow_iff_right h2).1 h3
    omega
  refine ⟨he, hf, ?_⟩
  rw [hN, hf, pow_one]; rfl

theorem splitE_count (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (q : Prm E) (hl : ¬ l ∣ Nrm q) (hq : χ ((Nrm q : ℕ) : ZMod l) = 1)
    (K : IntermediateField E (CyclotomicField l E))
    (hK : ∀ x : K, ∀ σ ∈ splitEH hirr χ, σ (x : CyclotomicField l E) = x) :
    Module.finrank E K ≤ {P : Prm K | under P = q ∧ Nrm P = Nrm q}.ncard := by
  classical
  have hfin : (q.asIdeal.primesOver (𝓞 K)).Finite := Algebra.QuasiFinite.finite_primesOver q.asIdeal
  let : Fintype (q.asIdeal.primesOver (𝓞 K)) := hfin.fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank q.asIdeal (𝓞 K)
  rw [← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K] at hsum
  have hone : ∀ Q : q.asIdeal.primesOver (𝓞 K),
      Q.1.ramificationIdx (𝓞 E) * Q.1.inertiaDeg (𝓞 E) = 1 := by
    rintro ⟨Q, hQp, hQl⟩
    obtain ⟨h1, h2, -⟩ := splitE_prime hirr χ q hl hq K hK Q
    rw [h1, h2]
  simp only [hone, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  let g : q.asIdeal.primesOver (𝓞 K) → Prm K := fun Q =>
    have := Q.2.2
    ⟨Q.1, Q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot q.ne_bot Q.1⟩
  have hg : Function.Injective g := by
    intro Q1 Q2 h
    apply Subtype.ext
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
  have hset : {P : Prm K | under P = q ∧ Nrm P = Nrm q} = Set.range g := by
    ext P
    constructor
    · rintro ⟨hP, -⟩
      have hlo : P.asIdeal.LiesOver q.asIdeal := ⟨by rw [← hP, under_asIdeal]⟩
      exact ⟨⟨P.asIdeal, P.isPrime, hlo⟩, rfl⟩
    · rintro ⟨Q, rfl⟩
      have := Q.2.1
      have := Q.2.2
      refine ⟨?_, ?_⟩
      · ext1
        rw [under_asIdeal]
        exact (Ideal.over_def Q.1 q.asIdeal).symm
      · exact (splitE_prime hirr χ q hl hq K hK Q.1).2.2
  rw [hset, Set.ncard_range_of_injective hg, Nat.card_eq_fintype_card, hsum]

end

end ReciprocityTheory.Cheb
