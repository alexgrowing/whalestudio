import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private lemma nt_expand {R : Type*} [Ring R] (y : R) (m : ℕ) :
    ∃ w : R, (1 + y) ^ m = 1 + m • y + (m.choose 2) • (y * y) + y * y * y * w := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨w * (1 + y) + (m.choose 2) • 1, ?_⟩
    have hc : (m + 1).choose 2 = m + m.choose 2 := by
      rw [Nat.choose_succ_succ' m 1, Nat.choose_one_right]
    rw [pow_succ, hw, hc]
    simp only [add_smul, one_smul, mul_add, add_mul, mul_one, one_mul, smul_mul_assoc,
      mul_smul_comm, mul_assoc]
    abel

section TF

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {p : ℕ}

omit [IsNoetherianRing R] in
private lemma nt_step (hp : p.Prime) (hp2 : p ≠ 2) (hp0 : (p : R) ≠ 0) (hpm : ¬ IsUnit (p : R)) {n : ℕ} (q : ℕ) (hq : q.Prime)
    (k : ℕ) (z : Matrix (Fin n) (Fin n) R)
    (h : (1 + (p : R) ^ (k + 1) • z) ^ q = 1) :
    ∃ z' : Matrix (Fin n) (Fin n) R, z = (p : R) • z' := by
  obtain ⟨w, hw⟩ := nt_expand ((p : R) ^ (k + 1) • z) q
  rw [h] at hw
  by_cases hqp : q = p
  · subst hqp
    obtain ⟨c, hc⟩ : q ∣ q.choose 2 :=
      hq.dvd_choose_self (by norm_num) (lt_of_le_of_ne hq.two_le (Ne.symm hp2))
    refine ⟨-((c : R) * (q : R) ^ k) • (z * z) - ((q : R) ^ (2 * k)) • (z * z * z * w), ?_⟩
    have hne : (q : R) ^ (k + 2) ≠ 0 := pow_ne_zero _ hp0
    apply smul_right_injective _ hne
    rw [hc] at hw
    simp only [← Nat.cast_smul_eq_nsmul R, smul_mul_assoc, mul_smul_comm, smul_smul] at hw
    push_cast at hw
    linear_combination (norm := module) -hw
  · have hu : IsUnit (q : R) := by
      obtain ⟨a, b, hab⟩ : IsCoprime (q : R) (p : R) := Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hqp)
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
      · exact isUnit_of_mul_isUnit_right h
      · exact absurd (isUnit_of_mul_isUnit_right h) hpm
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    refine ⟨v • (-((q.choose 2 : R) * (p : R) ^ k) • (z * z) - ((p : R) ^ (2 * k + 1)) • (z * z * z * w)), ?_⟩
    have hne : (p : R) ^ (k + 1) ≠ 0 := pow_ne_zero _ hp0
    have key : (q : R) • z = (p : R) • (-((q.choose 2 : R) * (p : R) ^ k) • (z * z) - ((p : R) ^ (2 * k + 1)) • (z * z * z * w)) := by
      apply smul_right_injective _ hne
      simp only [← Nat.cast_smul_eq_nsmul R, smul_mul_assoc, mul_smul_comm, smul_smul] at hw
      linear_combination (norm := module) -hw
    rw [smul_comm, ← key, smul_smul, hv, one_smul]

private lemma nt_prime (hp : p.Prime) (hp2 : p ≠ 2) (hp0 : (p : R) ≠ 0) (hpm : ¬ IsUnit (p : R)) {n : ℕ} (q : ℕ) (hq : q.Prime)
    (z : Matrix (Fin n) (Fin n) R)
    (h : (1 + (p : R) • z) ^ q = 1) : (p : R) • z = 0 := by
  have hk : ∀ k : ℕ, ∃ z' : Matrix (Fin n) (Fin n) R, (p : R) • z = (p : R) ^ (k + 1) • z' := by
    intro k
    induction k with
    | zero => exact ⟨z, by simp⟩
    | succ k ih =>
      obtain ⟨z', hz'⟩ := ih
      rw [hz'] at h
      obtain ⟨z'', hz''⟩ := nt_step hp hp2 hp0 hpm q hq k z' h
      exact ⟨z'', by rw [hz', hz'', smul_smul, ← pow_succ]⟩
  ext i j
  by_contra hne
  have hne' : ((p : R) • z) i j ≠ 0 := hne
  obtain ⟨k, hk'⟩ := FiniteMultiplicity.of_not_isUnit hpm hne'
  obtain ⟨z', hz'⟩ := hk k
  apply hk'
  rw [hz']
  exact ⟨z' i j, rfl⟩

private lemma nt_mat (hp : p.Prime) (hp2 : p ≠ 2) (hp0 : (p : R) ≠ 0) (hpm : ¬ IsUnit (p : R)) {n : ℕ} (m : ℕ) :
    m ≠ 0 → ∀ (z : Matrix (Fin n) (Fin n) R), (1 + (p : R) • z) ^ m = 1 → (p : R) • z = 0 := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one => intro _ z h; simpa using h
  | prime_mul q a hq ih =>
    intro hm z h
    have ha : a ≠ 0 := right_ne_zero_of_mul hm
    apply ih ha z
    obtain ⟨w, hw⟩ := nt_expand ((p : R) • z) a
    have hz : (1 + (p : R) • z) ^ a = 1 + (p : R) • (a • z + (a.choose 2) • (z * ((p : R) • z)) +
        z * ((p : R) • z) * ((p : R) • z) * w) := by
      rw [hw]
      simp only [← Nat.cast_smul_eq_nsmul R, smul_mul_assoc, mul_smul_comm, smul_smul]
      module
    rw [mul_comm, pow_mul, hz] at h
    rw [hz, nt_prime hp hp2 hp0 hpm q hq _ h, add_zero]

end TF

section Loc

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

private theorem nt_le (w : Plc L) (x y : w.adicCompletion L) :
    valuation (w.adicCompletion L) x ≤ valuation (w.adicCompletion L) y ↔ Valued.v x ≤ Valued.v y := by
  rw [← Valuation.Compatible.vle_iff_le]
  exact Iff.rfl

private theorem nt_val (w : Plc L) (x : L) : Valued.v (algebraMap L (w.adicCompletion L) x) = w.valuation L x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

private theorem nt_sq {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr L) (w : Plc L) (hv : (p : 𝓞 L) ∈ w.asIdeal) :
    (p : 𝓞 L) ∉ w.asIdeal ^ 2 := by
  intro h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  have hP := w.isPrime
  have hlo : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hpz).2 (by simpa using hv)
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have hun := (not_dvd_discr_iff_forall_mem L (𝓞 L) hpz).1 hd w.asIdeal hP (by simpa using hv)
  have hu : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := hlo.over.symm
  have : Finite (ℤ ⧸ w.asIdeal.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ (hu ▸ hb)
  have : (w.asIdeal.under ℤ).IsMaximal := hu ▸ hmax
  have : Finite (w.asIdeal.under ℤ).ResidueField := inferInstance
  have he : w.asIdeal.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hmap : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 L)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) w.asIdeal hb] at he
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h

private theorem nt_free {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : ¬ (p : ℤ) ∣ discr L) (w : Plc L)
    (hv : (p : 𝓞 L) ∈ w.asIdeal) (g : GLw n w) (hg : g ∈ Kc _ n 1) (hf : IsOfFinOrder g) : g = 1 := by
  have hvp : Valued.v ((p : ℕ) : w.adicCompletion L) = w.intValuation (p : 𝓞 L) := by
    rw [← w.valuation_of_algebraMap (K := L), ← nt_val]
    exact congrArg Valued.v (map_natCast ((algebraMap L (w.adicCompletion L)).comp (algebraMap (𝓞 L) L)) p).symm
  have h1 : Valued.v ((p : ℕ) : w.adicCompletion L) < 1 := by
    rw [hvp]; exact (w.intValuation_lt_one_iff_mem _).2 hv
  have h2 : ¬ Valued.v ((p : ℕ) : w.adicCompletion L) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [hvp, w.intValuation_le_pow_iff_mem]; exact nt_sq hp hd w hv
  have h3 : ∀ y : w.adicCompletion L, Valued.v y < 1 → Valued.v y ≤ Valued.v ((p : ℕ) : w.adicCompletion L) := by
    intro y
    generalize Valued.v y = a
    revert h2
    generalize Valued.v ((p : ℕ) : w.adicCompletion L) = b
    intro h2 ha
    rcases eq_or_ne a 0 with rfl | ha0
    · exact zero_le
    have hb0 : b ≠ 0 := by rintro rfl; exact h2 zero_le
    rw [← WithZero.exp_log ha0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at ha
    rw [← WithZero.exp_log hb0, WithZero.exp_le_exp] at h2
    rw [← WithZero.exp_log ha0, ← WithZero.exp_log hb0, WithZero.exp_le_exp]
    push_cast at h2
    omega
  haveI : IsLocalRing 𝒪[w.adicCompletion L] := (inferInstance : IsDiscreteValuationRing 𝒪[w.adicCompletion L]).toIsLocalRing
  have hI := Valuation.integer.integers (valuation (w.adicCompletion L))
  have hlt : ∀ y : w.adicCompletion L, valuation _ y < 1 ↔ Valued.v y < 1 := fun y => by
    have := nt_le w 1 y
    simp only [map_one] at this
    rw [← not_le, ← not_le, this]
  have hp0 : ((p : ℕ) : 𝒪[w.adicCompletion L]) ≠ 0 := by
    intro h
    have : ((p : ℕ) : w.adicCompletion L) = 0 := by simpa using congrArg (algebraMap _ (w.adicCompletion L)) h
    rw [this, map_zero] at h2
    exact h2 zero_le
  have hpm : ¬ IsUnit ((p : ℕ) : 𝒪[w.adicCompletion L]) := by
    intro h
    have := hI.one_of_isUnit h
    rw [map_natCast] at this
    exact ((hlt _).2 h1).ne this
  obtain ⟨x, hx, rfl⟩ := hg
  have hdv : ∀ i j, ((p : ℕ) : 𝒪[w.adicCompletion L]) ∣ (x.val - 1) i j := by
    intro i j
    rw [hI.dvd_iff_le, nt_le, map_natCast]
    refine h3 _ ((hlt _).1 ((GlobalTheory.StepData.residue_eq_zero_iff_lt _).1 ?_))
    rw [IsLocalRing.residue_eq_zero_iff, ← pow_one (maximalIdeal _), ← Ideal.Quotient.eq_zero_iff_mem]
    have := congrArg (fun y : GL (Fin n) _ => y.val i j) (MonoidHom.mem_ker.1 hx)
    change Ideal.Quotient.mk _ (x.val i j) = (1 : Matrix _ _ _) i j at this
    rw [Matrix.sub_apply, map_sub, this]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n)
      (algebraMap 𝒪[w.adicCompletion L] (w.adicCompletion L))) := fun a b h => by
    exact Units.ext (Matrix.ext fun i j => Subtype.ext (congrArg (fun y : GLw n w => y.val i j) h))
  have hfin : IsOfFinOrder x := (isOfFinOrder_iff_pow_eq_one.2 <| by
    obtain ⟨m, hm, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    exact ⟨m, hm, hinj (by rw [map_pow, h, map_one])⟩)
  choose c hc using hdv
  have hz : x.val = 1 + ((p : ℕ) : 𝒪[w.adicCompletion L]) • (Matrix.of c) := by
    rw [← sub_eq_iff_eq_add']
    ext i j
    rw [hc]
    rfl
  obtain ⟨m, hm, hxm⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h0 := nt_mat hp hp2 hp0 hpm m hm.ne' (Matrix.of c) (by rw [← hz, ← Units.val_pow_eq_pow_val, hxm, Units.val_one])
  have : x = 1 := Units.ext (by rw [hz, h0, add_zero, Units.val_one])
  rw [this, map_one]

private theorem nt_pow (w : Plc L) (K : Subgroup (GLw n w)) (hK : IsCompact (K : Set (GLw n w))) (g : GLw n w) (hg : g ∈ K) :
    ∃ m, 0 < m ∧ g ^ m ∈ KO (w.adicCompletion L) (Fin n) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI := Subgroup.quotient_finite_of_isOpen ((KO (w.adicCompletion L) (Fin n)).subgroupOf K)
    (GlobalTheory.SplitFlip.isOpen_KO.preimage continuous_subtype_val)
  obtain ⟨m, hm, -, h⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.finiteIndex_of_finite_quotient (H := (KO (w.adicCompletion L) (Fin n)).subgroupOf K)).index_ne_zero ⟨g, hg⟩
  exact ⟨m, hm, h⟩

private theorem nt_char (w : Plc L) (M : GL (Fin n) L) (g : GLw n w)
    (h : g⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap L (w.adicCompletion L)) M * g ∈ KO (w.adicCompletion L) (Fin n))
    (i : ℕ) : w.valuation L (M.val.charpoly.coeff i) ≤ 1 := by
  obtain ⟨x, hx⟩ := h
  have e := congrArg (fun y : GLw n w => y.val.charpoly.coeff i) hx
  have e1 : (g⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap L (w.adicCompletion L)) M * g).val.charpoly =
      M.val.charpoly.map (algebraMap L (w.adicCompletion L)) := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_units_conj g⁻¹ (M.val.map _), Units.val_mul, Units.val_mul,
      ← Matrix.coe_units_inv, inv_inv]
    rfl
  have e2 : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[w.adicCompletion L] (w.adicCompletion L)) x).val.charpoly =
      x.val.charpoly.map (algebraMap _ _) := Matrix.charpoly_map _ _
  simp only [e1, e2, Polynomial.coeff_map] at e
  rw [← nt_val]
  have h1 := (nt_le w (algebraMap L (w.adicCompletion L) (M.val.charpoly.coeff i)) 1).1 (by
    rw [← e, map_one]; exact (x.val.charpoly.coeff i).2)
  rw [map_one] at h1
  exact h1

end Loc

section Glob

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private theorem nt_int (T : Plc (Lp L) → Plc L) (hT : ∀ v, (T v).under (𝓞 (Lp L)) = v) (x : L)
    (h1 : ∀ v, (T v).valuation L x ≤ 1) (h2 : ∀ v, (T v).valuation L (IsCMField.complexConj L x) ≤ 1) : IsIntegral ℤ x := by
  have key : ∀ y : L, IsCMField.complexConj L y = y → (∀ v, (T v).valuation L y ≤ 1) → IsIntegral ℤ y := by
    intro y hy hv
    let y' : Lp L := ⟨y, (IsCMField.complexConj_eq_self_iff L y).1 hy⟩
    obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 (Lp L)) (Lp L) y' fun v => by
      haveI : (T v).asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal (hT v)).symm⟩
      have e := HeightOneSpectrum.valuation_liesOver L v (T v) y'
      have h0 : v.asIdeal.ramificationIdx' (T v).asIdeal ≠ 0 :=
        Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ v.ne_bot
      exact (pow_le_one_iff h0).1 (e ▸ hv v)
    have : y = algebraMap (Lp L) L (algebraMap _ (Lp L) z) := by rw [hz]; rfl
    rw [this]
    exact z.isIntegral_coe.algebraMap
  have ha := key (x + IsCMField.complexConj L x) (by simp [add_comm]) fun v => Valuation.map_add_le _ (h1 v) (h2 v)
  have hb := key (x * IsCMField.complexConj L x) (by simp [mul_comm]) fun v => by
    rw [map_mul]; exact mul_le_one' (h1 v) (h2 v)
  let a : 𝓞 L := ⟨_, ha⟩
  let b : 𝓞 L := ⟨_, hb⟩
  refine isIntegral_trans (A := 𝓞 L) x ⟨X ^ 2 - C a * X + C b, by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X]
  change x ^ 2 - (x + IsCMField.complexConj L x) * x + x * IsCMField.complexConj L x = 0
  ring

private theorem nt_fin (M : GL (Fin n) L) (hU : ∀ k : ℕ, ((M ^ k).val.map (IsCMField.complexConj L)).transpose * (M ^ k).val = 1)
    (hM : ∀ i, IsIntegral ℤ (M.val.charpoly.coeff i)) : IsOfFinOrder M := by
  have hI : IsIntegral (𝓞 L) M.val := by
    have hl : M.val.charpoly ∈ Polynomial.lifts (algebraMap (𝓞 L) L) :=
      (Polynomial.lifts_iff_coeff_lifts _).2 fun i => ⟨⟨_, hM i⟩, rfl⟩
    obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl M.val.charpoly_monic
    refine ⟨q, hm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap L, hq, Matrix.aeval_self_charpoly]
  have hfg := hI.fg_adjoin_singleton
  have hent : ∀ i j, {x : L | ∃ k : ℕ, (M ^ k).val i j = x}.Finite := by
    intro i j
    obtain ⟨d, hd, h⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors (𝓞 L)) (P := L)
      (hfg.map (Matrix.entryLinearMap (𝓞 L) L i j))
    have hd0 : (d : L) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
    refine Set.Finite.of_finite_image (f := fun x => (d : L) * x)
      ((Embeddings.finite_of_norm_le L ℂ (∑ φ : L →+* ℂ, ‖φ d‖)).subset ?_) (mul_right_injective₀ hd0).injOn
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨?_, fun φ => ?_⟩
    · obtain ⟨z, hz⟩ := h ((M ^ k).val i j) ⟨M.val ^ k, pow_mem (Algebra.self_mem_adjoin_singleton (𝓞 L) M.val) k, rfl⟩
      rw [Algebra.smul_def] at hz
      exact (congrArg (IsIntegral ℤ) hz).mp z.isIntegral_coe
    · have hu : (M ^ k).val.map φ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
        rw [Matrix.mem_unitaryGroup_iff']
        have := congrArg (fun y : Matrix (Fin n) (Fin n) L => y.map φ) (hU k)
        simp only [Matrix.map_mul] at this
        rw [Matrix.map_one _ φ.map_zero φ.map_one] at this
        rw [← this]
        congr 1
        ext a b
        simp [IsCMField.complexEmbedding_complexConj]
      rw [map_mul, norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (entry_norm_bound_of_unitary hu i j)).trans
        (Finset.single_le_sum (f := fun φ : L →+* ℂ => ‖φ d‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ φ))
  have hfin : (Set.range fun k : ℕ => M ^ k).Finite := by
    refine Set.Finite.of_finite_image (f := fun y : GL (Fin n) L => fun i j => y.val i j)
      ((Set.Finite.pi' fun i => Set.Finite.pi' fun j => hent i j).subset ?_)
      fun a _ b _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩ i j
    exact ⟨k, rfl⟩
  exact finite_powers.1 hfin

private theorem nt_ord (T : Plc (Lp L) → Plc L) (hT : ∀ v, (T v).under (𝓞 (Lp L)) = v) (M : GL (Fin n) L)
    (hU : ∀ k : ℕ, ((M ^ k).val.map (IsCMField.complexConj L)).transpose * (M ^ k).val = 1)
    (h : ∀ v, ∃ g : GLw n (T v), g⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap L _) M * g ∈ KO _ (Fin n)) :
    IsOfFinOrder M := by
  refine nt_fin M hU fun i => nt_int T hT _ (fun v => ?_) fun v => ?_
  · obtain ⟨g, hg⟩ := h v
    exact nt_char _ M g hg i
  · obtain ⟨g, hg⟩ := h v
    have e : (M⁻¹).val = (M.val.map (IsCMField.complexConj L)).transpose := by
      have := hU 1
      rw [pow_one] at this
      exact Units.inv_eq_of_mul_eq_one_left this
    have := nt_char _ M⁻¹ g (by
      have := inv_mem hg
      rwa [mul_inv_rev, mul_inv_rev, inv_inv, ← map_inv, ← mul_assoc] at this) i
    rw [e, Matrix.charpoly_transpose] at this
    have e2 := Matrix.charpoly_map M.val (IsCMField.complexConj L).toRingEquiv.toRingHom
    rw [show (M.val.map (IsCMField.complexConj L)).charpoly = _ from e2, Polynomial.coeff_map] at this
    exact this

private theorem nt_under {Ω : Type} [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (s : HidaSetting l L Ω)
    (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  rw [← s.hA v x, IsScalarTower.algebraMap_apply (Lp L) L Ω]
  exact (s.hw v (algebraMap _ (𝓞 L) x)).symm

private theorem nt_nat (l : ℕ) (w : Plc L) : ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

private theorem nt_rat (γ : ratU L n) : ∃ M : GL (Fin n) L, ratGL L n M = γ.1.1 ∧
    (∀ k : ℕ, ((M ^ k).val.map (IsCMField.complexConj L)).transpose * (M ^ k).val = 1) ∧
    ∀ w : Plc L, cLoc w γ.1 = Matrix.GeneralLinearGroup.map (algebraMap L _) M := by
  obtain ⟨M, hM⟩ := γ.2
  refine ⟨M, hM, fun k => ?_, fun w => ?_⟩
  · have h := (γ.1 ^ k).2
    rw [SubgroupClass.coe_pow, show γ.1.1 = _ from hM.symm, ← map_pow] at h
    generalize M ^ k = N at h
    have h' : ((N.val.map (algebraMap L (Ad L))).map (conjAd L)).transpose * 1 * N.val.map (algebraMap L (Ad L)) = 1 := h
    apply Matrix.map_injective (f := algebraMap L (Ad L)) (AdeleRing.algebraMap_injective _ _)
    change Matrix.map _ _ = Matrix.map _ _
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← h', mul_one]
    congr 1
    ext i j : 1
    exact (conjAd_algebraMap _).symm
  · change Matrix.GeneralLinearGroup.map _ γ.1.1 = _
    rw [show γ.1.1 = _ from hM.symm]
    rfl

end Glob

private theorem nt_conj {G : Type} [Group G] (a b : G) (k : ℕ) : (a⁻¹ * b * a) ^ k = a⁻¹ * b ^ k * a := by
  simpa using conj_pow (a := a⁻¹) (b := b) (i := k)

section Lev

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ}

private theorem nt_sec (w : Plc L) (g : GLw n w) : sec n s w g ∈ locA n s w ∧
    (cmp n w (sec n s w g).1 = g ∨ cmp n w (sec n s w g).1 = 1) := by
  unfold sec
  split_ifs with h
  · exact ⟨Subtype.mem _, Or.inl ((MulEquiv.ofBijective _ h).apply_symm_apply g)⟩
  · exact ⟨one_mem _, Or.inr (map_one _)⟩

omit [Fact l.Prime] in
private theorem nt_cmp (w : Plc L) (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dif_pos h]
  rfl

variable {V : s.Lev} (Q : QData V) {c : Coef l} {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev)

private theorem nt_out (w : Plc L) (hw : w.under (𝓞 (Lp L)) ∉ V.S') :
    (hset Q τ₀).lev K ≤ (KO (w.adicCompletion L) (Fin n)).comap ((cmp n w).comp (Ub n s).subtype) := by
  refine sup_le (inf_le_left.trans ((iInf_le _ w).trans (iInf_le _ hw))) (iSup_le fun q => ?_)
  rintro _ ⟨g, -, rfl⟩
  have hne : w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) := fun e => hw (by
    rw [Q.range, e]; exact Or.inr ⟨q, rfl⟩)
  have := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (nt_sec (s := s) (Q.wq q) g).1 w) hne
  exact Subgroup.mem_comap.2 ((MonoidHom.mem_ker.1 this).symm ▸ one_mem _)

private theorem nt_Q (q : Q.Q) :
    (hset Q τ₀).lev K ≤ (K.1 q).comap ((cmp n (Q.wq q)).comp (Ub n s).subtype) := by
  refine sup_le (inf_le_right.trans ((iInf_le _ q).trans fun x hx => ?_)) (iSup_le fun q' => ?_)
  · exact Subgroup.mem_comap.2 ((MonoidHom.mem_ker.1 hx).symm ▸ one_mem _)
  rintro _ ⟨g, hg, rfl⟩
  by_cases e : q = q'
  · subst e
    rcases (nt_sec (s := s) (Q.wq q) g).2 with h | h
    · exact Subgroup.mem_comap.2 ((congrArg (· ∈ K.1 q) h).mpr hg)
    · exact Subgroup.mem_comap.2 ((congrArg (· ∈ K.1 q) h).mpr (one_mem _))
  · have := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (nt_sec (s := s) (Q.wq q') g).1 (Q.wq q)) fun h => e (Q.inj h)
    exact Subgroup.mem_comap.2 ((MonoidHom.mem_ker.1 this).symm ▸ one_mem _)

end Lev

private theorem nt_Iw {L : Type} [Field L] [NumberField L] {n : ℕ} {V : Type} [Fintype V] (S : V → Plc L) :
    (iwS n S).Iw 0 ≤ Subgroup.pi Set.univ fun v => KO ((S v).adicCompletion L) (Fin n) := by
  have key : ∀ v, (glIwa ((S v).adicCompletion L) n).Iw 0 ≤ KO ((S v).adicCompletion L) (Fin n) := fun v => by
    rw [(glBridge _ n ℂ 1).2.2.2.2.2.1]
    exact iwahori_le_KO _ _
  exact sup_le (sup_le (fun g hg v hv => key v (Subgroup.mem_sup_left (Subgroup.mem_sup_left (hg v hv))))
    fun g hg v hv => key v (Subgroup.mem_sup_left (Subgroup.mem_sup_right (hg v hv))))
    fun g hg v hv => key v (Subgroup.mem_sup_right (hg v hv))

theorem UpperTheory.V.Hi.neatU :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ K, (hset Q τ₀).X.Neat ((hset Q τ₀).lev K) := by
  intro l hl L Ω _ _ _ _ _ _ s n _ V Q c m τ₀ K g γ u hu b hb h
  classical
  obtain ⟨M, hM, hU, hc⟩ := nt_rat (L := L) (n := n) γ
  have ha : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ k : ℕ,
      (cmp n w g.1)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap L _) (M ^ k) * cmp n w g.1 = cmp n w u.1 ^ k := by
    intro w hw k
    have e : cmp n w ((away l L n).rangeRestrict γ.1) * cmp n w g.1 = cmp n w g.1 * cmp n w u.1 :=
      ((map_mul _ _ _).symm.trans (congrArg (fun x => cmp n w x.1) h)).trans (map_mul _ _ _)
    rw [nt_cmp w hw, hc] at e
    rw [map_pow, ← nt_conj, mul_assoc, e, inv_mul_cancel_left]
  let g2 : ∀ v : Vl l L, GLw n (s.w v.1) := g.2
  let b2 : ∀ v : Vl l L, GLw n (s.w v.1) := b
  have hp : ∀ (v : Vl l L) (k : ℕ),
      (g2 v)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap L ((s.w v.1).adicCompletion L)) (M ^ k) * g2 v = b2 v ^ k := by
    intro v k
    have e : cLoc (s.w v.1) γ.1 * g2 v = g2 v * b2 v := congrArg (fun x => x.2 v) h
    rw [hc] at e
    rw [map_pow, ← nt_conj, mul_assoc, e, inv_mul_cancel_left]
  have hlS : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → ((l : ℕ) : 𝓞 L) ∉ w.asIdeal :=
    fun w hw h => hw (Or.inl ((nt_nat l w).2 h))
  have hp0 : ((s.p : ℕ) : 𝓞 L) ∈ (s.w s.v0).asIdeal := by
    rw [← nt_nat, nt_under, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← s.norm_v0_eq_one, normV]
    haveI : Finite (𝓞 (Lp L) ⧸ s.v0.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v0.ne_bot
    haveI := Fintype.ofFinite (𝓞 (Lp L) ⧸ s.v0.asIdeal)
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero _
  have hl0 : ((l : ℕ) : 𝓞 L) ∉ (s.w s.v0).asIdeal := fun h => by
    obtain ⟨a, b, hab⟩ : IsCoprime (l : 𝓞 L) (s.p : 𝓞 L) :=
      Nat.Coprime.cast ((Nat.coprime_primes hl.out s.p_prime).2 s.p_ne.symm)
    exact (s.w s.v0).isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hp0)))
  have hu0 : cmp n (s.w s.v0) u.1 ∈ Kc _ n 1 := u.2.2
  choose e he0 he using fun q : Q.Q => nt_pow (Q.wq q) (K.1 q) (K.2 q).2 _ (nt_Q Q τ₀ K q hu)
  have hN : 0 < ∏ q, e q := Finset.prod_pos fun q _ => he0 q
  have hT : ∀ v : Plc (Lp L), ∃ w : Plc L, w.under (𝓞 (Lp L)) = v ∧ ∃ x : GLw n w,
      x⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap L _) (M ^ ∏ q, e q) * x ∈ KO _ (Fin n) := by
    intro v
    by_cases h1 : ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal
    · refine ⟨s.w v, nt_under s v, g2 ⟨v, h1⟩, ?_⟩
      rw [hp ⟨v, h1⟩]
      exact pow_mem (nt_Iw _ hb ⟨v, h1⟩ trivial) _
    have h1' : ((l : ℕ) : 𝓞 L) ∉ (s.w v).asIdeal := by rwa [← nt_nat, nt_under]
    by_cases h2 : v ∈ V.S'
    · rw [Q.range] at h2
      rcases h2 with (h2 | h2 | rfl) | ⟨q, rfl⟩
      · exact absurd h2 h1
      · refine ⟨s.w v, nt_under s v, _, (ha _ h1' _).symm ▸ pow_mem ?_ _⟩
        exact Subgroup.mem_iInf.1 u.2.1 ⟨v, h2⟩
      · refine ⟨s.w s.v0, nt_under s _, _, (ha _ h1' _).symm ▸ pow_mem ?_ _⟩
        obtain ⟨x, -, hx⟩ := hu0
        exact ⟨x, hx⟩
      · refine ⟨Q.wq q, rfl, cmp n _ g.1, ?_⟩
        rw [ha _ (hlS _ (Q.notS q))]
        obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem e (Finset.mem_univ q)
        rw [hd, pow_mul]
        exact pow_mem (he q) d
    · refine ⟨s.w v, nt_under s v, _, (ha _ h1' _).symm ▸ pow_mem ?_ _⟩
      exact nt_out Q τ₀ K (s.w v) (by rwa [nt_under]) hu
  choose T hT1 hT2 using hT
  have hfin : IsOfFinOrder M := (nt_ord T hT1 _ (fun k => by rw [← pow_mul]; exact hU _) hT2).of_pow hN.ne'
  obtain ⟨k, hk, hMk⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h1 : cmp n (s.w s.v0) u.1 = 1 := nt_free s.p_prime s.p_odd s.p_unr _ hp0 _ hu0
    (isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, by rw [← ha _ hl0, hMk, map_one, mul_one, inv_mul_cancel]⟩)
  have h2 := ha _ hl0 1
  rw [h1, pow_one, pow_one, mul_assoc, inv_mul_eq_one, right_eq_mul] at h2
  have hM1 : M = 1 := by
    refine Units.ext (Matrix.ext fun i j => (algebraMap L ((s.w s.v0).adicCompletion L)).injective ?_)
    refine (congrArg (fun y : GLw n (s.w s.v0) => y.val i j) h2).trans ?_
    simp only [Units.val_one, Matrix.one_apply]
    split_ifs <;> simp
  have hγ : γ = 1 := Subtype.ext (Subtype.ext (by rw [hM1, map_one] at hM; exact hM.symm))
  rw [hγ, map_one, one_mul, left_eq_mul] at h
  exact ⟨Subtype.ext (congrArg Prod.fst h), congrArg Prod.snd h⟩
