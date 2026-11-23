import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraAlt

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem dO_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.S6.norm_le_one_of_isIntegral l x hx

private theorem dO_small {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (y : A →+* PadicAlgCl l) (hle : ∀ x, ‖y x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal A ^ n, ‖y z‖ < ε := by
  have hl0 : ((l : ℕ) : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl : (l : A) ≠ 0 := fun h => hl0 (by simpa using congrArg y h)
  have hl1 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hl1
  refine ⟨e * n, fun z hz => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
  have hd : (l : A) ^ n ∣ z := by
    refine Dvd.dvd.trans ?_ hz
    rw [pow_mul, hu]
    exact pow_dvd_pow_of_dvd (Units.mul_left_dvd.2 dvd_rfl) n
  obtain ⟨w, rfl⟩ := hd
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (hle w)) hn

private theorem dO_desc {O Q : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field Q] [Algebra O Q]
    (hinj : Function.Injective (algebraMap O Q)) {n : ℕ} (Y : Matrix (Fin n) (Fin n) Q) :
    ∃ (a : O) (Y0 : Matrix (Fin n) (Fin n) O), a ≠ 0 ∧ ∀ (e : O) (A B Z : Matrix (Fin n) (Fin n) O),
      Z.map (algebraMap O Q) = algebraMap O Q e • (A.map (algebraMap O Q) * Y * B.map (algebraMap O Q)) - Y →
      a • Z = e • (A * Y0 * B) - Y0 := by
  haveI : FaithfulSMul O Q := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  let N : Submodule O Q := Submodule.span O (insert 1 (Set.range fun p : Fin n × Fin n => Y p.1 p.2))
  haveI : Module.Finite O N := Module.Finite.span_of_finite O ((Set.finite_range _).insert _)
  let one : N := ⟨1, Submodule.subset_span (Set.mem_insert _ _)⟩
  let Yn : Fin n → Fin n → N := fun i j => ⟨Y i j, Submodule.subset_span (Set.mem_insert_of_mem _ ⟨(i, j), rfl⟩)⟩
  have h1 : one ≠ 0 := fun h => one_ne_zero (congrArg Subtype.val h)
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_ne_zero O h1
  refine ⟨π one, Matrix.of fun i j => π (Yn i j), hπ, fun e A B Z h => ?_⟩
  ext i j
  have h2 : Z i j • one = e • (∑ k, ∑ m, (A i m * B k j) • Yn m k) - Yn i j := by
    apply Subtype.ext
    have := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul] at this
    simp only [one, Yn, Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_sum, Algebra.smul_def, mul_one, this, map_mul,
      Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
  have h3 := congrArg π h2
  simp only [map_smul, map_sub, map_sum, smul_eq_mul] at h3
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Matrix.of_apply, Finset.sum_mul]
  rw [mul_comm, h3]
  congr 2
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring

private theorem dO_pol {O : Type} [CommRing O] {n : ℕ} (P P' A A' B B' Y Z W : Matrix (Fin n) (Fin n) O) (s s' e a : O)
    (hP : P * P' = 1) (hP' : P' * P = 1) (hA : A * A' = 1) (hA' : A' * A = 1) (hs : s * s' = 1)
    (h1 : Aᵀ * P * B = s • P) (h2 : A'ᵀ * P * B' = s' • P) (hz : P * W = Zᵀ * P)
    (hc : a • Z = e • (A * Y * A') - Y) :
    a • W = e • (B * (P' * Yᵀ * P) * B') - P' * Yᵀ * P := by
  have e1 : P * B = s • (A'ᵀ * P) := by
    rw [← Matrix.mul_smul, ← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hA]; simp
  have e2 : P * B' = s' • (Aᵀ * P) := by
    rw [← Matrix.mul_smul, ← h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hA']; simp
  have e3 : P * (a • W) = P * (e • (B * (P' * Yᵀ * P) * B') - P' * Yᵀ * P) := by
    have f1 : P * (B * (P' * Yᵀ * P) * B') = (P * B) * P' * Yᵀ * (P * B') := by simp only [Matrix.mul_assoc]
    have f2 : P * (P' * Yᵀ * P) = Yᵀ * P := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP, Matrix.one_mul]
    have f3 : A'ᵀ * P * P' = A'ᵀ := by rw [Matrix.mul_assoc, hP, Matrix.mul_one]
    rw [Matrix.mul_smul, hz, ← Matrix.smul_mul, ← Matrix.transpose_smul, hc, Matrix.mul_sub, Matrix.mul_smul, f1, f2, e1, e2,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul s, hs, one_smul, f3]
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.mul_assoc]
  have := congrArg (P' * ·) e3
  simpa only [← Matrix.mul_assoc, hP', Matrix.one_mul] using this

private theorem dO_sym {O : Type} [CommRing O] {n : ℕ} (P P' Y : Matrix (Fin n) (Fin n) O)
    (hP : P * P' = 1) (hP' : P' * P = 1) (hs : Pᵀ = P ∨ Pᵀ = -P) :
    P * (Y + P' * Yᵀ * P) = (Y + P' * Yᵀ * P)ᵀ * P := by
  have f2 : P * (P' * Yᵀ * P) = Yᵀ * P := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP, Matrix.one_mul]
  have f0 : P'ᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hP, Matrix.transpose_one]
  have f3 : (P' * Yᵀ * P)ᵀ * P = P * Y := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rcases hs with h | h
    · rw [h] at f0
      rw [f0, h, Matrix.mul_one]
    · rw [h, Matrix.mul_neg, neg_eq_iff_eq_neg] at f0
      rw [f0, h]; simp
  rw [Matrix.mul_add, Matrix.transpose_add, Matrix.add_mul, f2, f3, add_comm]

theorem UpperTheory.V.Th.detO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (c : Coef l) (n : ℕ) (y : Pt G0.frame c.O n) (S : Set G0.G₀), l ≠ 2 → DetQ G0.frame c.O (pushRep (algebraMap c.O (Qbar l)) y.ρ) (GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P) S → DetO y S := by
  intro l _ L G0 c n y S _ hQ z hcont hcoc hpol htr
  set f := algebraMap c.O (Qbar l) with hf
  have hinj : Function.Injective f := Subtype.val_injective
  have hle : ∀ x : c.O, ‖f x‖ ≤ 1 := fun x =>
    dO_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val)
  have hm : ∀ g, mat (pushRep f y.ρ) g = (mat y.ρ g).map f := fun g => rfl
  have hP : ((GeneralLinearGroup.map f y.P : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
    (y.P : Matrix (Fin n) (Fin n) c.O).map f := rfl
  have he : ∀ g : G0.G₀, ((G0.frame.eps c.O (Qbar l) g : (Qbar l)ˣ) : Qbar l) =
    f (algebraMap ℤ_[l] c.O (G0.ε g : ℤ_[l])) := fun g => rfl
  obtain ⟨Y, hY⟩ := hQ (fun g => (z g).map f) (by
      refine continuous_matrix fun a b => continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
      obtain ⟨k, hk⟩ := dO_small f hle hε
      filter_upwards [(hcont a b k).eventually_eq g] with g' hg'
      rw [dist_eq_norm, Matrix.map_apply, Matrix.map_apply, ← map_sub]
      exact hk _ (Ideal.Quotient.eq.1 hg'))
    (fun g g' => by
      rw [hcoc, hm, hm, he, Matrix.map_add _ (map_add f), ← Matrix.map_mul, ← Matrix.map_mul]
      congr 1
      all_goals (ext i j; simp))
    (fun g => by rw [hP, ← Matrix.map_mul, hpol, Matrix.map_mul, Matrix.transpose_map])
    (fun σ hσ k => by
      rw [← map_pow, hm, ← Matrix.map_mul, ← AddMonoidHom.map_trace, map_pow, htr σ hσ k, map_zero])
  obtain ⟨a, Y0, ha, hY0⟩ := dO_desc hinj Y
  have hc : ∀ g : G0.G₀, a • z g = algebraMap ℤ_[l] c.O (G0.ε g : ℤ_[l]) • (mat y.ρ g * Y0 * mat y.ρ g⁻¹) - Y0 :=
    fun g => hY0 _ _ _ _ (hY g)
  have hP1 : (y.P : Matrix (Fin n) (Fin n) c.O) * (y.P⁻¹ : GL (Fin n) c.O) = 1 := Units.mul_inv _
  have hP2 : ((y.P⁻¹ : GL (Fin n) c.O) : Matrix (Fin n) (Fin n) c.O) * y.P = 1 := Units.inv_mul _
  refine ⟨a + a, Y0 + (y.P⁻¹ : GL (Fin n) c.O) * Y0ᵀ * y.P, ?_, dO_sym _ _ _ hP1 hP2 y.sgn, fun g => ?_⟩
  · rw [← two_mul]
    exact mul_ne_zero two_ne_zero ha
  have hcc : G0.frame.conj (G0.frame.conj g) = g := by
    apply Subtype.ext
    have h2 : G0.c⁻¹ = G0.c := inv_eq_of_mul_eq_one_right G0.c_sq
    show G0.c * (G0.c * g * G0.c⁻¹) * G0.c⁻¹ = g
    rw [h2, ← mul_assoc, ← mul_assoc, G0.c_sq, one_mul, mul_assoc, G0.c_sq, mul_one]
  have hε : G0.ε (G0.frame.conj g : G0.G₀) = G0.ε g := by
    show G0.ε (G0.c * g * G0.c⁻¹) = _
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have h5 := dO_pol _ _ _ _ _ _ Y0 _ _ _ _ _ a hP1 hP2 (by rw [← map_mul, mul_inv_cancel, map_one])
    (by rw [← map_mul, inv_mul_cancel, map_one])
    (by rw [← Units.val_mul, ← mul_zpow, ← map_mul, mul_inv_cancel, map_one, _root_.one_zpow, Units.val_one])
    (y.form (G0.frame.conj g)) (y.form (G0.frame.conj g)⁻¹) (hpol (G0.frame.conj g)) (hc (G0.frame.conj g))
  rw [map_inv, hcc, hε] at h5
  rw [add_smul, Matrix.mul_add, Matrix.add_mul, smul_add]
  conv_lhs => rw [hc g]; arg 2; rw [← hc g, h5]
  abel
