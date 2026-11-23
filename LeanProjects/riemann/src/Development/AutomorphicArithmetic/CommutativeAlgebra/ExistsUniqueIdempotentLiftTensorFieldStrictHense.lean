import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

private lemma algebraMap_eq_zero_of_mem (O K : Type) [CommRing O] [IsLocalRing O] [Field K]
    [Algebra O K] [Algebra.IsIntegral O K] {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) :
    algebraMap O K a = 0 := by
  have hm : Ideal.comap (algebraMap O K) ⊥ = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ⊥)
  have h : a ∈ Ideal.comap (algebraMap O K) ⊥ := hm ▸ ha
  simpa using h

private noncomputable def resMap (O K : Type) [CommRing O] [IsLocalRing O] [Field K]
    [Algebra O K] [Algebra.IsIntegral O K] : IsLocalRing.ResidueField O →+* K :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) (algebraMap O K)
    (fun _ ha ↦ algebraMap_eq_zero_of_mem O K ha)

private theorem mem_maximal_of_includeLeft_eq_zero (O R K : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Field K]
    [Algebra O R] [Algebra O K] [Algebra.IsIntegral O R] [Algebra.IsIntegral O K]
    (M : Ideal R) [M.IsMaximal] (x : R)
    (hx : (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) x = 0) : x ∈ M := by
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  haveI : Algebra.IsIntegral O (R ⧸ M) := inferInstance
  letI : Algebra (IsLocalRing.ResidueField O) K := (resMap O K).toAlgebra
  letI : Algebra (IsLocalRing.ResidueField O) (AlgebraicClosure (R ⧸ M)) :=
    ((algebraMap (R ⧸ M) (AlgebraicClosure (R ⧸ M))).comp (resMap O (R ⧸ M))).toAlgebra
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) K :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField O) K :=
    Algebra.IsIntegral.tower_top O
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) K := inferInstance
  let g : K →ₐ[IsLocalRing.ResidueField O] AlgebraicClosure (R ⧸ M) := IsAlgClosed.lift
  let fR : R →+* AlgebraicClosure (R ⧸ M) :=
    (algebraMap (R ⧸ M) (AlgebraicClosure (R ⧸ M))).comp (Ideal.Quotient.mk M)
  have hc : ∀ o : O, g (algebraMap O K o) = fR (algebraMap O R o) := by
    intro o
    have h1 : algebraMap O K o =
        algebraMap (IsLocalRing.ResidueField O) K (IsLocalRing.residue O o) := rfl
    rw [h1, g.commutes]
    rfl
  letI : Algebra O (AlgebraicClosure (R ⧸ M)) := (fR.comp (algebraMap O R)).toAlgebra
  let FR : R →ₐ[O] AlgebraicClosure (R ⧸ M) := { fR with commutes' := fun _ ↦ rfl }
  let G : K →ₐ[O] AlgebraicClosure (R ⧸ M) :=
    { g.toRingHom with commutes' := fun o ↦ hc o }
  have h2 := congrArg (Algebra.TensorProduct.productMap FR G) hx
  have h3 : fR x = 0 := by
    simpa [FR, G] using h2
  have h4 : Ideal.Quotient.mk M x = 0 :=
    (algebraMap (R ⧸ M) (AlgebraicClosure (R ⧸ M))).injective (by simpa [fR] using h3)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h4

private theorem exists_includeLeft_eq_pow_expChar_pow (O R K : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Field K]
    [Algebra O R] [Algebra O K] [Algebra.IsIntegral O K]
    [IsSepClosed (IsLocalRing.ResidueField O)] (q : ℕ) [ExpChar (IsLocalRing.ResidueField O) q]
    (t : R ⊗[O] K) :
    ∃ n : ℕ, ∃ r : R, (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) r = t ^ q ^ n := by
  letI : Algebra (IsLocalRing.ResidueField O) K := (resMap O K).toAlgebra
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) K :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField O) K :=
    Algebra.IsIntegral.tower_top O
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) K := inferInstance
  haveI : IsPurelyInseparable (IsLocalRing.ResidueField O) K := inferInstance
  haveI : ExpChar K q :=
    expChar_of_injective_algebraMap (algebraMap (IsLocalRing.ResidueField O) K).injective q
  rcases subsingleton_or_nontrivial (R ⊗[O] K) with hs | hs
  · exact ⟨0, 0, Subsingleton.elim _ _⟩
  haveI : ExpChar (R ⊗[O] K) q :=
    expChar_of_injective_ringHom
      (f := (Algebra.TensorProduct.includeRight : K →ₐ[O] R ⊗[O] K).toRingHom)
      (RingHom.injective _) q
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r y =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem (IsLocalRing.ResidueField O) q y
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨n, algebraMap O R o * r ^ q ^ n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ← hc, Algebra.TensorProduct.includeLeftRingHom_apply]
    show (algebraMap O R o * r ^ q ^ n) ⊗ₜ[O] (1 : K) = (r ^ q ^ n) ⊗ₜ[O] (algebraMap O K o)
    rw [← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  | add a b ha hb =>
    obtain ⟨n1, r1, h1⟩ := ha
    obtain ⟨n2, r2, h2⟩ := hb
    refine ⟨n1 + n2, r1 ^ q ^ n2 + r2 ^ q ^ n1, ?_⟩
    rw [map_add, map_pow, map_pow, h1, h2, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
      add_comm n2 n1, add_pow_expChar_pow]

theorem UpperTheory.existsUnique_idempotent_lift_tensor_field_strictHenselian :
    ∀ (O R K : Type) [CommRing O] [CommRing R] [Field K] [Algebra O R] [Algebra O K] [Algebra.IsIntegral O R] [Algebra.IsIntegral O K], SH O → ∀ e' : R ⊗[O] K, IsIdempotentElem e' → ∃! e : R, IsIdempotentElem e ∧ (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) e = e' := by
  intro O R K _ _ _ _ _ _ _ hO e' he'
  obtain ⟨hH, hsep⟩ := hO
  obtain ⟨q, hq⟩ := ExpChar.exists (IsLocalRing.ResidueField O)
  have hjac : ∀ y : R, (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) y = 0 →
      ∀ Q : Ideal R, Q.IsMaximal → y ∈ Q := fun y hy Q hQ ↦ by
    haveI := hQ
    exact mem_maximal_of_includeLeft_eq_zero O R K Q y hy
  obtain ⟨n, x, hx⟩ := exists_includeLeft_eq_pow_expChar_pow O R K q e'
  have hx' : (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) x = e' := by
    have hpos : 0 < q ^ n := pow_pos (expChar_pos (IsLocalRing.ResidueField O) q) n
    obtain ⟨m, hm⟩ : ∃ m, q ^ n = m + 1 := ⟨q ^ n - 1, by omega⟩
    rw [hx, hm, he'.pow_succ_eq]
  refine existsUnique_of_exists_of_unique ?_ ?_
  · let S := Algebra.adjoin O {x}
    haveI : Module.Finite O S :=
      Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral x)
    let ψ : S →+* R ⊗[O] K :=
      (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K).comp S.val.toRingHom
    have hxS : x ∈ S := Algebra.subset_adjoin (Set.mem_singleton x)
    let c : ψ.range := ⟨e', ⟨⟨x, hxS⟩, hx'⟩⟩
    have hc : IsIdempotentElem c := Subtype.ext he'
    have hker : RingHom.ker ψ.rangeRestrict ≤ Ideal.jacobson ⊥ := by
      rw [RingHom.ker_rangeRestrict]
      intro s hs
      rw [RingHom.mem_ker] at hs
      refine Ideal.mem_sInf.mpr ?_
      rintro P ⟨-, hP⟩
      haveI := hP
      haveI : Algebra.IsIntegral S R := Algebra.IsIntegral.tower_top O
      obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := R) P (by
        intro z hz
        rw [RingHom.mem_ker] at hz
        have : z = 0 := Subtype.ext hz
        simp [this])
      rw [← hQP, Ideal.mem_comap]
      exact hjac _ hs Q hQ
    obtain ⟨e, ⟨he, hec⟩, -⟩ := GlobalTheory.existsUnique_idempotent_lift_of_henselian O ψ.rangeRestrict
      ψ.rangeRestrict_surjective hker hc
    refine ⟨(e : R), he.map S.val, ?_⟩
    exact congrArg Subtype.val hec
  · rintro y z ⟨hy, hyc⟩ ⟨hz, hzc⟩
    have hy2 : y * y = y := hy
    have hz2 : z * z = z := hz
    have he2 : e' * e' = e' := he'
    have hf0 : (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K) (y + z - 2 * y * z) = 0 := by
      rw [map_sub, map_add, map_mul, map_mul, hyc, hzc, map_ofNat]
      linear_combination (-2 : R ⊗[O] K) * he2
    have hfj : ∀ Q : Ideal R, Q.IsMaximal → y + z - 2 * y * z ∈ Q := hjac _ hf0
    have hmem : y + z - 2 * y * z ∈ Ideal.jacobson (⊥ : Ideal R) :=
      Ideal.mem_sInf.mpr (fun Q hQ ↦ hfj Q hQ.2)
    have hu := Ideal.mem_jacobson_bot.mp hmem (-1)
    have hfid : (y + z - 2 * y * z) * (y + z - 2 * y * z) = y + z - 2 * y * z := by
      linear_combination (1 + 4 * z * z - 4 * z) * hy2 + hz2
    have hff : (y + z - 2 * y * z) * ((y + z - 2 * y * z) * -1 + 1) = 0 := by
      linear_combination (-1 : R) * hfid
    have hf : y + z - 2 * y * z = 0 := (hu.mul_left_eq_zero).mp hff
    linear_combination (-1 + 2 * z) * hy2 + (1 - 2 * y) * hz2 + (y - z) * hf
