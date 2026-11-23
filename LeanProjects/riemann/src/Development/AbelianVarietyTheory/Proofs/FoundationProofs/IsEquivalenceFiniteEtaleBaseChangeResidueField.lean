import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

noncomputable section

namespace GlobalTheory

open IsLocalRing Polynomial TensorProduct

theorem ker_includeRight_residueField_le_jacobson (R B : Type*) [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] :
    RingHom.ker (Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) ≤
      (⊥ : Ideal B).jacobson := by
  intro x hx
  apply mem_jacobson_bot_of_forall_isMaximal
  intro n hn
  haveI := hn
  have hc := comap_eq_maximalIdeal_of_finite (R := R) n
  let φ : ResidueField R →ₐ[R] B ⧸ n :=
    Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R (B ⧸ n)) fun a ha => by
      rw [Algebra.ofId_apply, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem,
        ← Ideal.mem_comap, hc]
      exact ha
  let ψ := Algebra.TensorProduct.lift φ (Ideal.Quotient.mkₐ R n) fun _ _ => Commute.all _ _
  have h1 : ψ ((1 : ResidueField R) ⊗ₜ[R] x) = Ideal.Quotient.mk n x := by
    simp [ψ]
  have h0 : (1 : ResidueField R) ⊗ₜ[R] x = 0 := by
    simpa using RingHom.mem_ker.mp hx
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← h1, h0, map_zero]

theorem includeRight_residueField_surjective (R B : Type*) [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] :
    Function.Surjective (Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) := by
  have hs : Function.Surjective (algebraMap R (ResidueField R)) := IsLocalRing.residue_surjective
  exact Algebra.TensorProduct.includeRight_surjective B hs

theorem isUnit_of_isUnit_one_tmul_residueField (R : Type*) {B : Type*} [CommRing R]
    [IsLocalRing R] [CommRing B] [Algebra R B] [Module.Finite R B] {x : B}
    (hx : IsUnit ((1 : ResidueField R) ⊗ₜ[R] x)) : IsUnit x := by
  apply isUnit_of_isUnit_mk_of_le_jacobson (ker_includeRight_residueField_le_jacobson R B)
  let e := Ideal.quotientKerAlgEquivOfSurjective (includeRight_residueField_surjective R B)
  have he : e (Ideal.Quotient.mk _ x) = (1 : ResidueField R) ⊗ₜ[R] x := rfl
  have h := hx.map e.symm
  rwa [← he, AlgEquiv.symm_apply_apply] at h

theorem isLocalRing_of_isLocalRing_residueField_tensor (R B : Type*) [CommRing R]
    [IsLocalRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
    [IsLocalRing (ResidueField R ⊗[R] B)] : IsLocalRing B := by
  haveI : Nontrivial B := (includeRight_residueField_surjective R B).nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((1 : ResidueField R) ⊗ₜ[R] x) with h | h
  · exact Or.inl (isUnit_of_isUnit_one_tmul_residueField R h)
  · right
    apply isUnit_of_isUnit_one_tmul_residueField R
    rwa [TensorProduct.tmul_sub, ← Algebra.TensorProduct.one_def]

theorem existsUnique_idempotent_lift_quotient (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    {c : S ⧸ (maximalIdeal R).map (algebraMap R S)} (hc : IsIdempotentElem c) :
    ∃! e : S, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = c := by
  refine existsUnique_idempotent_lift_of_henselian R (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective ?_ hc
  rw [Ideal.mk_ker]
  exact map_maximalIdeal_le_jacobson_of_finite R S

theorem bijective_baseChange_residueField_of_etale (R A B : Type*) [CommRing R]
    [HenselianLocalRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.Etale R A] [Module.Finite R B] :
    Function.Bijective fun f : A →ₐ[R] B ↦
      Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) f := by
  have hG := bijective_algHom_comp_of_etale_of_henselian R (A := A)
    (Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B)
    (includeRight_residueField_surjective R B) (ker_includeRight_residueField_le_jacobson R B)
  have key : ∀ f : A →ₐ[R] B,
      ((Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) f).restrictScalars
        R).comp Algebra.TensorProduct.includeRight = Algebra.TensorProduct.includeRight.comp f := by
    intro f
    ext a
    simp
  refine ⟨fun f g hfg => ?_, fun h => ?_⟩
  · apply hG.1
    dsimp only at hfg ⊢
    rw [← key f, ← key g, hfg]
  · obtain ⟨f, hf⟩ := hG.2 ((h.restrictScalars R).comp Algebra.TensorProduct.includeRight)
    refine ⟨f, ?_⟩
    dsimp only at hf ⊢
    apply Algebra.TensorProduct.ext'
    intro a b
    have hb : Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) f
        ((1 : ResidueField R) ⊗ₜ[R] b) = h ((1 : ResidueField R) ⊗ₜ[R] b) := by
      have := congrArg (fun φ : A →ₐ[R] ResidueField R ⊗[R] B => φ b) hf
      simpa using this
    have hab : a ⊗ₜ[R] b = a • ((1 : ResidueField R) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hab, map_smul, map_smul, hb]

theorem etale_adjoinRoot_of_isUnit_derivative {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic)
    (h : IsUnit (AdjoinRoot.mk f f.derivative)) : Algebra.Etale R (AdjoinRoot f) := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (↑u⁻¹ : AdjoinRoot f)
  have h1 : AdjoinRoot.mk f (derivative f * p - 1) = 0 := by
    rw [map_sub, map_mul, hp, ← hu, Units.mul_inv, map_one, sub_self]
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_eq_zero.mp h1
  let P : StandardEtalePair R :=
    ⟨f, hf, 1, p, -q, 0, by rw [pow_zero]; linear_combination hq⟩
  have hunit : IsUnit (AdjoinRoot.mk P.f P.g) := by
    simp [P]
  let e2 : AdjoinRoot f ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnit (AdjoinRoot f) (Localization.Away (AdjoinRoot.mk P.f P.g)) _
      hunit).restrictScalars R
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans e2.symm)

theorem exists_etale_lift_of_isSeparable.{u} (R : Type u) (L : Type*) [CommRing R] [IsLocalRing R]
    [Field L] [Algebra (ResidueField R) L] [Module.Finite (ResidueField R) L]
    [Algebra.IsSeparable (ResidueField R) L] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
      IsLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  let pb := Field.powerBasisOfFiniteOfSeparable (ResidueField R) L
  have hsep : (minpoly (ResidueField R) pb.gen).Separable :=
    Algebra.IsSeparable.isSeparable _ pb.gen
  have hmon : (minpoly (ResidueField R) pb.gen).Monic := minpoly.monic pb.isIntegral_gen
  have hs : Function.Surjective (algebraMap R (ResidueField R)) := IsLocalRing.residue_surjective
  obtain ⟨f, hfmap, hfdeg, hf⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts _).mpr (Polynomial.map_surjective _ hs _)) hmon
  haveI hfin : Module.Finite R (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  letI : Algebra R L :=
    ((algebraMap (ResidueField R) L).comp (algebraMap R (ResidueField R))).toAlgebra
  haveI : IsScalarTower R (ResidueField R) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hroot : Polynomial.aeval pb.gen f = 0 := by
    rw [← Polynomial.aeval_map_algebraMap (ResidueField R), hfmap, minpoly.aeval]
  let g : AdjoinRoot f →ₐ[R] L := AdjoinRoot.liftAlgHom f (Algebra.ofId R L) pb.gen hroot
  let ψ : ResidueField R ⊗[R] AdjoinRoot f →ₐ[ResidueField R] L :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) g fun _ _ => Commute.all _ _
  have hψroot : ψ ((1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.root f) = pb.gen := by
    simp only [ψ, g, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hsurjψ : Function.Surjective ψ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← pb.adjoin_gen_eq_top, Algebra.adjoin_le_iff,
      Set.singleton_subset_iff]
    exact (AlgHom.mem_range ψ).mpr ⟨_, hψroot⟩
  let bT := Algebra.TensorProduct.basis (ResidueField R) (AdjoinRoot.powerBasis' hf).basis
  haveI : Module.Finite (ResidueField R) (ResidueField R ⊗[R] AdjoinRoot f) :=
    Module.Finite.of_basis bT
  have hdim : Module.finrank (ResidueField R) (ResidueField R ⊗[R] AdjoinRoot f) =
      Module.finrank (ResidueField R) L := by
    rw [Module.finrank_eq_card_basis bT, Fintype.card_fin, AdjoinRoot.powerBasis'_dim, pb.finrank,
      ← pb.natDegree_minpoly, Polynomial.natDegree_eq_of_degree_eq hfdeg]
  have hinjψ : Function.Injective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := ψ.toLinearMap)).mpr
      hsurjψ
  let e := AlgEquiv.ofBijective ψ ⟨hinjψ, hsurjψ⟩
  haveI : Nontrivial (ResidueField R ⊗[R] AdjoinRoot f) := hsurjψ.nontrivial
  haveI : IsLocalRing (ResidueField R ⊗[R] AdjoinRoot f) :=
    IsLocalRing.of_surjective' e.symm.toRingEquiv.toRingHom e.symm.surjective
  have hloc : IsLocalRing (AdjoinRoot f) := isLocalRing_of_isLocalRing_residueField_tensor R _
  have hder : IsUnit (AdjoinRoot.mk f (derivative f)) := by
    apply isUnit_of_isUnit_one_tmul_residueField R
    have h1 : ψ ((1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.mk f (derivative f)) =
        Polynomial.aeval pb.gen (derivative (minpoly (ResidueField R) pb.gen)) := by
      rw [← hfmap, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
      simp only [ψ, g, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    have h2 : IsUnit (e ((1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.mk f (derivative f))) := by
      rw [show e _ = ψ _ from rfl, h1, isUnit_iff_ne_zero]
      exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
    simpa using h2.map e.symm
  haveI := etale_adjoinRoot_of_isUnit_derivative hf hder
  exact ⟨AdjoinRoot f, inferInstance, inferInstance, hfin, inferInstance, hloc, ⟨e⟩⟩

theorem exists_etale_lift_of_etale.{u, v} (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R]
    [CommRing E] [Algebra (ResidueField R) E] [Algebra.Etale (ResidueField R) E] :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧
      Algebra.Etale R A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] E) := by
  obtain ⟨I, hI, Ai, _, _, e, hAi⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (ResidueField R) E).mp inferInstance
  have H : ∀ i, ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧
      Algebra.Etale R A ∧ IsLocalRing A ∧
        Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] Ai i) := fun i => by
    haveI := (hAi i).1
    haveI := (hAi i).2
    exact exists_etale_lift_of_isSeparable R (Ai i)
  choose A hA1 hA2 hfin het _ hiso using H
  have := Fintype.ofFinite I
  classical
  refine ⟨Π i, A i, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.piRight R (ResidueField R) (ResidueField R) A).trans
    ((AlgEquiv.piCongrRight fun i => (hiso i).some).trans e.symm)

end GlobalTheory
