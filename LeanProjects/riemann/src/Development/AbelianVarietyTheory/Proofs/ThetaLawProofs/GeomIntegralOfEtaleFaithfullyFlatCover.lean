import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteExtGeomIntegralLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralBaseChangeAndLocalization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem exists_point_over_of_idempotent {F A B : Type} [Field F] [IsAlgClosed F] [CommRing A]
    [CommRing B] [Algebra F A] [Algebra F B] [IsNoetherianRing A] (f : A →ₐ[F] B)
    (hfin : f.toRingHom.Finite) (hflat : f.toRingHom.Flat) (P : B →ₐ[F] F) (Q : A →ₐ[F] F)
    (h : ∀ e : A, IsIdempotentElem e → P (f e) = Q e) (E : B) (hE : IsIdempotentElem E)
    (hP : P E = 1) : ∃ Q' : B →ₐ[F] F, Q' E = 1 ∧ ∀ a, Q' (f a) = Q a := by
  algebraize [f.toRingHom]
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have hcl : IsClopen (PrimeSpectrum.basicOpen E : Set (PrimeSpectrum B)) :=
    PrimeSpectrum.isClopen_iff.2 ⟨E, hE, rfl⟩
  have him : IsClopen (PrimeSpectrum.comap (algebraMap A B) ''
      (PrimeSpectrum.basicOpen E : Set (PrimeSpectrum B))) :=
    ⟨PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (Algebra.IsIntegral.isIntegral) _ hcl.1,
      PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation _ hcl.2⟩
  obtain ⟨ε, hε, hεe⟩ := PrimeSpectrum.isClopen_iff.1 him
  have h1 : PrimeSpectrum.comap (algebraMap A B) ⟨RingHom.ker P, RingHom.ker_isPrime P⟩ ∈
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum A)) := by
    rw [← hεe]
    refine ⟨_, ?_, rfl⟩
    change ¬ (P E = 0)
    rw [hP]; exact one_ne_zero
  have h2 : (⟨RingHom.ker Q, RingHom.ker_isPrime Q⟩ : PrimeSpectrum A) ∈
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum A)) := by
    change ¬ (Q ε = 0)
    rw [← h ε hε]
    exact h1
  rw [← hεe] at h2
  obtain ⟨𝔮, h𝔮E, h𝔮⟩ := h2
  have hker : ∀ a : A, Q a = 0 → f a ∈ 𝔮.asIdeal := by
    intro a ha
    have : a ∈ (PrimeSpectrum.comap (algebraMap A B) 𝔮).asIdeal := by
      rw [h𝔮]; exact ha
    exact this
  have hcomp : ∀ a : A, Ideal.Quotient.mk 𝔮.asIdeal (f a) =
      algebraMap F (B ⧸ 𝔮.asIdeal) (Q a) := by
    intro a
    have := hker (a - algebraMap F A (Q a)) (by simp)
    rw [map_sub, AlgHom.commutes] at this
    exact Ideal.Quotient.eq.2 this
  have hint : (algebraMap F (B ⧸ 𝔮.asIdeal)).IsIntegral := by
    apply RingHom.IsIntegral.tower_top Q.toRingHom
    have : (algebraMap F (B ⧸ 𝔮.asIdeal)).comp Q.toRingHom =
        (Ideal.Quotient.mk 𝔮.asIdeal).comp f.toRingHom := by
      ext a; exact (hcomp a).symm
    rw [this]
    exact RingHom.IsIntegral.trans _ _ hfin.to_isIntegral
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  haveI : Algebra.IsIntegral F (B ⧸ 𝔮.asIdeal) := ⟨hint⟩
  have hbij : Function.Bijective (Algebra.ofId F (B ⧸ 𝔮.asIdeal)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ := (AlgEquiv.ofBijective _ hbij).symm
  refine ⟨φ.toAlgHom.comp (Ideal.Quotient.mkₐ F 𝔮.asIdeal), ?_, fun a => ?_⟩
  · rcases IsIdempotentElem.iff_eq_zero_or_one.1
      (hE.map (φ.toAlgHom.comp (Ideal.Quotient.mkₐ F 𝔮.asIdeal))) with h0 | h0
    · exfalso
      apply h𝔮E
      have : Ideal.Quotient.mk 𝔮.asIdeal E = 0 := φ.injective (by rw [map_zero]; exact h0)
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    · exact h0
  · change φ (Ideal.Quotient.mk 𝔮.asIdeal (f a)) = _
    rw [hcomp, AlgEquiv.commutes]; rfl

theorem exists_algHom_baseChange_away {k₀ k B L : Type} [Field k₀] [Field k] [Algebra k₀ k]
    [CommRing B] [Algebra k₀ B] [CommRing L] [Algebra k₀ L] [Algebra k L] [IsScalarTower k₀ k L]
    (e : B) (G : B →ₐ[k₀] L) (hG : G e = 1) :
    ∃ s : k ⊗[k₀] Localization.Away e →ₐ[k] L,
      ∀ b, s (1 ⊗ₜ algebraMap B (Localization.Away e) b) = G b := by
  have hu : ∀ y : Submonoid.powers e, IsUnit (G y) := by
    rintro ⟨_, n, rfl⟩
    simp [hG]
  refine ⟨Algebra.TensorProduct.lift (Algebra.ofId k L)
    (IsLocalization.liftAlgHom (S := Localization.Away e) hu) (fun _ _ => Commute.all _ _),
    fun b => ?_⟩
  simp

theorem exists_finset_integral_of_finiteType {K T L : Type} [Field K] [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] [CommRing L] [Algebra K L] (g : T →ₐ[K] L)
    (hg : ∀ x, IsIntegral K (g x)) :
    ∃ s : Set L, s.Finite ∧ (∀ y ∈ s, IsIntegral K y) ∧
      ∀ U : Subalgebra K L, s ⊆ U → ∀ x, g x ∈ U := by
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := K) (A := T)
  refine ⟨g '' t, t.finite_toSet.image _, ?_, fun U hU x => ?_⟩
  · rintro _ ⟨x, -, rfl⟩; exact hg x
  · have : Algebra.adjoin K (t : Set T) ≤ U.comap g :=
      Algebra.adjoin_le fun y hy => hU ⟨y, hy, rfl⟩
    rw [ht] at this
    exact this Algebra.mem_top

theorem finite_flat_tensor_map (K F R R₁ : Type) [CommRing K] [CommRing F] [Algebra K F]
    [CommRing R] [Algebra K R] [CommRing R₁] [Algebra R R₁] [Algebra K R₁] [IsScalarTower K R R₁]
    [Module.Finite R R₁] [Module.Flat R R₁] :
    (Algebra.TensorProduct.map (AlgHom.id F F) (IsScalarTower.toAlgHom K R R₁)).toRingHom.Finite ∧
    (Algebra.TensorProduct.map (AlgHom.id F F) (IsScalarTower.toAlgHom K R R₁)).toRingHom.Flat := by
  constructor
  · exact RingHom.Finite.tensorProductMap (f := AlgHom.id K F) (RingHom.Finite.id F)
      (g := IsScalarTower.toAlgHom K R R₁) (RingHom.finite_algebraMap.2 inferInstance)
  · exact RingHom.Flat.tensorProductMap (f := AlgHom.id F F)
      (g := IsScalarTower.toAlgHom K R R₁) (RingHom.Flat.id F)
      (RingHom.flat_algebraMap_iff.2 inferInstance)

theorem exists_geomInt_piece_of_finite_etale : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R R₁ : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] [CommRing R₁] [Algebra R R₁] [Algebra K R₁] [IsScalarTower K R R₁] (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (σ₁ : K₁ →ₐ[K] ℂ) (p : R₁ →ₐ[K] ℂ) (q : R →ₐ[K] K₁), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) → (∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (p.comp (IsScalarTower.toAlgHom K R R₁)) (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (σ₁.comp q) (fun _ _ => Commute.all _ _) e) → ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S) (j : R₁ →+* S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (ii : K₁ →+* k), GeomInt k S ∧ s.comp j = p.toRingHom ∧ (s₀.toRingHom.comp j).comp (algebraMap R R₁) = ii.comp q.toRingHom := by
  intro K _ _ _ R R₁ _ _ _ _ _ _ _ K₁ _ _ _ σ₁ p q ⟨hfin, het, hff⟩ hidem
  haveI : Algebra.Smooth K R₁ := Algebra.Smooth.comp K R R₁
  obtain ⟨k₀, e, hk₀, he, hpe, hgi⟩ := GlobalTheory.T.exists_finite_ext_geom_integral_localization K R₁ p
  haveI : IsNoetherianRing (ℂ ⊗[K] R) := Algebra.FiniteType.isNoetherianRing ℂ _
  let f : ℂ ⊗[K] R →ₐ[ℂ] ℂ ⊗[K] R₁ :=
    Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (IsScalarTower.toAlgHom K R R₁)
  obtain ⟨hf1, hf2⟩ : f.toRingHom.Finite ∧ f.toRingHom.Flat := finite_flat_tensor_map K ℂ R R₁
  let emb : k₀ ⊗[K] R₁ →ₐ[K] ℂ ⊗[K] R₁ := Algebra.TensorProduct.map k₀.val (AlgHom.id K R₁)
  let P : ℂ ⊗[K] R₁ →ₐ[ℂ] ℂ :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _)
  have hPemb : ∀ x, P (emb x) = Algebra.TensorProduct.lift k₀.val p (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [P, emb]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hPf : ∀ x, P (f x) = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ)
      (p.comp (IsScalarTower.toAlgHom K R R₁)) (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [P, f]
    | add a b ha hb => simp only [map_add, ha, hb]
  obtain ⟨Q', hQE, hQ⟩ := exists_point_over_of_idempotent f hf1 hf2 P
    (Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (σ₁.comp q) (fun _ _ => Commute.all _ _))
    (fun x hx => (hPf x).trans (hidem x hx)) (emb e) (he.map emb) ((hPemb e).trans hpe)
  let q' : R₁ →ₐ[K] ℂ := (Q'.restrictScalars K).comp Algebra.TensorProduct.includeRight
  have hq' : ∀ r, q' (algebraMap R R₁ r) = σ₁ (q r) := by
    intro r
    have := hQ (1 ⊗ₜ r)
    simpa [f, q'] using this
  have hq'int : ∀ x, IsIntegral K (q' x) := by
    intro x
    letI : Algebra K₁ ℂ := σ₁.toRingHom.toAlgebra
    haveI : IsScalarTower K K₁ ℂ := IsScalarTower.of_algebraMap_eq fun a => (σ₁.commutes a).symm
    have h1 : IsIntegral K₁ (q' x) :=
      (Algebra.IsIntegral.isIntegral (R := R) x).map_of_comp_eq q.toRingHom q'.toRingHom
        (RingHom.ext fun r => (hq' r).symm)
    exact isIntegral_trans _ h1
  obtain ⟨s₁, hs₁, hs₁i, hs₁U⟩ := exists_finset_integral_of_finiteType q' hq'int
  obtain ⟨s₂, hs₂, hs₂i, hs₂U⟩ := exists_finset_integral_of_finiteType σ₁
    (fun x => (Algebra.IsIntegral.isIntegral (R := K) x).map σ₁)
  let k : IntermediateField k₀ ℂ := IntermediateField.adjoin k₀ (s₁ ∪ s₂)
  haveI : Finite ↥(s₁ ∪ s₂) := (hs₁.union hs₂).to_subtype
  haveI : FiniteDimensional k₀ k := IntermediateField.finiteDimensional_adjoin (by
    rintro x (hx | hx)
    · exact (hs₁i x hx).tower_top
    · exact (hs₂i x hx).tower_top)
  haveI : NumberField k₀ := NumberField.of_module_finite K k₀
  haveI : NumberField k := NumberField.of_module_finite k₀ k
  have hm₁ : ∀ x, q' x ∈ k := hs₁U (k.toSubalgebra.restrictScalars K)
    (fun y hy => IntermediateField.subset_adjoin k₀ (s₁ ∪ s₂) (Or.inl hy))
  have hm₂ : ∀ x, σ₁ x ∈ k := hs₂U (k.toSubalgebra.restrictScalars K)
    (fun y hy => IntermediateField.subset_adjoin k₀ (s₁ ∪ s₂) (Or.inr hy))
  let qk : R₁ →ₐ[K] k :=
    { toRingHom := q'.toRingHom.codRestrict k hm₁
      commutes' := fun a => Subtype.ext (q'.commutes a) }
  let G : k₀ ⊗[K] R₁ →ₐ[k₀] ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId k₀ ℂ) p (fun _ _ => Commute.all _ _)
  let G₀ : k₀ ⊗[K] R₁ →ₐ[k₀] k :=
    Algebra.TensorProduct.lift (Algebra.ofId k₀ k) qk (fun _ _ => Commute.all _ _)
  have hG : ∀ x, G x = Algebra.TensorProduct.lift k₀.val p (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have hG₀ : ∀ x, (G₀ x : ℂ) = Q' (emb x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have : emb (a ⊗ₜ b) = (a : ℂ) • ((1 : ℂ) ⊗ₜ[K] b) := by
        simp [emb, TensorProduct.smul_tmul']
      rw [this, map_smul, smul_eq_mul]
      rfl
    | add a b ha hb => simp only [map_add, ← ha, ← hb]; rfl
  obtain ⟨s, hs⟩ := exists_algHom_baseChange_away (k := k) e G ((hG e).trans hpe)
  obtain ⟨s₀, hs₀⟩ := exists_algHom_baseChange_away (k := k) e G₀
    (Subtype.ext ((hG₀ e).trans hQE))
  refine ⟨k, inferInstance, inferInstance, k ⊗[k₀] Localization.Away e, inferInstance,
    inferInstance,
    (Algebra.TensorProduct.includeRight (R := k₀) (A := k)).toRingHom.comp
      ((algebraMap (k₀ ⊗[K] R₁) (Localization.Away e)).comp
        (Algebra.TensorProduct.includeRight (R := K) (A := k₀)).toRingHom),
    s.toRingHom, s₀, σ₁.toRingHom.codRestrict k hm₂, (geomInt_baseChange_and_away k₀ k _ hgi).1, ?_, ?_⟩
  · ext x
    refine (hs (1 ⊗ₜ x)).trans ?_
    simp [G]
  · refine RingHom.ext fun x => ?_
    refine (hs₀ (1 ⊗ₜ algebraMap R R₁ x)).trans (Subtype.ext ?_)
    rw [hG₀]
    exact Eq.trans (by simp [emb, q']) (hq' x)

end GlobalTheory.KeyFam
