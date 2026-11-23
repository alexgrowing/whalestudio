import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKummerFieldOfPowerIdealRootsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllipticTorsionPointCoordinatesFiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgebraicOfEllipticTorsionCoordinatesFiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldFinrankPowPrincipalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdFinrankStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotInjectiveTwoPrimesEqualNormCofiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwoPrimesSameNormOfTrivialFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureFrobeniusElementsEqTopStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormModEqOneOfPrincipalRayClassStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityMemRayClassFieldOfMultipleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratorPowPrimeOneModModulusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterValueViaPowerGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharacterValueMemKummerFieldStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.Mem.BaseExt
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

section Prescribed

def toComap {F K : IntermediateField ℚ ℂ} (h : F ≤ K) : F →+* (F.comap K.val) where
  toFun x := ⟨⟨x, h x.2⟩, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem image_comap {E : Type} [Field E] {F K : IntermediateField ℚ ℂ} (h : F ≤ K) (𝔞 : Ideal (𝓞 E)) (τ : E →+* ℂ)
    (e : E → K) (he : ∀ a, (e a : ℂ) = τ a) :
    extend (toComap h) (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)}) =
      Submodule.span (𝓞 (F.comap K.val)) {x : F.comap K.val | ∃ a ∈ 𝔞, (x : K) = e (a : E)} := by
  rw [extend_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
    exact ⟨a, ha, Subtype.ext (hy.trans (he _).symm)⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨⟨x.1.1, x.2⟩, ⟨a, ha, (congrArg Subtype.val hx).trans (he _)⟩, rfl⟩

theorem kPsi_comap {R : Ranks} (H : Host R) {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) [FiniteDimensional ℚ F]
    (hV : kummerField H.φ₀ (classNumber H.E) ≤ F) (e : H.E →+* K) (he : ∀ a, (e a : ℂ) = H.φ₀ a) (p q : ℕ)
    (𝔞 : Ideal (𝓞 H.E)) (h𝔞 : 𝔞 ≠ ⊥) : ∃ β : F.comap K.val, β ≠ 0 ∧
    Submodule.span (𝓞 (F.comap K.val)) {β} =
      ∏ g : Tau R,
        (Submodule.span (𝓞 (F.comap K.val)) {x : F.comap K.val | ∃ a ∈ 𝔞, (x : K) = e (H.sigmaOf g (a : H.E))} ^ p *
          Submodule.span (𝓞 (F.comap K.val))
            {x : F.comap K.val | ∃ a ∈ 𝔞, (x : K) = e (H.sigmaOf g (H.conj (a : H.E)))} ^ q) ∧
    ∀ σ : F.comap K.val →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ (p + q) := by
  have hcm : IsCMField H.E := H.isCMField_hostE
  have hgal : IsGalois ℚ H.E := H.hostE_isGalois
  let f := toComap hFK
  obtain ⟨β, hβ, hsp, hn⟩ := typeNorm_of_kummer _ (typeExp H p q) _ (typeExp_add H _ _) F hV 𝔞 h𝔞
  refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
  have h := congrArg (extend f) hsp
  rw [prod_typeExp, extend_span, Set.image_singleton, map_prod] at h
  refine h.trans (Finset.prod_congr rfl fun g _ => ?_)
  have e1 := image_comap hFK 𝔞 (H.emb g) (fun a => e (H.sigmaOf g a)) fun _ => he _
  have e2 := image_comap hFK 𝔞 (ComplexEmbedding.conjugate (H.emb g)) (fun a => e (H.sigmaOf g (H.conj a)))
    fun a => (he _).trans (conjugate_emb_apply H g a).symm
  rw [map_mul, map_pow, map_pow]
  exact congrArg₂ (· * ·) (congrArg (· ^ p) e1) (congrArg (· ^ q) e2)

theorem capit_comap {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K)
    [FiniteDimensional ℚ F] (hV : kummerField φ (classNumber E) ≤ F) (e : E →+* K) (he : ∀ a, (e a : ℂ) = φ a)
    (𝔞 : Ideal (𝓞 E)) : ∃ β : F.comap K.val, Submodule.span (𝓞 (F.comap K.val)) {β} =
      Submodule.span (𝓞 (F.comap K.val)) {x : F.comap K.val | ∃ a ∈ 𝔞, (x : K) = e (a : E)} := by
  obtain ⟨β, hsp⟩ := capit_of_kummer _ F hV 𝔞
  refine ⟨toComap hFK β, ?_⟩
  have h := congrArg (extend (toComap hFK)) hsp
  rw [extend_span, Set.image_singleton] at h
  exact h.trans (image_comap hFK 𝔞 φ e he)

theorem exists_gens_le (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] : ∃ S : Finset ℂ,
    (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ K : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ K) → F ≤ K := by
  have : NumberField F := NumberField.mk
  obtain ⟨S, hS, h⟩ := exists_gens F
  exact ⟨S, hS, fun K hK z hz => h K hK F.val.toRingHom ⟨z, hz⟩⟩

theorem exists_base_ks (B : Pre) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F]
    (hV : kummerField B.host.φ₀ (classNumber B.host.E) ≤ F) (hr : rootsField B ≤ F)
    (hp : rootOne B.host.pde ∈ F) (hp' : rootOne B.host.pde' ∈ F) (S : Finset ℂ) (hSa : ∀ z ∈ S, IsAlgebraic ℚ z) :
    ∃ B' : Base, B'.toPre = B ∧ (∀ z, (∃ x ∈ B'.Ks, B'.embLL x = z) ↔ z ∈ F) ∧
      ∀ z ∈ S, ∃ x ∈ B'.LL0, B'.embLL x = z := by
  classical
  have hcm : IsCMField B.host.E := B.host.isCMField_hostE
  have hgal : IsGalois ℚ B.host.E := B.host.hostE_isGalois
  obtain ⟨SF, hSF, hF⟩ := exists_gens_le F
  let A : Finset ℕ := {B.ramOrder} ∪ Finset.univ.image B.T
  let SR : Finset ℂ := A.image fun N : ℕ => Complex.exp (2 * Real.pi * Complex.I / N)
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable (S ∪ SF ∪ SR) (by
      intro z hz
      simp only [Finset.mem_union] at hz
      rcases hz with (hz | hz) | hz
      exacts [hSa z hz, hSF z hz, by
        obtain ⟨N, -, rfl⟩ := Finset.mem_image.1 hz
        exact isAlgebraic_exp N])
  simp only [Finset.mem_union] at hS
  have hFK : F ≤ K := hF K fun z hz => hS z (by tauto)
  obtain ⟨hEF, hh, -⟩ := (kummerField_le_iff _).1 hV
  have hEK : ∀ x, B.host.φ₀ x ∈ K := fun x => hFK (hEF x)
  have hR : ∀ N ∈ A, Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K := fun N hN => by
    have hz : Complex.exp (2 * Real.pi * Complex.I / N) ∈ SR := Finset.mem_image.2 ⟨N, hN, rfl⟩
    exact hS _ (by tauto)
  have : NumberField K := {}
  simp only [rootsField, sup_le_iff, cycField_le_iff] at hr
  obtain ⟨⟨⟨⟨hr1, hr2⟩, hr3⟩, hr4⟩, hr5⟩ := hr
  refine ⟨{ toPre := B
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := B.host.φ₀.codRestrict K hEK
            embE_φ₀ := rfl
            LL0 := ⊤
            coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm
            Ks := F.comap K.val
            Ks_le := le_top
            E_le_Ks := hEF
            roots_Ks := ?_
            roots_Ks' := ?_
            capit := capit_comap _ hFK hV _ fun _ => rfl
            kPsi := fun j _ _ => kPsi_comap B.host hFK hV _ (fun _ => rfl) _ _
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := ⟨⟨_, hR B.ramOrder (by simp [A])⟩, trivial, rfl⟩
            roots_LL := fun u => ⟨⟨_, hR (B.T u) (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (Finset.mem_univ u)))⟩, rfl⟩ }, rfl, ?_, ?_⟩
  · intro N hN
    have h : rootOne N ∈ F := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
      rcases hN with rfl | rfl | rfl | rfl | rfl <;> assumption
    exact ⟨⟨_, hFK h⟩, h, rfl⟩
  · intro N hN
    have h : rootOne N ∈ F := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
      rcases hN with rfl | rfl | rfl <;> assumption
    exact ⟨⟨_, hFK h⟩, h, rfl⟩
  · intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · exact fun hz => ⟨⟨z, hFK hz⟩, hz, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (by tauto)⟩, trivial, rfl⟩

end Prescribed

section Ray

variable {E : Type} [Field E] [NumberField E]

theorem aut_eq_one (S : Set (HeightOneSpectrum (𝓞 E))) (hS : S.Finite) (F : Type) [Field F] [NumberField F]
    [Algebra E F] (h : ∀ v : HeightOneSpectrum (𝓞 E), v ∉ S → IsFrob F v 1) (σ : F ≃ₐ[E] F) : σ = 1 := by
  by_contra hσ
  obtain ⟨T, hT, H⟩ := GlobalTheory.T.exists_two_primes_same_norm_of_trivial_frobenius E F σ hσ
  choose P Q hne hP hQ nP nQ using fun v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S ∪ T} =>
    H v.1 (fun hv => v.2 (Or.inr hv)) (h v.1 fun hv => v.2 (Or.inl hv))
  let f : {v : HeightOneSpectrum (𝓞 E) // v ∉ S ∪ T} × Bool → HeightOneSpectrum (𝓞 F) :=
    fun x => bif x.2 then P x.1 else Q x.1
  have ho : ∀ x, (f x).asIdeal.under (𝓞 E) = x.1.1.asIdeal := by
    rintro ⟨v, _ | _⟩
    exacts [(hQ v).over.symm, (hP v).over.symm]
  refine GlobalTheory.T.not_injective_two_primes_equal_norm_cofinite E F _ (hS.union hT) f ?_ ?_
  · rintro ⟨v, b⟩ ⟨w, c⟩ e
    obtain rfl : v = w := Subtype.ext (HeightOneSpectrum.ext ((ho (v, b)).symm.trans (by rw [e]; exact ho (w, c))))
    rcases b with _ | _ <;> rcases c with _ | _
    exacts [rfl, absurd e.symm (hne v), absurd e (hne v), rfl]
  · rintro ⟨v, _ | _⟩
    exacts [nQ v, nP v]

theorem rootOne_mem_ray [IsTotallyComplex E] (φ : E →+* ℂ) {n p : ℕ} (hn : n ≠ 0) (hp : p ∣ n)
    {M : IntermediateField ℚ ℂ} (hM : IsRayFieldIn φ (natIdeal E n) M) : rootOne p ∈ M := by
  classical
  have hp0 : p ≠ 0 := ne_zero_of_dvd_ne_zero hn hp
  have := hM.numberField
  obtain ⟨SM, hSM, hle⟩ := exists_gens_le M
  obtain ⟨L, hfd, hgal, hS, -, -⟩ := GlobalTheory.exists_galois_subfield_conj_stable (insert (rootOne p) SM) (by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    exacts [isAlgebraic_exp p, hSM z hz])
  have hML : M ≤ L := hle L fun z hz => hS z (Finset.mem_insert_of_mem hz)
  have : NumberField L := {}
  let := algOf φ M hM.emb_mem
  let := algOf φ L fun x => hML (hM.emb_mem x)
  let : Algebra M L := (IntermediateField.inclusion hML).toRingHom.toAlgebra
  have : IsScalarTower E M L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois E L := IsGalois.tower_top_of_isGalois ℚ E L
  have hq : natIdeal E n ≤ Ideal.span {(p : 𝓞 E)} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hp)
  have hfin : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ natIdeal E n}.Finite :=
    Ideal.finite_factors (natIdeal_ne_bot hn)
  obtain ⟨x, hx⟩ := GlobalTheory.T.rootsOfUnity_mem_rayClassField_of_multiple E M L _ p hp0 hq hM.isRayField
    (GlobalTheory.T.closure_frobeniusElements_eq_top E L _ hfin fun F _ _ _ => aut_eq_one _ hfin F) (GlobalTheory.T.absNorm_modEq_one_of_principal_rayClass E _ p hq)
    ⟨rootOne p, hS _ (Finset.mem_insert_self _ _)⟩
    (Subtype.ext (Complex.isPrimitiveRoot_exp p hp0).pow_eq_one)
  have e : (x : ℂ) = rootOne p := congrArg Subtype.val hx
  exact e ▸ x.2

theorem valueField_le [IsGalois ℚ E] [IsTotallyComplex E] (φ₀ : E →+* ℂ) {𝔮 : Ideal (𝓞 E)} (h𝔮 : 𝔮 ≠ ⊥)
    {M : IntermediateField ℚ ℂ} [NumberField M] (hM : IsRayFieldIn φ₀ 𝔮 M) {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar E) (n : I → ℤ) (r : ℤ)
    (hi : χ.HasInf φ n) (he : ∀ i, Even (n i - r)) (hu : ∀ v, ¬ v.asIdeal ∣ 𝔮 → χ.UnrAt v) (ht : ∀ v, χ.TameAt v) :
    valueField χ ((r : ℝ) / 2) ≤ kummerField φ₀ (degOver φ₀ M hM.emb_mem) := by
  classical
  rw [valueField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨v, hv, rfl⟩
  let := algOf φ₀ M hM.emb_mem
  obtain ⟨k, hk, hk1⟩ := GlobalTheory.T.exists_generator_pow_prime_one_mod_modulus E 𝔮 _ h𝔮 (GlobalTheory.T.rayClassField_finrank_pow_principal E M 𝔮 hM.isRayField) v
  have hfin := Ideal.finite_factors h𝔮
  refine GlobalTheory.T.algebraicHeckeCharacter_value_mem_kummerField E φ₀ I φ hφ χ n r hi he v _ k hk
    (GlobalTheory.T.tameHeckeCharacter_value_via_power_generator E χ (hfin.toFinset.erase v) (fun w hw => ?_) (fun w _ => ht w) v (Finset.notMem_erase _ _) _ k hk
      fun w hw => ?_)
  · by_cases e : w = v
    · exact e ▸ hv
    · exact hu w fun h => hw (Finset.mem_erase.2 ⟨e, hfin.mem_toFinset.2 h⟩)
  · exact hk1 w (Finset.mem_erase.1 hw).1 (hfin.mem_toFinset.1 (Finset.mem_erase.1 hw).2)

theorem tameAt_of_unrAt {χ : HChar E} {v : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt v) : χ.TameAt v :=
  fun x hx _ => h x hx

end Ray

section Omega

variable {P : Pre} (D : FieldDat P) (C : Chars P)

theorem host_cplx (P : Pre) : IsTotallyComplex P.host.E := by
  have := P.host.isCMField_hostE
  infer_instance

theorem classNumber_dvd_hstar : classNumber P.host.E ∣ D.hstar := by
  let := algOf P.host.φ₀ D.ray D.isRay.emb_mem
  exact GlobalTheory.T.classNumber_dvd_finrank_alt P.host.E D.ray _ (natIdeal_ne_bot (modulus_ne_zero P)) D.isRay.isRayField

theorem kummer_le_V : kummerField P.host.φ₀ (classNumber P.host.E) ≤ D.V :=
  kummerField_mono _ D.hstar_pos.ne' (classNumber_dvd_hstar D)

theorem finite_adjoin_roots {n : ℕ} (hn : n ≠ 0) {a : ℂ} (ha : IsIntegral ℚ a) :
    FiniteDimensional ℚ (IntermediateField.adjoin ℚ {z : ℂ | z ^ n = a}) := by
  have : Finite {z : ℂ | z ^ n = a} := by
    refine Set.Finite.subset (Polynomial.nthRoots n a).toFinset.finite_toSet fun z hz => ?_
    simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn)] using hz
  refine IntermediateField.finiteDimensional_adjoin fun z hz => IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
  rw [show z ^ n = a from hz]
  exact ha

theorem finite_cycField (N : ℕ) : FiniteDimensional ℚ (cycField N) :=
  IntermediateField.adjoin.finiteDimensional (isAlgebraic_exp N).isIntegral

theorem finite_M' : FiniteDimensional ℚ D.M' := by
  have := D.good.numberField
  have := D.good.isElliptic
  have : (D.curve.baseChange ℂ).IsElliptic := inferInstanceAs (D.curve.map (algebraMap D.jField ℂ)).IsElliptic
  have hfin := GlobalTheory.T.ellipticTorsionPointCoordinates_finite (D.curve.baseChange ℂ) 12 (by norm_num)
  have h1 : FiniteDimensional ℚ ℚ⟮sqrtNegNat P.host.d⟯ := IntermediateField.adjoin.finiteDimensional
    (IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast _).neg))
  have h2 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (torsionCoords (D.curve.baseChange ℂ) 12)) := by
    have := hfin.to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun z hz =>
      (GlobalTheory.T.isAlgebraic_of_ellipticTorsionCoordinates_finite D.jField D.curve 12 hfin z hz).isIntegral
  have h3 := finite_adjoin_roots (n := 12) (a := (D.curve.Δ : ℂ)) (by norm_num)
    ((Algebra.IsIntegral.isIntegral (R := ℚ) D.curve.Δ).map D.jField.val)
  unfold FieldDat.M' discField torsionField hilbertField
  infer_instance

theorem finite_Om : FiniteDimensional ℚ D.Om := by
  have h1 := finite_M' D
  have h2 := finite_cycField (rootOrder P)
  have h3 : FiniteDimensional ℚ D.V := GlobalTheory.T.finiteDimensional_kummerFieldOfPowerIdealRoots _ _ _ D.hstar_pos.ne'
  unfold FieldDat.Om
  infer_instance

theorem dvd_card_GL {g r : ℕ} (hg : g.Prime) (hr : 2 ≤ r) : g * (g - 1) ∣ Nat.card (GL (Fin r) (ZMod g)) := by
  have := Fact.mk hg
  rw [Matrix.card_GL_field, ZMod.card]
  refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨r - 1, by omega⟩ : Fin r)))
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  refine ⟨g ^ s, ?_⟩
  show g ^ (s + 2) - g ^ (s + 1) = _
  rw [mul_right_comm, Nat.mul_sub_one]
  congr 1 <;> ring

theorem rootsField_le_Om : rootsField P ≤ D.Om := by
  have hr : 2 ≤ P.R.r := by
    have := P.R.two_le_m
    have := P.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hf : P.R.f ≠ 0 := mul_ne_zero two_ne_zero P.R.ord_pos.ne'
  have hg : ∀ k, P.host.g k * (P.host.g k - 1) ∣ P.restRowsFiniteGroupCard := fun k =>
    ((dvd_card_GL (P.host.g_prime k) hr).trans (dvd_pow_self _ hf)).trans
      (Finset.dvd_prod_of_mem (fun k : Fin 2 => Nat.card (GL (Fin P.R.r) (ZMod (P.host.g k))) ^ P.R.f)
        (Finset.mem_univ k))
  have key : ∀ {N}, N ∣ rootOrder P → cycField N ≤ D.Om := fun h =>
    (cycField_mono (rootOrder_ne_zero P) h).trans D.cycField_le_Om
  have h1 : P.restRowsFiniteGroupCard ∣ rootOrder P := Nat.dvd_lcm_left _ _
  have h2 : 3 ^ 4 * 5 ^ 4 ∣ rootOrder P := Nat.dvd_lcm_right _ _
  exact sup_le (sup_le (sup_le (sup_le (key h1) (key ((hg 0).trans h1))) (key ((hg 1).trans h1)))
    (key ((dvd_mul_right _ _).trans h2))) (key ((dvd_mul_left _ _).trans h2))

theorem KPsi_le_V (j : ℕ) : D.KPsi j ≤ D.V := by
  refine le_trans (sup_le (sup_le (imField_le_kummerField _ _) (cycField_le_kummerField _ _)) ?_) (kummer_le_V D)
  rw [IntermediateField.adjoin_le_iff]
  rintro z ⟨i, hz⟩
  have hγ : (D.basis.γ i : P.host.E) ∈ powIdealElts P.host.E (D.basis.h i) :=
    ⟨(D.basis.γ i).ne_zero, D.basis.c i, by
      rw [← coe_toPrincipalIdeal, ← D.basis.pow_eq i, Units.val_pow_eq_pow_val]; rfl⟩
  refine kummerField_mono _ (classNumber_ne_zero _) (orderOf_dvd_card : D.basis.h i ∣ _) (mem_kummerField _ ?_ hz)
  have hσ : ∀ (σ : P.host.E ≃ₐ[ℚ] P.host.E) {x}, x ∈ powIdealElts P.host.E (D.basis.h i) →
      σ x ∈ powIdealElts P.host.E (D.basis.h i) := fun σ _ hx => map_mem_pow (σ : P.host.E →+* P.host.E) hx
  exact prod_mem_pow _ _ fun g _ => mul_mem_pow (npow_mem_pow (hσ _ hγ) _) (npow_mem_pow (hσ _ (hσ _ hγ)) _)

theorem value_le_V (χ : HChar P.host.E) (n : P.R.Psi → ℤ) (r : ℤ) (hi : χ.HasInf (embPsi P.host) n)
    (he : ∀ i, Even (n i - r)) (hu : ∀ v, (∀ p, p ∣ modulus P → OverP P.host p v → p = 0) → χ.UnrAt v)
    (ht : ∀ v, χ.TameAt v) : valueField χ ((r : ℝ) / 2) ≤ D.V := by
  have := host_cplx P
  have : IsGalois ℚ P.host.E := P.host.hostE_isGalois
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm P.R P.host
  refine valueField_le _ (natIdeal_ne_bot (modulus_ne_zero P)) D.isRay _ hcm.bij χ n r hi he
    (fun v hv => hu v fun p hp ho => absurd ?_ hv) ht
  obtain ⟨k, hk⟩ := hp
  rw [Ideal.dvd_span_singleton, hk, Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ ho

theorem delta_le_V {p : ℕ} (hp : p ∣ modulus P) {χ : HChar P.host.E} (h : IsDelta (H := P.host) p χ) :
    valueField χ 0 ≤ D.V := by
  have := host_cplx P
  obtain ⟨n, hn, ho⟩ := h.fin
  have := value_le_V D χ (fun _ => 0) 0 (fun k => by simp [GlobalTheory.TypeValues.inf_eq_one χ hn ho k]) (fun _ => by simp)
    (fun v hv => h.unr v fun ho => ne_zero_of_dvd_ne_zero (modulus_ne_zero P) hp (hv p hp ho)) h.tame
  simpa using this

theorem chiPsi_le_V : valueField C.chiPsi 0 ≤ D.V := by
  simpa using value_le_V D C.chiPsi (fun _ => 2) 0 C.isChi.inf (fun _ => by simp) (fun v _ => C.isChi.unr v)
    fun v => tameAt_of_unrAt (C.isChi.unr v)

theorem pde_dvd (P : Pre) : P.host.pde ∣ modulus P := (dvd_mul_left _ _).mul_right _

theorem pde'_dvd (P : Pre) : P.host.pde' ∣ modulus P := dvd_mul_left _ _

theorem charField_le_Om : charField C ≤ D.Om := by
  refine sup_le (sup_le (sup_le (sup_le (iSup_le fun j => ?_) ?_) ?_) ?_) ?_
  · obtain ⟨n, hn, hi⟩ := (C.isMu0 j).inf
    have hg : ∀ k, P.host.g k ∣ modulus P := fun k => by
      fin_cases k
      · exact ((dvd_mul_right _ _).mul_right _).mul_right _
      · exact ((dvd_mul_left _ _).mul_right _).mul_right _
    have := value_le_V D (C.mu0 j) n 0 hi (fun i => by
        obtain ⟨z, hz⟩ := (P.hc i).e_int j
        have h1 : (n i : ℚ) = 2 * -(P.hc i).e j := hn i
        rw [hz] at h1
        have h2 : n i = 2 * -z := by exact_mod_cast h1
        exact ⟨-z, by rw [h2]; ring⟩)
      (fun v hv => (C.isMu0 j).unr v fun k ho => (P.host.g_prime k).ne_zero (hv _ (hg k) ho)) (C.isMu0 j).tame
    simpa using this.trans D.V_le_Om
  · simpa using (value_le_V D C.eta (fun _ => 1) 1 C.isEta.inf (fun _ => by simp) (fun v _ => C.isEta.unr v)
      fun v => tameAt_of_unrAt (C.isEta.unr v)).trans D.V_le_Om
  · exact (delta_le_V D (pde_dvd P) C.isDel).trans D.V_le_Om
  · exact (delta_le_V D (pde'_dvd P) C.isDel').trans D.V_le_Om
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, a, rfl⟩
    exact rootsField_le_Om D (om_mem_rootsField C k a)

theorem listField_le_Om : listField D C ≤ D.Om :=
  (listField_le_iff D C).2 ⟨D.imField_le_Om, D.M'_le_Om, D.ray_le_Om, rootsField_le_Om D, charField_le_Om D C,
    fun j _ _ => (KPsi_le_V D j).trans D.V_le_Om⟩

end Omega

theorem exists_base_fieldsOK (hR : RayField) (P : Pre) (D : FieldDat P) (C : Chars P) (c M : ℕ) (S₁ S₂ : Finset ℂ)
    (h₁ : ∀ z ∈ S₁, IsAlgebraic ℚ z) (h₂ : ∀ z ∈ S₂, IsAlgebraic ℚ z) :
    ∃ (B : Base) (h : B.toPre = P), B.FieldsOK (h ▸ D) (h ▸ C) c M ∧ B.KsC = D.Om ∧
      (∀ z ∈ S₁, z ∈ B.fixedCoefficientFieldInComplex) ∧ ∀ z ∈ S₂, z ∈ B.LLC := by
  classical
  have := host_cplx P
  have := finite_Om D
  have hray : ∀ n : ℕ, n ≠ 0 → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ K : IntermediateField ℚ ℂ,
      (∀ z ∈ S, z ∈ K) → ∃ R, IsRayFieldIn P.host.φ₀ (natIdeal P.host.E n) R ∧ R ≤ K := fun n hn => by
    obtain ⟨R, h⟩ := exists_isRayFieldIn P.host.φ₀ hR (natIdeal_ne_bot hn)
    have := h.numberField
    obtain ⟨S, hS, hle⟩ := exists_gens_le R
    exact ⟨S, hS, fun K hK => ⟨R, h, hle K hK⟩⟩
  choose ST hST hT using fun u => hray (P.T u) (P.T_prime u).ne_zero
  obtain ⟨SG, hSG, hG⟩ := hray _ (mul_ne_zero (P.host.g_prime 0).ne_zero (P.host.g_prime 1).ne_zero)
  obtain ⟨B, rfl, hK', hS⟩ := exists_base_ks P D.Om ((kummer_le_V D).trans D.V_le_Om) (rootsField_le_Om D)
    (D.ray_le_Om (rootOne_mem_ray _ (modulus_ne_zero P) (pde_dvd P) D.isRay))
    (D.ray_le_Om (rootOne_mem_ray _ (modulus_ne_zero P) (pde'_dvd P) D.isRay))
    (S₁ ∪ S₂ ∪ SG ∪ Finset.univ.biUnion ST ∪
      ({15 ^ c, P.host.pde ^ (2 * M), P.host.pde' ^ (2 * M)} : Finset ℕ).image rootOne) (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hz
      rcases hz with (((hz | hz) | hz) | ⟨u, -, hz⟩) | ⟨N, -, rfl⟩
      exacts [h₁ z hz, h₂ z hz, hSG z hz, hST u z hz, isAlgebraic_exp N])
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, ← Base.mem_LL0C] at hS
  have hK : B.KsC = D.Om := IntermediateField.ext hK'
  have hN : ∀ N ∈ ({15 ^ c, B.host.pde ^ (2 * M), B.host.pde' ^ (2 * M)} : Finset ℕ), rootOne N ∈ B.fixedCoefficientFieldInComplex :=
    fun N hN => hS _ (Or.inr ⟨N, hN, rfl⟩)
  refine ⟨B, rfl, (B.fieldsOK_iff D C c M).2 ⟨⟨hK ▸ listField_le_Om D C, hK.le⟩,
    ((chiPsi_le_V D C).trans D.V_le_Om).trans (hK.ge.trans B.KsC_le_LL0C),
    ⟨hN _ (by simp), hN _ (by simp), hN _ (by simp)⟩,
    fun u => hT u _ fun z hz => B.fixedField_le_coefficientField (hS z (Or.inl (Or.inr ⟨u, Finset.mem_univ _, hz⟩))),
    hG _ fun z hz => B.fixedField_le_coefficientField (hS z (Or.inl (Or.inl (Or.inr hz))))⟩, hK,
    fun z hz => hS z (Or.inl (Or.inl (Or.inl (Or.inl hz)))),
    fun z hz => B.fixedField_le_coefficientField (hS z (Or.inl (Or.inl (Or.inl (Or.inr hz)))))⟩

end GlobalTheory.Mem.FieldsEx

end
