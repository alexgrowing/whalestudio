import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

open Polynomial in

theorem exists_etale_subset_range_of_isPrime {A : Type} [CommRing A] (q : Ideal A) [q.IsPrime]
    {K : Type} [Field K] [Algebra A K] [Algebra q.ResidueField K]
    [IsScalarTower A q.ResidueField K] [Algebra.IsSeparable q.ResidueField K]
    {ι : Type} [Finite ι] (b : ι → K) :
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra A E) (_ : Algebra.Etale A E) (ε : E →ₐ[A] K),
      ∀ i, b i ∈ Set.range ε := by
  classical
  let k := q.ResidueField
  let L := IntermediateField.adjoin k (Set.range b)
  have : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element k L
  have hi : IsIntegral k θ := Algebra.IsIntegral.isIntegral θ
  have hr : ∀ i, ∃ r : k[X], aeval θ r = (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L) := by
    intro i
    have h₁ : (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L) ∈ Algebra.adjoin k {θ} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, hθ]
      trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h₁
    obtain ⟨g, hg⟩ := h₁
    exact ⟨g, hg⟩
  choose r hr using hr
  have := Fintype.ofFinite ι
  let T : Finset k := (minpoly k θ).coeffs ∪ Finset.univ.biUnion fun i => (r i).coeffs
  obtain ⟨⟨d, hd⟩, hdT⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (A ⧸ q)) T
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective d
  have hs : algebraMap A k s ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A (A ⧸ q) k]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd)
  let As := Localization.Away s
  let ρ : As →+* k := IsLocalization.Away.lift s (Ne.isUnit hs)
  have hρ : ∀ a : A, ρ (algebraMap A As a) = algebraMap A k a := IsLocalization.Away.lift_eq s _
  letI : Algebra As k := ρ.toAlgebra
  letI : Algebra As K := ((algebraMap k K).comp ρ).toAlgebra
  have : IsScalarTower As k K := .of_algebraMap_eq' rfl
  have : IsScalarTower A As K := .of_algebraMap_eq fun a => by
    change algebraMap A K a = algebraMap k K (ρ (algebraMap A As a))
    rw [hρ, ← IsScalarTower.algebraMap_apply]
  have hT : ∀ c ∈ T, c ∈ Set.range ρ := by
    intro c hc
    obtain ⟨a, ha⟩ := hdT c hc
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨IsLocalization.mk' As a (⟨s, 1, by simp⟩ : Submonoid.powers s), ?_⟩
    have e1 : ρ (IsLocalization.mk' As a (⟨s, 1, by simp⟩ : Submonoid.powers s)) * algebraMap A k s =
        algebraMap A k a := by
      rw [← hρ, ← hρ, ← map_mul, IsLocalization.mk'_spec]
    have e2 : c * algebraMap A k s = algebraMap A k a := by
      rw [IsScalarTower.algebraMap_apply A (A ⧸ q) k s, IsScalarTower.algebraMap_apply A (A ⧸ q) k a]
      erw [ha]
      rw [Algebra.smul_def, mul_comm]
      rfl
    exact mul_right_cancel₀ hs (e1.trans e2.symm)
  have hlift : ∀ g : k[X], (∀ c ∈ g.coeffs, c ∈ Set.range ρ) → ∃ g' : As[X], g'.map ρ = g := by
    intro g hg
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases h : g.coeff n = 0
    · exact ⟨0, by simp [h]⟩
    · exact hg _ (Polynomial.coeff_mem_coeffs h)
  obtain ⟨μ, hμ, -, hμm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap As k)
    (p := minpoly k θ) (Polynomial.mem_lifts _ |>.mpr
      (hlift _ fun c hc => hT c (Finset.mem_union_left _ hc))) (minpoly.monic hi)
  let P : StandardEtalePair As := ⟨μ, hμm, derivative μ, 1, 0, 1, by simp⟩
  have key : ∀ g : As[X], aeval (θ : K) g = (aeval θ (g.map (algebraMap As k)) : L) := fun g => by
    rw [← aeval_map_algebraMap k]
    exact aeval_algHom_apply L.val θ _
  have hP : P.HasMap (θ : K) := by
    refine ⟨by rw [key, hμ, minpoly.aeval]; rfl, Ne.isUnit ?_⟩
    rw [key, ← derivative_map, hμ]
    exact fun h => (Algebra.IsSeparable.isSeparable k θ).aeval_derivative_ne_zero
      (minpoly.aeval k θ) (Subtype.ext h)
  let ε₀ : P.Ring →ₐ[As] K := P.lift _ hP
  letI : Algebra A P.Ring := ((algebraMap As P.Ring).comp (algebraMap A As)).toAlgebra
  have : IsScalarTower A As P.Ring := .of_algebraMap_eq' rfl
  refine ⟨P.Ring, inferInstance, inferInstance, Algebra.Etale.comp A As P.Ring,
    ε₀.restrictScalars A, fun i => ?_⟩
  obtain ⟨g, hg⟩ := hlift (r i) fun c hc =>
    hT c (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hc⟩))
  refine ⟨aeval P.X g, ?_⟩
  change ε₀ (aeval P.X g) = b i
  rw [← aeval_algHom_apply, StandardEtalePair.lift_X, key]
  change ((aeval θ (g.map ρ) : L) : K) = b i
  rw [hg, hr i]

theorem exists_etale_prime_of_smooth {A C : Type} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.Smooth A C] (p : Ideal C) [p.IsPrime] :
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W) (_ : C →ₐ[A] W)
      (P : Ideal W), P.IsPrime ∧ P.comap (algebraMap A W) = p.comap (algebraMap A C) := by
  set q := p.comap (algebraMap A C) with hq
  let K := SeparableClosure q.ResidueField
  letI : Algebra A K := ((algebraMap q.ResidueField K).comp (algebraMap A q.ResidueField)).toAlgebra
  have : IsScalarTower A q.ResidueField K := .of_algebraMap_eq' rfl
  have hker : RingHom.ker (algebraMap A K) = q := by
    rw [IsScalarTower.algebraMap_eq A q.ResidueField K, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap q.ResidueField K).injective]
    exact Ideal.ker_algebraMap_residueField q
  obtain ⟨φ⟩ := nonempty_algHom_of_smooth_of_isSepClosed (R := A) (K := K) p hker.symm
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A)
    (p := RingHom.ker φ)
  let S := Localization.Away f
  let P := MvPolynomial (Fin n) A
  let φ' : S →ₐ[A] K := IsLocalization.Away.liftAlgHom f (Ne.isUnit hf)
  obtain ⟨E, _, _, _, ε, hε⟩ := exists_etale_subset_range_of_isPrime q
    fun i : Fin n => φ' (algebraMap P S (MvPolynomial.X i))
  choose c hc using hε
  let χ : P →ₐ[A] K := φ'.comp (IsScalarTower.toAlgHom A _ _)
  have hχ : ε.comp (MvPolynomial.aeval c) = χ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    exact (congrArg ε (MvPolynomial.aeval_X (R := A) c i)).trans (hc i)
  letI := (MvPolynomial.aeval (R := A) c).toAlgebra
  have : IsScalarTower A P E := .of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := A) c).commutes r).symm
  letI := χ.toAlgebra
  letI := ε.toAlgebra
  have : IsScalarTower A E K := .of_algebraMap_eq fun r => (ε.commutes r).symm
  have : IsScalarTower P E K := .of_algebraMap_eq fun r => congr($hχ r).symm
  let φ'' : S →ₐ[P] K := ⟨φ', fun r => rfl⟩
  let W := E ⊗[P] S
  let ε' : W →ₐ[E] K := Algebra.TensorProduct.lift (Algebra.ofId E K) φ'' fun _ _ => .all _ _
  have hcomm : ∀ r : A, (1 : E) ⊗ₜ[P] algebraMap A S r = algebraMap A W r := fun r => by
    change (1 : E) ⊗ₜ[P] algebraMap A S r = (algebraMap A E r) ⊗ₜ[P] (1 : S)
    rw [IsScalarTower.algebraMap_apply A P S, IsScalarTower.algebraMap_apply A P E]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm
  refine ⟨W, inferInstance, inferInstance, Algebra.Etale.comp A E W,
    ⟨(Algebra.TensorProduct.includeRight (R := P) (A := E) (B := S)).toRingHom.comp
      (algebraMap C S), fun r => ?_⟩, RingHom.ker ε', RingHom.ker_isPrime _, ?_⟩
  · change (1 : E) ⊗ₜ[P] algebraMap C S (algebraMap A C r) = algebraMap A W r
    rw [← IsScalarTower.algebraMap_apply]
    exact hcomm r
  · ext r
    rw [Ideal.mem_comap, RingHom.mem_ker,
      show ε' (algebraMap A W r) = algebraMap A K r from (ε'.restrictScalars A).commutes r,
      ← RingHom.mem_ker, hker]

theorem exists_etale_quasiSection_of_smooth : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] (x : X),
    x ∈ Set.range f → ∃ (V : Scheme.{0}) (s : V ⟶ Y), Etale (s ≫ f) ∧ x ∈ Set.range (s ≫ f) := by
  intro Y X f _ x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨U, V, hU, hV, hVU, -, hyV⟩ := exists_isAffineOpen_pair f y (O := ⊤) trivial
  obtain ⟨p, rfl⟩ : y ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have := f.smooth_appLE hU hV hVU
  have := p.isPrime
  algebraize [(f.appLE U V hVU).hom]
  obtain ⟨W, _, _, _, ψ, P, hP, hPq⟩ :=
    exists_etale_prime_of_smooth (A := Γ(X, U)) (C := Γ(Y, V)) p.asIdeal
  have hs : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W)) ≫ hU.fromSpec := by
    rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact ψ.commutes a
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)
  refine ⟨Spec (.of W), Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ⟨⟨P, hP⟩, ?_⟩⟩
  · rw [hs]
    infer_instance
  have e : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W)) ⟨P, hP⟩ =
      Spec.map (f.appLE U V hVU) p := PrimeSpectrum.ext hPq
  rw [hs]
  exact (congrArg hU.fromSpec e).trans congr($(hU.SpecMap_appLE_fromSpec f hV hVU) p)

end GlobalTheory
