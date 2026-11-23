import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealPrimeAvoidingVariable
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GenericTrdeg

theorem exists_hom_of_ker_eq {R K K' : Type} [CommRing R] [Field K] [Field K'] (φ : R →+* K) (θ : R →+* K')
    (hk : RingHom.ker θ = RingHom.ker φ) (hs : ∀ z : K, ∃ a b, z = φ a / φ b) :
    ∃ j : K →+* K', j.comp φ = θ := by
  letI : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  haveI : IsFractionRing (R ⧸ RingHom.ker φ) K := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨a, b, h⟩ := hs z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  let g : (R ⧸ RingHom.ker φ) →+* K' := Ideal.Quotient.lift _ θ (fun a ha => by rw [← hk] at ha; exact ha)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hk]
    exact ha
  refine ⟨IsFractionRing.lift hg, ?_⟩
  ext a
  exact IsFractionRing.lift_algebraMap (K := K) hg (Ideal.Quotient.mk _ a)

theorem exists_local_domain {A K : Type} [CommRing A] [Field K] (e : A →+* K) (P : Ideal A) [P.IsPrime]
    (hP : P ≤ RingHom.ker e) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (ρ : A →+* R') (ψ : R' →+* K),
      RingHom.ker ρ = P ∧ ψ.comp ρ = e ∧ ∀ r, ψ r ≠ 0 → IsUnit r := by
  let e' : A ⧸ P →+* K := Ideal.Quotient.lift P e (fun a ha => hP ha)
  haveI : (RingHom.ker e').IsPrime := RingHom.ker_isPrime e'
  let R' := Localization.AtPrime (RingHom.ker e')
  have hu : ∀ y : (RingHom.ker e').primeCompl, IsUnit (e' y) := fun y =>
    isUnit_iff_ne_zero.2 y.2
  have hinj : Function.Injective (algebraMap (A ⧸ P) R') :=
    IsLocalization.injective R' (RingHom.ker e').primeCompl_le_nonZeroDivisors
  refine ⟨R', inferInstance, inferInstance, (algebraMap (A ⧸ P) R').comp (Ideal.Quotient.mk P),
    IsLocalization.lift hu, ?_, ?_, ?_⟩
  · ext a
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
  · ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  · intro r hr
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker e').primeCompl r
    rw [IsLocalization.AtPrime.isUnit_mk'_iff R' (RingHom.ker e')]
    intro ha
    apply hr
    rw [IsLocalization.lift_mk']
    rw [show e' a = 0 from ha, zero_mul]

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (h : spMap f = spMap f') : f = f' := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem exists_factor {X : Scheme.{0}} {R R' K : Type} [CommRing R] [CommRing R'] [Field K] (x : Sp R ⟶ X)
    [IsOpenImmersion x] (x' : Sp R' ⟶ X) (φ : R →+* K) (ψ : R' →+* K) (hψ : ∀ r, ψ r ≠ 0 → IsUnit r)
    (h : spMap ψ ≫ x' = spMap φ ≫ x) : ∃ χ : R →+* R', spMap χ ≫ x = x' ∧ ψ.comp χ = φ := by
  have hr : Set.range x' ⊆ Set.range x := by
    rintro _ ⟨q, rfl⟩
    let pt : Sp K := (⊥ : PrimeSpectrum K)
    have hsp : q ⤳ spMap ψ pt := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      intro r hr
      change ψ r ∈ (⊥ : Ideal K)
      by_contra hne
      exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hr (hψ r hne))
    have hmem : x' (spMap ψ pt) ∈ Set.range x := by
      rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    exact (hsp.map x'.continuous).mem_open x.isOpenEmbedding.isOpen_range hmem
  have hχ : spMap (Spec.preimage (IsOpenImmersion.lift x x' hr)).hom ≫ x = x' := by
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  refine ⟨_, hχ, spMap_inj ?_⟩
  rw [← cancel_mono x, ← spMap_comp, Category.assoc, hχ, h]

theorem exists_algebraicIndependent : Out.Laws → Out.Laws2 → ∀ (n : ℕ), ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : ThetaFam n em C), ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.MM), IsOpenImmersion x → x ≫ F.s = spMap (algebraMap o R) → ∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y := by
  intro hL hL2 n g N' J Mat κ w w' o _ b em C d F hA hG R _ _ x hx hxs K _ _ φ hmin hsurj
  have hη : (spMap φ.toRingHom ≫ x) ≫ F.s = spMap (algebraMap o K) := by
    rw [Category.assoc, hxs, spMap_comp]
    congr 1
    exact φ.comp_algebraMap
  obtain ⟨v, hv, hvI⟩ := F.loc K (algebraMap o K) _ hη
  let e : MvPolynomial (Ix g (N' ^ 2)) o →+* K := MvPolynomial.eval₂Hom (algebraMap o K) v
  have hN : N' ≠ 0 := by
    rintro rfl
    have := b.unit.map (algebraMap o K)
    simp at this
  obtain ⟨c₁, hc₁⟩ := hvI.2 ⊥ Ideal.isPrime_bot 0
  set a₁ := 0 + (N' / n) • c₁ with ha₁
  have hva₁ : v a₁ ≠ 0 := hc₁
  obtain ⟨P, a₀, a, hP, hIP, hPp, -, hind⟩ := GlobalTheory.ThetaPrime.exists_prime_independent_ratios hL hL2 g N' J Mat κ w w' o b em C d hA hG
    (RingHom.ker e) a₁ hN (RingHom.ker_isPrime e) (fun G hG => hvI.1 G hG)
    (by simpa [e, RingHom.mem_ker] using hva₁)
  obtain ⟨R', _, _, ρ, ψ, hρ, hψρ, hψ⟩ := exists_local_domain e P hPp
  let β' : o →+* R' := ρ.comp MvPolynomial.C
  let v' : Ix g (N' ^ 2) → R' := fun i => ρ (MvPolynomial.X i)
  have hev : MvPolynomial.eval₂Hom β' v' = ρ := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp [β', v']
  have hψv : (fun i => ψ (v' i)) = v := by
    funext i
    have := RingHom.congr_fun hψρ (MvPolynomial.X i)
    simpa [e] using this
  have hψβ : ψ.comp β' = algebraMap o K := by
    ext i
    have := RingHom.congr_fun hψρ (MvPolynomial.C i)
    simpa [e, β'] using this
  have hI' : InMM n N' (thIdeal em C) β' v' := by
    refine ⟨fun G hG => ?_, fun q hq i => ?_⟩
    · have : ρ G = 0 := by rw [← RingHom.mem_ker, hρ]; exact hIP hG
      rw [← hev] at this
      exact this
    · obtain ⟨c, hc⟩ := hvI.2 ⊥ Ideal.isPrime_bot i
      refine ⟨c, fun hm => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hψ _ ?_))⟩
      rw [congrFun hψv]
      exact hc
  obtain ⟨x', ⟨hx's, hx'v⟩, -⟩ := F.pts R' β' v' hI'
  have hcl : spMap ψ ≫ x' = spMap φ.toRingHom ≫ x := by
    refine (F.pts K (algebraMap o K) v hvI).unique ⟨?_, ?_⟩ ⟨hη, hv⟩
    · rw [Category.assoc, hx's, spMap_comp, hψβ]
    · have := GlobalTheory.hasTh_baseChange hL2 o g N' J b _ _ F.univ R' K ψ x' v' hx'v
      rwa [hψv] at this
  obtain ⟨χ, hχx, hψχ⟩ := exists_factor x x' φ.toRingHom ψ hψ hcl
  let K' := FractionRing R'
  let lam : R' →+* K' := algebraMap R' K'
  have hlam : Function.Injective lam := IsFractionRing.injective R' K'
  have hker : RingHom.ker (lam.comp χ) = RingHom.ker φ.toRingHom := by
    have hle : RingHom.ker (lam.comp χ) ≤ RingHom.ker φ.toRingHom := by
      intro r hr
      rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hlam] at hr
      rw [RingHom.mem_ker, ← hψχ, RingHom.comp_apply, hr, map_zero]
    exact le_antisymm hle (hmin.2 ⟨RingHom.ker_isPrime _, bot_le⟩ hle)
  obtain ⟨j, hj⟩ := exists_hom_of_ker_eq φ.toRingHom (lam.comp χ) hker hsurj
  have hpt : spMap j ≫ spMap φ.toRingHom ≫ x = spMap lam ≫ x' := by
    rw [← Category.assoc, spMap_comp, hj, ← spMap_comp, Category.assoc, hχx]
  have h1 := GlobalTheory.hasTh_baseChange hL2 o g N' J b _ _ F.univ K K' j _ v hv
  have h2 := GlobalTheory.hasTh_baseChange hL2 o g N' J b _ _ F.univ R' K' lam _ v' hx'v
  rw [hpt] at h1
  obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ F.univ K' _ _ _ h1 h2
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a₁, rfl⟩)
      (isUnit_iff_ne_zero.2 ((map_ne_zero j).2 hva₁)))
  have hjβ : j.comp (algebraMap o K) = lam.comp β' := by
    apply spMap_inj
    rw [← spMap_comp, ← hη, ← Category.assoc, hpt, Category.assoc, hx's, spMap_comp]
  have hkP : RingHom.ker (MvPolynomial.eval₂Hom (lam.comp β') (fun i => lam (v' i))) = P := by
    rw [← MvPolynomial.comp_eval₂Hom, hev, ← hρ]
    ext G
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hlam, RingHom.mem_ker]
  refine ⟨fun i => v (a i) / v a₀, algebraicIndependent_iff.2 fun G hG => hind K' _ _ hkP G ?_⟩
  have h3 := congrArg j hG
  rw [MvPolynomial.aeval_def, MvPolynomial.hom_eval₂, hjβ, map_zero] at h3
  rw [← h3]
  congr 1
  funext i
  rw [hu, hu, mul_div_mul_left _ _ u.ne_zero, map_div₀]

end GlobalTheory.ZM.GenericTrdeg
