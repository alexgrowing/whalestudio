import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ResidueGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealPrimeAvoidingVariableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GenericDim

open GlobalTheory.CoordChart

theorem exists_secCoord_field {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {σ : Type} (th : σ → M.Sec)
    {K : Type} [Field K] (x : Sp K ⟶ X) : ∃ v, SecCoord M th x v := by
  let p₀ : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have h : x p₀ ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine GlobalTheory.SegreCoord.exists_secCoord hM (k := k) fun y => ?_
  have : y = p₀ := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [this]; exact hk

theorem exists_common_field {R L : Type} [CommRing R] [CommRing L] [IsDomain L] (q : Ideal R) [q.IsPrime]
    (φ : R →+* L) (h : RingHom.ker φ = q) :
    ∃ (K : Type) (_ : Field K) (lam : L →+* K) (j : FractionRing (R ⧸ q) →+* K), Function.Injective lam ∧
      j.comp ((algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q)) = lam.comp φ := by
  have hl := IsFractionRing.injective L (FractionRing L)
  have hχ : Function.Injective ((algebraMap L (FractionRing L)).comp (Ideal.Quotient.lift q φ fun a ha => h.ge ha)) :=
    hl.comp ((Ideal.injective_lift_iff fun a ha => h.ge ha).2 h)
  refine ⟨FractionRing L, inferInstance, algebraMap L (FractionRing L),
    IsFractionRing.lift (A := R ⧸ q) (K := FractionRing (R ⧸ q)) hχ, hl, ?_⟩
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, IsFractionRing.lift_algebraMap hχ, RingHom.comp_apply,
    RingHom.comp_apply]
  exact congrArg _ (Ideal.Quotient.lift_mk q φ _)

theorem exists_extension {o : Type} [CommRing o] {g n N' : ℕ} {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)}
    (Y : MMPre n N' I) {R : Type} [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) [IsOpenImmersion x]
    (hx : x ≫ Y.s = spMap β) (q : Ideal R) [q.IsPrime] (hmin : q ∈ minimalPrimes R)
    (y : R →+* FractionRing (R ⧸ q)) (hy : y = (algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q))
    (v : Ix g (N' ^ 2) → FractionRing (R ⧸ q)) (hv : SecCoord Y.de Y.th (spMap y ≫ x) v)
    (P : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (hP : P.IsPrime) (hI : I ≤ P)
    (hle : P ≤ RingHom.ker (MvPolynomial.eval₂Hom (y.comp β) v)) :
    ∃ (K : Type) (_ : Field K) (j : FractionRing (R ⧸ q) →+* K) (u : Kˣ),
      RingHom.ker (MvPolynomial.eval₂Hom (j.comp (y.comp β)) (fun a => u * j (v a))) = P := by
  have h3 : (spMap y ≫ x) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hx, sp_comp]
  have hK := Y.loc _ _ _ _ h3 hv
  set ev := MvPolynomial.eval₂Hom (y.comp β) v with hev
  let e : (MvPolynomial (Ix g (N' ^ 2)) o ⧸ P) →+* FractionRing (R ⧸ q) :=
    Ideal.Quotient.lift P ev fun a ha => hle ha
  haveI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  let L := Localization.AtPrime (RingHom.ker e)
  have hu : ∀ s : (RingHom.ker e).primeCompl, IsUnit (e s) := fun s => IsUnit.mk0 _ s.2
  let ψ : L →+* FractionRing (R ⧸ q) := IsLocalization.lift (M := (RingHom.ker e).primeCompl) hu
  let π : MvPolynomial (Ix g (N' ^ 2)) o →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk P)
  have hπ : ∀ F, ψ (π F) = ev F := fun F => by
    simp only [ψ, π, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  have hπe : ∀ F, MvPolynomial.eval₂ (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) F = π F := fun F => by
    conv_rhs => rw [← MvPolynomial.eval₂_eta F, MvPolynomial.eval₂_comp_left]
    rfl
  have hπ0 : ∀ F, π F = 0 ↔ F ∈ P := fun F => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsLocalization.injective L (RingHom.ker e).primeCompl_le_nonZeroDivisors)
  have hψ : ∀ l, ψ l ≠ 0 → IsUnit l := by
    intro l hl
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker e).primeCompl l
    rw [IsLocalization.AtPrime.isUnit_mk'_iff L (RingHom.ker e)]
    intro ha
    apply hl
    change ψ (IsLocalization.mk' L a s) = 0
    rw [IsLocalization.lift_mk'_spec, mul_zero]
    exact ha
  have hw : ∀ a, ψ (π (MvPolynomial.X a)) = v a := fun a => by rw [hπ]; simp [hev]
  have hβ : ψ.comp (π.comp MvPolynomial.C) = y.comp β := by ext t; simp [hπ, hev]
  have hL : InMM n N' I (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) := by
    refine ⟨fun F hF => by rw [hπe, hπ0]; exact hI hF, fun r hr a => ?_⟩
    obtain ⟨c, hc⟩ := hK.2 ⊥ Ideal.isPrime_bot a
    refine ⟨c, fun hm => hr.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hψ _ ?_))⟩
    rw [hw]
    simpa using hc
  obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := Y.pts L _ _ hL
  have h4 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 _ ψ
  have h5 : (spMap ψ ≫ z) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hz1, sp_comp, hβ]
  have heq : spMap ψ ≫ z = spMap y ≫ x := by
    refine (Y.pts _ _ _ hK).unique ⟨h5, ?_⟩ ⟨h3, hv⟩
    simpa only [hw] using h4
  have hr : Set.range z ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    let p₀ : Sp (FractionRing (R ⧸ q)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing (R ⧸ q)))
    have hs : p ⤳ spMap ψ p₀ := by
      refine (PrimeSpectrum.le_iff_specializes (R := L) p (spMap ψ p₀)).1 ?_
      intro l hl
      change ψ l ∈ (⊥ : Ideal _)
      by_contra hne
      exact p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hl (hψ _ (by simpa using hne)))
    refine (hs.map z.continuous).mem_open x.isOpenEmbedding.isOpen_range ⟨spMap y p₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, heq]
  obtain ⟨φ, hφ⟩ := sp_surj (IsOpenImmersion.lift x z hr)
  have hz : spMap φ ≫ x = z := by rw [hφ, IsOpenImmersion.lift_fac]
  have hφy : ψ.comp φ = y := sp_inj (by rw [← cancel_mono x, ← sp_comp, Category.assoc, hz, heq])
  have hφβ : φ.comp β = π.comp MvPolynomial.C := sp_inj (by rw [← sp_comp, ← hx, ← Category.assoc, hz, hz1])
  have hy0 : ∀ r, y r = 0 ↔ r ∈ q := fun r => by
    rw [hy, RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ q) _),
      Ideal.Quotient.eq_zero_iff_mem]
  have hk1 : RingHom.ker φ ≤ q := fun r hr => by
    rw [RingHom.mem_ker] at hr
    rw [← hy0, ← hφy, RingHom.comp_apply, hr, map_zero]
  have hk2 : q ≤ RingHom.ker φ := hmin.2 ⟨RingHom.ker_isPrime φ, bot_le⟩ hk1
  haveI : IsDomain L := IsLocalization.isDomain_localization (RingHom.ker e).primeCompl_le_nonZeroDivisors
  obtain ⟨K, _, lam, j, hl, hj⟩ := exists_common_field q φ (le_antisymm hk1 hk2)
  rw [← hy] at hj
  have h6 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 _ j
  have h7 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 _ lam
  rw [← Category.assoc, sp_comp, hj, ← sp_comp, Category.assoc, hz] at h6
  obtain ⟨u, hu'⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h6).2.2 _ h7
  refine ⟨K, inferInstance, j, u, ?_⟩
  ext F
  rw [RingHom.mem_ker, ← hπ0, ← map_eq_zero_iff lam hl, ← hπe, MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hj,
    RingHom.comp_assoc, hφβ, MvPolynomial.coe_eval₂Hom, ← funext hu']
  rfl

theorem le_ringKrullDim_of_independent {o : Type} [CommRing o] [IsDomain o] {R : Type} [CommRing R] [Algebra o R]
    [Algebra.FiniteType o R] {d : ℕ}
    (h : ∀ (q : Ideal R) [q.IsPrime], q ∈ minimalPrimes R → ∃ y : Fin d → FractionRing (R ⧸ q), AlgebraicIndependent o y)
    (q : Ideal (FractionRing o ⊗[o] R)) (hq : q ∈ minimalPrimes (FractionRing o ⊗[o] R)) :
    (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q) := by
  have hqp : q.IsPrime := hq.1.1
  let f : R →ₐ[o] FractionRing o ⊗[o] R := Algebra.TensorProduct.includeRight
  have hmin : q.comap f ∈ minimalPrimes R := by
    letI : Algebra R (FractionRing o ⊗[o] R) := Algebra.TensorProduct.rightAlgebra
    have h1 := IsLocalization.minimalPrimes_map (Algebra.algebraMapSubmonoid R (nonZeroDivisors o))
      (FractionRing o ⊗[o] R) ⊥
    rw [Ideal.map_bot] at h1
    have h2 : q ∈ (⊥ : Ideal (FractionRing o ⊗[o] R)).minimalPrimes := hq
    rw [h1] at h2
    exact h2
  obtain ⟨y, hy⟩ := h (q.comap f) hmin
  let B := (FractionRing o ⊗[o] R) ⧸ q
  let f' : (R ⧸ q.comap f) →ₐ[o] FractionRing B :=
    (IsScalarTower.toAlgHom o B (FractionRing B)).comp (Ideal.quotientMapₐ q f le_rfl)
  have hf' : Function.Injective f' :=
    (IsFractionRing.injective B (FractionRing B)).comp (Ideal.quotientMap_injective' (f := f.toRingHom) (H := le_rfl) le_rfl)
  let j : FractionRing (R ⧸ q.comap f) →ₐ[o] FractionRing B := IsFractionRing.liftAlgHom hf'
  have h1 : AlgebraicIndependent o (j ∘ y) := hy.map' j.toRingHom.injective
  have : Algebra.IsAlgebraic o (FractionRing o) := IsLocalization.isAlgebraic _ (nonZeroDivisors o)
  have h2 := (h1.extendScalars (FractionRing o)).cardinalMk_le_trdeg
  have : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq (FractionRing o) B
  have : FaithfulSMul (FractionRing o) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap (FractionRing o) B).injective
  rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top (FractionRing o) B (FractionRing B), hs2] at h2
  have h3 : d ≤ s := by simpa using h2
  rw [hs1]
  exact_mod_cast h3

theorem le_ringKrullDim_genericFibre : Out.Laws → Out.Laws2 → ∀ (g n N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : WFam n em C Mat κ), 3 ≤ N' → Odd N' → ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.U.toScheme), IsOpenImmersion x → x ≫ F.U.ι ≫ F.Y.s = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q) := by
  intro h1 h2 g n N' J Mat κ w w' o _ b em C d F hN _ hb hC R _ _ x hox hx
  have : IsDedekindDomain o := hb.1
  have hx' : (x ≫ F.U.ι) ≫ F.Y.s = spMap (algebraMap o R) := by rw [Category.assoc, hx]
  have : Algebra.FiniteType o R := by
    obtain ⟨N, i, hi, -, hs⟩ := F.Y.qproj
    have := isProper_str o N
    have h : LocallyOfFiniteType (spMap (algebraMap o R)) := by
      rw [← hx', ← hs]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
    exact RingHom.finiteType_algebraMap.mp h
  refine le_ringKrullDim_of_independent fun q _ hq => ?_
  let y : R →+* FractionRing (R ⧸ q) := (algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q)
  have hy : y.comp (algebraMap o R) = algebraMap o _ := by
    rw [IsScalarTower.algebraMap_eq o (R ⧸ q) (FractionRing (R ⧸ q))]; rfl
  obtain ⟨v, hv⟩ := exists_secCoord_field F.Y.isLB F.Y.th (spMap y ≫ x ≫ F.U.ι)
  have hK := F.Y.loc _ (y.comp (algebraMap o R)) _ _ (by rw [Category.assoc, hx', sp_comp]) hv
  obtain ⟨c, hc⟩ := hK.2 ⊥ Ideal.isPrime_bot 0
  obtain ⟨P, a₀, a, hP, hI, hle, -, hind⟩ := GlobalTheory.T.theta_ideal_prime_avoiding_variable h1 h2 g N' J Mat κ w w' o b em C d hb hC
    (RingHom.ker (MvPolynomial.eval₂Hom (y.comp (algebraMap o R)) v)) _ (by omega) (RingHom.ker_isPrime _)
    (fun G hG => hK.1 G hG) (by rw [RingHom.mem_ker, MvPolynomial.eval₂Hom_X']; simpa using hc)
  obtain ⟨K, _, j, u, hker⟩ := exists_extension F.Y _ (x ≫ F.U.ι) hx' q hq y rfl v hv P hP hI hle
  refine ⟨fun i => v (a i) / v a₀, algebraicIndependent_iff.2 fun G hG => hind K _ _ hker G ?_⟩
  have := congrArg j hG
  rw [map_zero, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, ← hy] at this
  convert this using 2
  ext i
  simp [mul_div_mul_left]

end GlobalTheory.ZM.GenericDim
