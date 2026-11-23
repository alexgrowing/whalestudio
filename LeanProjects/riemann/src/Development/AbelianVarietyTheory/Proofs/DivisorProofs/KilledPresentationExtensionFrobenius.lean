import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt

namespace GlobalTheory.FrobFilt.Exact

open TensorProduct

private theorem lTensor_injective_of_flat_quot {R Q S M N : Type} [CommRing R] [CommRing Q] [Algebra R Q]
    (hQ : Function.Surjective (algebraMap R Q))
    [AddCommGroup S] [Module R S] [Module Q S] [IsScalarTower R Q S]
    [AddCommGroup M] [Module R M] [Module Q M] [IsScalarTower R Q M]
    [AddCommGroup N] [Module R N] [Module Q N] [IsScalarTower R Q N] [Module.Flat Q S]
    (f : M →ₗ[R] N) (hf : Function.Injective f) : Function.Injective (f.lTensor S) := by
  let f' : M →ₗ[Q] N := f.extendScalarsOfSurjective hQ
  haveI : CompatibleSMul R Q S M := CompatibleSMul.of_algebraMap_surjective S M hQ
  haveI : CompatibleSMul R Q S N := CompatibleSMul.of_algebraMap_surjective S N hQ
  have h : ∀ x, (equivOfCompatibleSMul R Q R S N).symm (f.lTensor S x) =
      f'.lTensor S ((equivOfCompatibleSMul R Q R S M).symm x) := by
    intro x
    induction x with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | tmul s m => rfl
  intro x y hxy
  apply (equivOfCompatibleSMul R Q R S M).symm.injective
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := S) f' hf
  rw [← h, ← h, hxy]

private theorem lTensor_injective_val {R S M N : Type} [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [Algebra R S] (p : ℕ) (g : R) (u : R) (hu : IsUnit u) (hp0 : (p : R) ≠ 0) (hg : g ^ p = u * p)
    (π : R →+* S) (hπ : Function.Surjective π) (hker : ∀ r, π r = 0 ↔ (p : R) ∣ r)
    (hφ : ∀ r, algebraMap R S r = π r ^ p)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hM : ∀ m : M, g • m = 0) (hN : ∀ m : N, g • m = 0)
    (f : M →ₗ[R] N) (hf : Function.Injective f) : Function.Injective (f.lTensor S) := by
  have hgS : algebraMap R S g = 0 := by
    rw [hφ, ← map_pow, hker, hg]; exact dvd_mul_left _ _
  have hS : ∀ s : S, g • s = 0 := fun s => by rw [Algebra.smul_def, hgS, zero_mul]
  have tM : Module.IsTorsionBy R M g := fun m => hM m
  have tN : Module.IsTorsionBy R N g := fun m => hN m
  have tS : Module.IsTorsionBy R S g := fun m => hS m
  letI := tM.module
  letI := tN.module
  letI := tS.module
  have key : ∀ a b : R, a * b = g → ∀ s : S, a • s = 0 → ∃ t : S, s = b • t := by
    intro a b hab s hs
    obtain ⟨r, rfl⟩ := hπ s
    rw [Algebra.smul_def, hφ, ← map_pow, ← map_mul, hker] at hs
    have ha : a ^ p ≠ 0 := fun h => by
      apply hp0
      have : u * p = 0 := by rw [← hg, ← hab, mul_pow, h, zero_mul]
      exact (hu.mul_right_eq_zero).1 this
    have h1 : a ^ p * b ^ p ∣ a ^ p * r := by
      rw [← mul_pow, hab, hg]; exact (hu.mul_left_dvd).2 hs
    obtain ⟨c, rfl⟩ := (mul_dvd_mul_iff_left ha).1 h1
    exact ⟨π c, by rw [Algebra.smul_def, hφ, map_mul, map_pow]⟩
  haveI : Module.Flat (R ⧸ Ideal.span {g}) S := by
    rw [Module.Flat.iff_rTensor_injective]
    intro I hI
    obtain ⟨J, hJ⟩ : ∃ a : R, a ∣ g ∧ I = Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a} := by
      have hfg : (I.comap (Ideal.Quotient.mk (Ideal.span {g}))).FG := by
        refine Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective (f := Ideal.Quotient.mk (Ideal.span {g})) ?_ ?_ Ideal.Quotient.mk_surjective
        · rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
        · rw [inf_eq_right.2 (Ideal.ker_le_comap _), Ideal.mk_ker]
          exact ⟨{g}, by simp⟩
      obtain ⟨a, ha⟩ := (IsBezout.isPrincipal_of_FG _ hfg).principal
      refine ⟨a, ?_, ?_⟩
      · rw [← Ideal.mem_span_singleton]
        change g ∈ Submodule.span R {a}
        rw [← ha]
        change Ideal.Quotient.mk _ g ∈ I
        rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self g)]
        exact I.zero_mem
      · rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective I, ha]
        change Ideal.map _ (Ideal.span {a}) = _
        rw [Ideal.map_span, Set.image_singleton]
    obtain ⟨⟨b, hb⟩, rfl⟩ := hJ
    set a' := Ideal.Quotient.mk (Ideal.span {g}) J with ha'
    let e : Ideal.span {a'} := ⟨a', Ideal.mem_span_singleton_self _⟩
    have hsurj : ∀ x : Ideal.span {a'} ⊗[R ⧸ Ideal.span {g}] S, ∃ s : S, x = e ⊗ₜ s := by
      intro x
      induction x with
      | zero => exact ⟨0, by simp⟩
      | add x y hx hy =>
        obtain ⟨s, rfl⟩ := hx
        obtain ⟨t, rfl⟩ := hy
        exact ⟨s + t, by rw [tmul_add]⟩
      | tmul i s =>
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 i.2
        refine ⟨c • s, ?_⟩
        rw [← smul_tmul]
        congr 1
        exact Subtype.ext hc.symm
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨s, rfl⟩ := hsurj x
    have h1 : J • s = 0 := by
      have := congrArg (TensorProduct.lid _ S) hx
      have h0 : a' • s = 0 := by simpa using this
      exact h0
    obtain ⟨t, rfl⟩ := key J b hb.symm s h1
    have h2 : b • t = Ideal.Quotient.mk (Ideal.span {g}) b • t := rfl
    rw [h2, ← smul_tmul]
    have h3 : Ideal.Quotient.mk (Ideal.span {g}) b • e = 0 := by
      apply Subtype.ext
      change Ideal.Quotient.mk (Ideal.span {g}) b * a' = 0
      rw [ha', ← map_mul, mul_comm, ← hb]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self g)
    rw [h3, zero_tmul]
  exact lTensor_injective_of_flat_quot (Q := R ⧸ Ideal.span {g}) Ideal.Quotient.mk_surjective f hf

private theorem exists_smul_eq_zero {A C R M N M' N' : Type} [CommRing A] [CommRing C] [Algebra A C]
    (P : Ideal A) [P.IsPrime] [CommRing R] [Algebra A R] [IsLocalization.AtPrime R P]
    [IsDomain R] [ValuationRing R] (p : ℕ) (g u : A) (hu : IsUnit u) (hp0 : (p : R) ≠ 0)
    (hg : g ^ p = u * p)
    (π : A →+* C) (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {(p : A)})
    (hφ : ∀ r, algebraMap A C r = π r ^ p)
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (hM : ∀ m : M, g • m = 0) (hN : ∀ m : N, g • m = 0)
    [AddCommGroup M'] [Module A M'] [Module C M'] [IsScalarTower A C M']
    [AddCommGroup N'] [Module A N'] [Module C N'] [IsScalarTower A C N']
    {l : M →ₗ[A] M'} {l' : N →ₗ[A] N'} (hl : IsBaseChange C l) (hl' : IsBaseChange C l')
    (f : M →ₗ[A] N) (hf : Function.Injective f) (b : M' →ₗ[C] N') (hab : ∀ m, b (l m) = l' (f m))
    (s : M') (hs : b s = 0) : ∃ t : A, t ∉ P ∧ π t • s = 0 := by
  let T : Submonoid C := P.primeCompl.map π
  let S := Localization T
  let πR : R →+* S := IsLocalization.map S π (P.primeCompl.le_comap_map)
  have hπR : ∀ a, πR (algebraMap A R a) = algebraMap C S (π a) := fun a => IsLocalization.map_eq _ _
  have hunit : ∀ t : P.primeCompl, IsUnit (algebraMap C S (π t)) := fun t =>
    IsLocalization.map_units S (⟨π t, t, t.2, rfl⟩ : T)
  have hunit' : ∀ t : P.primeCompl, IsUnit (algebraMap A S t) := fun t => by
    rw [IsScalarTower.algebraMap_apply A C S, hφ, map_pow]; exact (hunit t).pow _
  letI : Algebra R S := (IsLocalization.lift (M := P.primeCompl) (S := R) hunit').toAlgebra
  haveI : IsScalarTower A R S := .of_algebraMap_eq fun a => (IsLocalization.lift_eq hunit' a).symm
  have hφR : ∀ r, algebraMap R S r = πR r ^ p := by
    intro r
    obtain ⟨⟨a, t⟩, h⟩ := IsLocalization.surj P.primeCompl r
    dsimp only at h
    refine (hunit' t).mul_right_cancel ?_
    have h1 := congrArg (algebraMap R S) h
    have h2 := congrArg (fun x => πR x ^ p) h
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
    simp only [map_mul, mul_pow, hπR] at h2
    rw [h1, IsScalarTower.algebraMap_apply A C S, IsScalarTower.algebraMap_apply A C S, hφ, hφ,
      map_pow, map_pow, h2]
  have hsurj : Function.Surjective πR :=
    IsLocalization.map_surjective_of_surjective P.primeCompl R S hπ
  have hkerR : ∀ r, πR r = 0 ↔ (p : R) ∣ r := by
    intro r
    rw [← RingHom.mem_ker, IsLocalization.ker_map (S := R) S π (M := P.primeCompl) (T := T) rfl, hker, Ideal.map_span,
      Set.image_singleton, map_natCast, Ideal.mem_span_singleton]
  haveI : Module.Flat A R := IsLocalization.flat R P.primeCompl
  have kill : ∀ (K : Type) [AddCommGroup K] [Module A K], (∀ m : K, g • m = 0) →
      ∀ x : R ⊗[A] K, algebraMap A R g • x = 0 := by
    intro K _ _ hK x
    rw [algebraMap_smul]
    induction x with
    | zero => simp
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
    | tmul r m => rw [← tmul_smul, hK, tmul_zero]
  have inj := lTensor_injective_val p (algebraMap A R g) (algebraMap A R u) (hu.map _) hp0
    (by rw [← map_pow, hg, map_mul, map_natCast]) πR hsurj hkerR hφR (kill M hM) (kill N hN)
    (f.baseChange R) (Module.Flat.lTensor_preserves_injective_linearMap f hf)
  have inj2 : Function.Injective (f.lTensor S) := by
    have h : ∀ x, AlgebraTensorModule.cancelBaseChange A R R S N ((f.baseChange R).lTensor S x) =
        f.lTensor S (AlgebraTensorModule.cancelBaseChange A R R S M x) := by
      intro x
      induction x with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul s m =>
        induction m with
        | zero => simp
        | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
        | tmul r m => simp
    intro x y hxy
    obtain ⟨x, rfl⟩ := (AlgebraTensorModule.cancelBaseChange A R R S M).surjective x
    obtain ⟨y, rfl⟩ := (AlgebraTensorModule.cancelBaseChange A R R S M).surjective y
    rw [← h, ← h] at hxy
    rw [inj ((AlgebraTensorModule.cancelBaseChange A R R S N).injective hxy)]
  obtain ⟨x, rfl⟩ := hl.equiv.surjective s
  have h1 : f.lTensor C x = 0 := by
    apply hl'.equiv.injective
    rw [map_zero, ← hs]
    clear hs
    induction x with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m => simp [hab]
  have h2 : ∀ y : C ⊗[A] M, f.lTensor S ((Algebra.linearMap C S).restrictScalars A |>.rTensor M y) =
      ((Algebra.linearMap C S).restrictScalars A).rTensor N (f.lTensor C y) := by
    intro y
    induction y with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m => simp
  have h3 : ((Algebra.linearMap C S).restrictScalars A).rTensor M x = 0 := by
    apply inj2
    rw [h2, h1, map_zero, map_zero]
  have h4 : (1 : S) ⊗ₜ[C] x = 0 := by
    apply (AlgebraTensorModule.cancelBaseChange A C C S M).injective
    rw [map_zero, ← h3]
    clear h1 h3 hs
    induction x with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
    | tmul c m => simp [Algebra.algebraMap_eq_smul_one]
  haveI : IsLocalizedModule T (TensorProduct.mk C S (C ⊗[A] M) 1) :=
    IsLocalization.tensorProduct_isLocalizedModule T S
  obtain ⟨⟨_, t, ht, rfl⟩, h5⟩ := (IsLocalizedModule.eq_zero_iff T (TensorProduct.mk C S (C ⊗[A] M) 1)).1 h4
  refine ⟨t, ht, ?_⟩
  rw [← map_smul]
  exact (congrArg hl.equiv h5).trans (map_zero _)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem valuationRing_stalk (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]
    (B : GlobalTheory.Vert.Model O) [GlobalTheory.IsNormalScheme B.X] (x : B.X) (hx : IsGenSpecial B x) :
    ValuationRing (B.X.presheaf.stalk x) ∧ (p : B.X.presheaf.stalk x) ≠ 0 := by
  have hp0 : (p : O) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpm : (p : O) ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  have hgen : B.gen = B.X.basicOpen (p : Γ(B.X, ⊤)) := by
    rw [B.gen_eq_basicOpen hp0 hpm, Vert.Model.const, map_natCast]
  have hpT : (p : Γ(B.X, ⊤)) ≠ 0 := by
    intro h
    have := B.genericPoint_mem_gen
    rw [hgen, h, Scheme.basicOpen_zero] at this
    exact this
  have hpx : (p : B.X.presheaf.stalk x) ≠ 0 := by
    intro h
    apply hpT
    apply germ_injective_of_isIntegral B.X x (U := ⊤) trivial
    rw [map_natCast, map_zero, h]
  refine ⟨?_, hpx⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    B.X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  haveI : IsNoetherianRing Γ(B.X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hbo : ∀ y : U, (p : Γ(B.X, U)) ∈ (hU.primeIdealOf y).asIdeal ↔ y.1 ∉ B.gen := by
    intro y
    have h1 := GlobalTheory.QCoh.mem_primeCompl_primeIdealOf_iff hU y (p : Γ(B.X, U))
    have h2 : B.X.basicOpen (p : Γ(B.X, U)) = U ⊓ B.X.basicOpen (p : Γ(B.X, ⊤)) := by
      rw [← B.X.basicOpen_res (p : Γ(B.X, ⊤)) (homOfLE (le_top : U ≤ ⊤)).op, map_natCast]
    rw [h2, ← hgen] at h1
    refine ⟨fun h h' => h1.2 ⟨y.2, h'⟩ h, fun h => by_contra fun h' => h (h1.1 h').2⟩
  have hmin : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∈ (Ideal.span {(p : Γ(B.X, U))}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).2 ((hbo _).2 hx.1)⟩, ?_⟩
    rintro Q ⟨hQ, hpQ⟩ hle
    let y : U := ⟨hU.fromSpec ⟨Q, hQ⟩, hU.range_fromSpec.le ⟨_, rfl⟩⟩
    have hy : hU.primeIdealOf y = ⟨Q, hQ⟩ :=
      hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
    have hyx : y.1 ⤳ x := by
      have : (⟨Q, hQ⟩ : PrimeSpectrum Γ(B.X, U)) ⤳ hU.primeIdealOf ⟨x, hxU⟩ :=
        (PrimeSpectrum.le_iff_specializes _ _).1 hle
      have := this.map hU.fromSpec.continuous
      rwa [hU.fromSpec_primeIdealOf] at this
    have h3 : y = ⟨x, hxU⟩ := Subtype.ext (hx.2 y ((hbo y).1 (by
      rw [hy]; exact (Ideal.span_singleton_le_iff_mem _).1 hpQ)) hyx)
    rw [← h3, hy]
  have hht := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  letI := TopCat.Presheaf.algebra_section_stalk B.X.presheaf (⟨x, hxU⟩ : U)
  haveI := hU.isLocalization_stalk ⟨x, hxU⟩
  have hdim := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
    (B.X.presheaf.stalk x)
  have h1 : Ring.KrullDimLE 1 (B.X.presheaf.stalk x) := by
    rw [Ring.krullDimLE_iff, hdim]
    exact_mod_cast hht
  haveI : Ring.DimensionLEOne (B.X.presheaf.stalk x) :=
    ⟨fun h0 hP => (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 h1 _ h0 hP)⟩
  haveI : IsDedekindDomain (B.X.presheaf.stalk x) := {}
  infer_instance

private theorem injective_app (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]
    (B : GlobalTheory.Vert.Model O) [GlobalTheory.IsNormalScheme B.X] (g : Γ(B.X, ⊤)) (hg : IsRootOfP p g p)
    {F G : B.X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) [Mono φ]
    (hF : Kills g F) (hG : Kills g G) (hE : NoEmb B ((frob p B).obj F)) (U : B.X.Opens)
    (hU : IsAffineOpen U) : Function.Injective (((frob p B).map φ).app U) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  let I := fibI p B
  let f := GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out (FrobQuot.natCast_eq_zero_fibI p B) ≫ I.subschemeι
  have hW : IsAffineOpen (I.subschemeι ⁻¹ᵁ U) := hU.preimage _
  have e : I.subschemeι ⁻¹ᵁ U ≤ f ⁻¹ᵁ U := le_rfl
  obtain ⟨u, hu⟩ := hg
  have loc : ∀ x ∈ U, IsGenSpecial B x → ∃ t : Γ(B.X, U), x ∈ B.X.basicOpen t ∧ t • s = 0 := by
    intro x hxU hx
    obtain ⟨hv, hp0⟩ := valuationRing_stalk p B x hx
    letI := TopCat.Presheaf.algebra_section_stalk B.X.presheaf (⟨x, hxU⟩ : U)
    haveI := hU.isLocalization_stalk ⟨x, hxU⟩
    letI := QCoh.appLEAlgebra f e
    letI := QCoh.appLEModule f ((Scheme.Modules.pullback f).obj F) e
    haveI := QCoh.appLE_isScalarTower f ((Scheme.Modules.pullback f).obj F) e
    letI := QCoh.appLEModule f ((Scheme.Modules.pullback f).obj G) e
    haveI := QCoh.appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
    have hk : ∀ K : B.X.Modules, Kills g K → ∀ m : Γ(K, U), restrictGlobal B.X U g • m = 0 := by
      intro K hK m
      have := congrArg (fun φ => φ.app U m) hK
      exact this
    obtain ⟨t, ht, hts⟩ := exists_smul_eq_zero (R := B.X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal p (restrictGlobal B.X U g) (restrictGlobal B.X U u)
      (u.isUnit.map _) hp0 (by rw [← map_pow, hu, map_mul, map_natCast])
      (I.subschemeι.app U).hom (I.subschemeι.app_surjective U hU)
      (by
        rw [I.ker_subschemeι_app ⟨U, hU⟩]
        simp only [I, fibI, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span,
          Set.image_singleton, map_natCast])
      (fun r => by
        have h1 := GlobalTheory.SS.FrobField.absFrob_appLE _ p 1 Fact.out (FrobQuot.natCast_eq_zero_fibI p B)
          (I.subschemeι ⁻¹ᵁ U) le_rfl ((I.subschemeι.app U).hom r)
        rw [pow_one] at h1
        rw [← h1]
        change (f.appLE U _ e).hom r = _
        rw [Scheme.Hom.app_eq_appLE]
        exact (congrArg (fun ψ => ψ.hom r) (Scheme.Hom.appLE_comp_appLE
          (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out (FrobQuot.natCast_eq_zero_fibI p B))
          (fibI p B).subschemeι U (I.subschemeι ⁻¹ᵁ U) (I.subschemeι ⁻¹ᵁ U) le_rfl le_rfl)).symm)
      (hk F hF) (hk G hG) (QCoh.isBaseChange_pullbackSections f F hW hU e)
      (QCoh.isBaseChange_pullbackSections f G hW hU e) (QCoh.homAppLinear φ U)
      (QCoh.app_injective_of_mono φ U) (QCoh.homAppLinear ((Scheme.Modules.pullback f).map φ) _)
      (QCoh.pullback_map_app_pullbackSections f φ e) s hs
    exact ⟨t, (GlobalTheory.QCoh.mem_primeCompl_primeIdealOf_iff hU ⟨x, hxU⟩ t).1 ht, hts⟩
  let ι := {t : Γ(B.X, U) // t • s = 0}
  have hle : (⨆ t : ι, B.X.basicOpen t.1) ≤ U := iSup_le fun t => B.X.basicOpen_le _
  refine hE U _ hle (fun x hxU hx => ?_) ?_
  · obtain ⟨t, ht, hts⟩ := loc x hxU hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨t, hts⟩, ht⟩
  · refine QCoh.section_eq_of_cover _ (fun t : ι => B.X.basicOpen t.1)
      (fun t => le_iSup (fun t : ι => B.X.basicOpen t.1) t) le_rfl _ _ fun t => ?_
    rw [QCoh.res_res, QCoh.res_res, map_zero]
    have h1 := (QCoh.resLinear ((frob p B).obj F) (B.X.basicOpen_le t.1)).map_smul t.1 s
    rw [t.2, map_zero] at h1
    exact ((QCoh.isUnit_res_of_le_basicOpen t.1 (B.X.basicOpen_le t.1) le_rfl).smul_eq_zero).1 h1.symm

end GlobalTheory.FrobFilt.Exact

theorem _root_.GlobalTheory.T.killed_presentation_extension_frobenius : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (g : Γ(B.X, ⊤)), IsRootOfP p g p → ∀ S : ShortComplex B.X.Modules, S.ShortExact → (∃ P : Pres B, Nonempty (S.X₁ ≅ P.mod)) → (∃ P : Pres B, Nonempty (S.X₂ ≅ P.mod)) → (∃ P : Pres B, Nonempty (S.X₃ ≅ P.mod)) → Kills g S.X₁ → Kills g S.X₂ → Kills g S.X₃ → NoEmb B ((frob p B).obj S.X₁) → (S.map (frob p B)).ShortExact := by
  intro O _ _ _ p _ _ _ B hN g hg S hS h₁ h₂ h₃ k₁ k₂ k₃ hE
  have qc : ∀ F : B.X.Modules, (∃ P : Pres B, Nonempty (F ≅ P.mod)) → F.IsQuasicoherent := by
    rintro F ⟨P, ⟨e⟩⟩
    haveI : P.E.IsQuasicoherent := P.vb.isQuasicoherent
    haveI : P.E'.IsQuasicoherent := P.vb'.isQuasicoherent
    haveI : P.mod.IsQuasicoherent := by unfold Pres.mod; infer_instance
    exact GlobalTheory.QCoh.isQuasicoherent_of_iso e.symm
  haveI := hS.epi_g
  haveI := hS.mono_f
  haveI := qc _ h₁
  haveI := qc _ h₂
  haveI := qc _ h₃
  let I := fibI p B
  let f := GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out (FrobQuot.natCast_eq_zero_fibI p B) ≫ I.subschemeι
  have hmono : Mono ((Scheme.Modules.pullback f).map S.f) := by
    refine QCoh.mono_of_locally_app_injective _ fun W z hz => ?_
    obtain ⟨W', hW', hWW⟩ := I.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.1 W.2
    have hz' : I.subschemeι z ∈ W' := by
      change z ∈ I.subschemeι ⁻¹' W'
      rw [hWW]; exact hz
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, hle⟩ := B.X.isBasis_affineOpens.exists_subset_of_mem_open hz' hW'
    refine ⟨I.subschemeι ⁻¹ᵁ U, hzU, fun y hy => ?_,
      GlobalTheory.FrobFilt.Exact.injective_app p B g hg S.f k₁ k₂ hE U hU⟩
    change y ∈ W.carrier
    rw [← hWW]
    exact hle hy
  obtain ⟨hx, hepi⟩ := QCoh.exact_map_pullback f hS.exact
  have hP : (S.map (Scheme.Modules.pullback f)).ShortExact := ShortComplex.ShortExact.mk' hx hmono hepi
  haveI : (S.map (Scheme.Modules.pullback f)).X₂.IsQuasicoherent := QCoh.isQuasicoherent_pullback f S.X₂
  haveI : (S.map (Scheme.Modules.pullback f)).X₃.IsQuasicoherent := QCoh.isQuasicoherent_pullback f S.X₃
  exact QCoh.shortExact_map_pushforward I.subschemeι hP
