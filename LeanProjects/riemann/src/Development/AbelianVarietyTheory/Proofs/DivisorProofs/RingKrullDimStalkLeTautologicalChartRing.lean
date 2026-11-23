import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.GlActionMemBalFormsOfSemilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalMvPolynomialLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimQuotientLeOfMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingOfRegularQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmoothOfRelativeDimensionPowObj
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.ChartDim

theorem isAlgebraic_of_quasiFinite (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [FaithfulSMul A K]
    [Algebra.QuasiFinite A K] : Algebra.IsAlgebraic A K := by
  letI : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
  haveI : IsScalarTower A (FractionRing A) K := FractionRing.isScalarTower_liftAlgebra A K
  haveI : Algebra.QuasiFinite (FractionRing A) K := .of_restrictScalars A _ _
  haveI : Module.Finite (FractionRing A) K := Algebra.QuasiFinite.iff_of_isArtinianRing.1 inferInstance
  haveI : Algebra.IsAlgebraic A (FractionRing A) := IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  exact Algebra.IsAlgebraic.trans A (FractionRing A) K

theorem trdeg_le (k A B K : Type) [CommRing k] [IsDomain k] [CommRing A] [IsDomain A] [CommRing B] [Field K] [Algebra k A]
    [Algebra k B] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [FaithfulSMul k A] [FaithfulSMul A K]
    [Algebra.IsAlgebraic A K] (b : B →ₐ[k] K) (hb : Function.Injective b) : Algebra.trdeg k B ≤ Algebra.trdeg k A := by
  refine (trdeg_le_of_injective b hb).trans ?_
  rw [← trdeg_add_eq k A (A := K), trdeg_eq_zero (R := A) (A := K), add_zero]

theorem ringKrullDim_le_of_isAlgebraic (A B K : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K]
    [Algebra.FiniteType ℤ A] [Algebra.FiniteType ℤ B] [Algebra A K] [FaithfulSMul A K] [Algebra.IsAlgebraic A K]
    (b : B →+* K) (hb : Function.Injective b) : ringKrullDim B ≤ ringKrullDim A := by
  have ha := FaithfulSMul.algebraMap_injective A K
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : CharP A p := RingHom.charP _ ha p
  haveI : CharP B p := RingHom.charP _ hb p
  rcases CharP.char_is_prime_or_zero K p with h | rfl
  · haveI := Fact.mk h
    letI := ZMod.algebra A p
    letI := ZMod.algebra B p
    letI := ZMod.algebra K p
    haveI : IsScalarTower ℤ (ZMod p) A := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : IsScalarTower ℤ (ZMod p) B := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : IsScalarTower (ZMod p) A K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : Algebra.FiniteType (ZMod p) A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
    haveI : Algebra.FiniteType (ZMod p) B := Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
    obtain ⟨s, hs⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := ZMod p) (S := A))
    obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := ZMod p) (S := B))
    have hle := trdeg_le (ZMod p) A B K
      { b with commutes' := fun r => RingHom.congr_fun (Subsingleton.elim (b.comp (algebraMap (ZMod p) B)) _) r } hb
    rw [hs, ht] at hle
    rw [ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field s hs, ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field t ht]
    exact_mod_cast hle
  · haveI : CharZero A := CharP.charP_to_charZero _
    haveI : CharZero B := CharP.charP_to_charZero _
    haveI : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective_int _)
    have hle := trdeg_le ℤ A B K b.toIntAlgHom hb
    rw [IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one A (RingHom.injective_int _),
      IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one B (RingHom.injective_int _)]
    exact WithBot.coe_le_coe.2 (add_le_add_left (OrderHomClass.mono Cardinal.toENat hle) 1)

theorem finiteType_int_quotient {A : Type} [CommRing A] [Algebra.FiniteType ℤ A] (I : Ideal A) :
    @Algebra.FiniteType ℤ (A ⧸ I) _ _ (Ring.toIntAlgebra _) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mk I).toIntAlgHom Ideal.Quotient.mk_surjective

theorem finiteType_int_mvPolynomial (A σ : Type) [CommRing A] [Algebra.FiniteType ℤ A] [Finite σ] :
    @Algebra.FiniteType ℤ (MvPolynomial σ A) _ _ (Ring.toIntAlgebra _) := by
  have h : Algebra.FiniteType ℤ (MvPolynomial σ A) := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  convert h
  · rfl
  · exact Subsingleton.elim _ _

theorem ringKrullDim_quotient_ker_le {A B K : Type} [CommRing A] [CommRing B] [Field K]
    [Algebra.FiniteType ℤ A] [Algebra.FiniteType ℤ B] (a : A →+* K) (ha : a.QuasiFinite) (b : B →+* K) :
    ringKrullDim (B ⧸ RingHom.ker b) ≤ ringKrullDim (A ⧸ RingHom.ker a) := by
  haveI := RingHom.ker_isPrime a
  haveI := RingHom.ker_isPrime b
  letI := a.toAlgebra
  letI := (RingHom.kerLift a).toAlgebra
  haveI : IsScalarTower A (A ⧸ RingHom.ker a) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.QuasiFinite A K := ha
  haveI : Algebra.QuasiFinite (A ⧸ RingHom.ker a) K := .of_restrictScalars A _ _
  haveI : FaithfulSMul (A ⧸ RingHom.ker a) K := (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective a)
  haveI := isAlgebraic_of_quasiFinite (A ⧸ RingHom.ker a) K
  haveI := finiteType_int_quotient (RingHom.ker a)
  haveI := finiteType_int_quotient (RingHom.ker b)
  exact ringKrullDim_le_of_isAlgebraic _ _ K (RingHom.kerLift b) (RingHom.kerLift_injective b)

theorem exists_flat_quasiFinite {o : Type} [CommRing o] {X : Scheme.{0}} (s : X ⟶ Sp o) (D : ℕ)
    (hs : SmoothOfRelativeDimension D s) (y : X) :
    ∃ φ : MvPolynomial (Fin D) o →+* X.presheaf.stalk y, φ.Flat ∧ φ.QuasiFinite := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hW : IsAffineOpen W := hW
  have h0 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) s hs ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  obtain ⟨t, ht, h'⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0
  have hcov := hW.self_le_iSup_basicOpen_iff.2 ht hxW
  obtain ⟨⟨g, hg⟩, hxg⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hl := hW.isLocalization_basicOpen g
  have h1 := h' g hg Γ(X, X.basicOpen g)
  have h3 := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv h1
  obtain ⟨φ, -, hφ⟩ := h3.exists_etale_mvPolynomial
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hxg⟩ : X.basicOpen g)
  haveI := (hW.basicOpen g).isLocalization_stalk ⟨y, hxg⟩
  letI := φ.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin D) o) Γ(X, X.basicOpen g) := hφ
  refine ⟨(algebraMap Γ(X, X.basicOpen g) (X.presheaf.stalk y)).comp φ, RingHom.Flat.comp ?_ ?_, RingHom.QuasiFinite.comp ?_ ?_⟩
  · exact (inferInstance : Module.Flat (MvPolynomial (Fin D) o) Γ(X, X.basicOpen g))
  · exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ ((hW.basicOpen g).primeIdealOf ⟨y, hxg⟩).asIdeal.primeCompl)
  · exact RingHom.quasiFinite_algebraMap.2 (.of_isLocalization ((hW.basicOpen g).primeIdealOf ⟨y, hxg⟩).asIdeal.primeCompl)
  · exact (inferInstance : Algebra.QuasiFinite (MvPolynomial (Fin D) o) Γ(X, X.basicOpen g))

theorem ringKrullDim_le_add_of_flat {B R : Type} [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (ψ : B →+* R) (hψ : ψ.Flat) :
    ringKrullDim B ≤ ringKrullDim R + ringKrullDim (B ⧸ RingHom.ker ((residue R).comp ψ)) := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  obtain ⟨h, hh, hle⟩ := DedekindDimFormula.affine_heights ℤ B
  set P := RingHom.ker ((residue R).comp ψ) with hP
  haveI : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  have h1 : ringKrullDim B ≤ (M.height : WithBot ℕ∞) :=
    (ringKrullDim_le_iff_isMaximal_height_le _).2 fun m hm => by rw [hh m, hh M]
  refine h1.trans ((hle P M).trans (add_le_add_left ?_ _))
  letI := ψ.toAlgebra
  haveI : Module.Flat B R := hψ
  haveI : (maximalIdeal R).LiesOver P := ⟨by rw [hP, ← RingHom.comap_ker, ker_residue]; rfl⟩
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown P (maximalIdeal R)]
  exact WithBot.coe_le_coe.2 le_self_add

theorem mem_of_mem_minimalPrimes {A : Type} [CommRing A] [IsNoetherianRing A] {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (hD : Dense U) (Q : PrimeSpectrum A) (hQ : Q.asIdeal ∈ minimalPrimes A) : Q ∈ U := by
  classical
  let t := (minimalPrimes.finite_of_isNoetherianRing A).toFinset.erase Q.asIdeal
  have h1 : ¬ t.inf id ≤ Q.asIdeal := fun h => by
    obtain ⟨I, hI, hle⟩ := Q.isPrime.inf_le'.1 h
    obtain ⟨hne, hI⟩ := Finset.mem_erase.1 hI
    rw [Set.Finite.mem_toFinset] at hI
    exact hne (le_antisymm hle (hQ.2 hI.1 hle))
  obtain ⟨f, hf, hfQ⟩ := SetLike.not_le_iff_exists.1 h1
  obtain ⟨z, hz, hzU⟩ := hD.inter_open_nonempty _ (PrimeSpectrum.basicOpen f).isOpen ⟨Q, hfQ⟩
  obtain ⟨Q', hQ', hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := z.asIdeal) bot_le
  have hQQ : Q' = Q.asIdeal := by
    by_contra hne
    have : t.inf id ≤ Q' := Finset.inf_le (f := id) (Finset.mem_erase.2 ⟨hne, (Set.Finite.mem_toFinset _).2 hQ'⟩)
    exact hz (hle (this hf))
  exact ((PrimeSpectrum.le_iff_specializes Q z).1 (show Q.asIdeal ≤ z.asIdeal from hQQ ▸ hle)).mem_open hU hzU

theorem finiteType_sections {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {S : Scheme.{0}} (s : S ⟶ Sp o)
    [LocallyOfFiniteType s] {U : S.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(S, U) := by
  have hl : LocallyOfFiniteType (Spec.map (Spec.preimage (hU.fromSpec ≫ s))) := by
    rw [Spec.map_preimage]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hl
  have h := hl.comp (RingHom.finiteType_algebraMap.2 (inferInstance : Algebra.FiniteType ℤ o))
  rw [← RingHom.finiteType_algebraMap]
  convert h using 1
  exact Subsingleton.elim _ _

theorem exists_stalk_hom {S : Scheme.{0}} {U : S.Opens} (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(S, U)) :
    ∃ a : Γ(S, U) →+* S.presheaf.stalk (hU.fromSpec P), a.QuasiFinite ∧ (maximalIdeal _).comap a = P.asIdeal ∧
      ringKrullDim (S.presheaf.stalk (hU.fromSpec P)) = P.asIdeal.height := by
  have hx : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  letI : Algebra Γ(S, U) (S.presheaf.stalk (hU.fromSpec P)) :=
    TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨hU.fromSpec P, hx⟩ : U)
  haveI : IsLocalization.AtPrime (S.presheaf.stalk (hU.fromSpec P)) P.asIdeal := hU.isLocalization_stalk' P hx
  exact ⟨algebraMap _ _, RingHom.quasiFinite_algebraMap.2 (.of_isLocalization P.asIdeal.primeCompl),
    IsLocalization.AtPrime.under_maximalIdeal _ P.asIdeal, IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal _⟩

theorem ringKrullDim_sections_le {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {S X : Scheme.{0}} (s : S ⟶ Sp o)
    [LocallyOfFiniteType s] (j : X ⟶ S) [IsOpenImmersion j] (hj : Dense (Set.range j)) (sX : X ⟶ Sp o) (D : ℕ)
    (hs : SmoothOfRelativeDimension D sX) {U : S.Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(S, U) ≤ ringKrullDim o + D := by
  haveI := finiteType_sections s hU
  haveI : IsNoetherianRing Γ(S, U) := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI : IsNoetherianRing o := Algebra.FiniteType.isNoetherianRing ℤ _
  rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot Γ(S, U))]
  refine IntFiniteTypeDim.ringKrullDim_quotient_le_of_minimalPrimes _ _ fun Q hQ => ?_
  let q : PrimeSpectrum Γ(S, U) := ⟨Q, hQ.1.1⟩
  obtain ⟨y, hy⟩ : q ∈ hU.fromSpec ⁻¹' Set.range j :=
    mem_of_mem_minimalPrimes (j.isOpenEmbedding.isOpen_range.preimage hU.fromSpec.continuous)
      (hj.preimage hU.fromSpec.isOpenEmbedding.isOpenMap) q hQ
  obtain ⟨φ, -, hφ⟩ := exists_flat_quasiFinite sX D hs y
  obtain ⟨a, -, ha, -⟩ := exists_stalk_hom hU q
  let e : S.presheaf.stalk (hU.fromSpec q) →+* X.presheaf.stalk y :=
    (j.stalkMap y).hom.comp (S.presheaf.stalkCongr (.of_eq hy.symm)).hom.hom
  haveI : IsLocalHom e := RingHom.isLocalHom_comp _ _
  haveI := finiteType_int_mvPolynomial o (Fin D)
  have h := ringKrullDim_quotient_ker_le ((residue _).comp φ)
    ((RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _ residue_surjective)).comp hφ)
    ((residue _).comp (e.comp a))
  rw [← RingHom.comap_ker (residue _) (e.comp a), ker_residue, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap, ha] at h
  refine h.trans ((ringKrullDim_quotient_le _).trans ?_)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem flat_map {A B σ : Type} [CommRing A] [CommRing B] {f : A →+* B} (hf : f.Flat) :
    (MvPolynomial.map (σ := σ) f).Flat := by
  letI := f.toAlgebra
  letI : Algebra (MvPolynomial σ A) (MvPolynomial σ B) := MvPolynomial.algebraMvPolynomial
  haveI : Module.Flat A B := hf
  exact RingHom.Flat.isStableUnderBaseChange A B (MvPolynomial σ A) (MvPolynomial σ B) hf

theorem card_basis {r : ℕ} {J : Type} [Fintype J] (ε : Module.Basis J ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) :
    Fintype.card J = r * (r + 1) / 2 := by
  have e : balForms (id : ℤ → ℤ) (Fin r → ℤ) = GlobalTheory.Forms.symForms ℤ (Fin r → ℤ) ℤ :=
    Submodule.ext fun β => mem_balForms_int.trans GlobalTheory.Forms.mem_symForms.symm
  rw [← Module.finrank_eq_card_basis ε, e, GlobalTheory.Forms.finrank_symLattice, Module.finrank_fin_fun, Nat.choose_two_right,
    Nat.add_sub_cancel, mul_comm]

theorem exists_ringKrullDim_eq (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] : ∃ k : ℕ, ringKrullDim A = k := by
  obtain ⟨h, hh, -⟩ := haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int; DedekindDimFormula.affine_heights ℤ A
  have h1 : ringKrullDim A ≤ (h : ℕ∞) := (ringKrullDim_le_iff_isMaximal_height_le _).2 fun m hm => by rw [hh m]
  have h0 : 0 ≤ ringKrullDim A := ringKrullDim_nonneg_of_nontrivial
  induction hA : ringKrullDim A with
  | bot => simp [hA] at h0
  | coe a =>
    rw [hA, WithBot.coe_le_coe] at h1
    exact ⟨a.toNat, by rw [← WithBot.coe_natCast, ENat.coe_toNat (ne_top_of_le_ne_top (ENat.coe_ne_top h) h1)]⟩

theorem ringKrullDim_stalk_le {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {S X : Scheme.{0}} (s : S ⟶ Sp o)
    [LocallyOfFiniteType s] (j : X ⟶ S) [IsOpenImmersion j] (hj : Dense (Set.range j)) (sX : X ⟶ Sp o) (D : ℕ)
    (hs : SmoothOfRelativeDimension D sX) {B R : Type} [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B] [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R) (hψ : ψ.Flat) (hB : ringKrullDim B = ringKrullDim o + D) {x : S}
    (f : S.presheaf.stalk x →+* R) [IsLocalHom f] (hf : ((residue R).comp f).Finite) :
    ringKrullDim (S.presheaf.stalk x) ≤ ringKrullDim R := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨P, rfl⟩ : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_stalk_hom hU P
  haveI := finiteType_sections s hU
  have h1 := ringKrullDim_quotient_ker_le (((residue R).comp f).comp a) ((RingHom.QuasiFinite.of_finite hf).comp ha₁)
    ((residue R).comp ψ)
  rw [← RingHom.comap_ker _ a, ← RingHom.comap_ker _ f, ker_residue, IsLocalRing.maximalIdeal_comap, ha₂] at h1
  haveI := P.isPrime
  haveI := finiteType_int_quotient P.asIdeal
  obtain ⟨k, hk⟩ := exists_ringKrullDim_eq (Γ(S, U) ⧸ P.asIdeal)
  have h2 := (RegularAscent.height_add_ringKrullDim_quotient_le P.asIdeal).trans
    ((ringKrullDim_sections_le s j hj sX D hs hU).trans (hB.ge.trans
      ((ringKrullDim_le_add_of_flat ψ hψ).trans (add_le_add_right h1 _))))
  rw [hk] at h2
  rw [ha₃]
  exact ENat.WithBot.add_le_add_natCast_right_iff.1 h2

theorem ringKrullDim_stalk_le_chart : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite → ringKrullDim (S.presheaf.stalk (ξ (closedPoint C.R))) ≤ ringKrullDim C.R := by
  intro g _ φ _ _ n hn _ F Z z i OZ d S π j _ BD _ hB C G₁ _ _ y α₁ ξ _ _ hf
  obtain ⟨J, -, -, -, -, hP, hD, -⟩ := hB
  have hn0 : n ≠ 0 := by omega
  haveI : IsProper (π ≫ z) := GlobalTheory.SchemeWords.isProper_of_isProjOver hP
  haveI := finiteType_cycAway n
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI : IsNoetherianRing C.R := C.compl.1
  have hd : SmoothOfRelativeDimension C.h C.F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim C.F.univ (by omega) (cycBase hn0).ζ.isUnit (isUnit_natCast hn0)
  haveI := GlobalTheory.smoothOfRelativeDimension_powObj C.F.univ.A C.h hd C.T.r
  haveI := C.F.smooth
  obtain ⟨χ, hχ, -⟩ := exists_flat_quasiFinite (LowChart.toO C.F C.T.r) (C.T.r * C.h + C.h * (C.h + 1) / 2)
    (smoothOfRelativeDimension_comp _ _ (LowChart.powA C.F C.T.r).hom C.F.s) (C.u (closedPoint C.W))
  haveI := finiteType_int_mvPolynomial (cycAway n) (Fin (C.T.r * C.h + C.h * (C.h + 1) / 2))
  haveI := finiteType_int_mvPolynomial (MvPolynomial (Fin (C.T.r * C.h + C.h * (C.h + 1) / 2)) (cycAway n)) (Fin C.m ⊕ Fin C.N)
  refine ringKrullDim_stalk_le (π ≫ z) j hD F.s _ F.smooth _ ((flat_map (hχ.comp C.u_et.1)).comp C.compl.2.2.1) ?_ _ hf
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_fin, card_basis C.ε, add_assoc, ← Nat.cast_add]
  congr 2
  obtain ⟨a, ha⟩ := Nat.even_mul_succ_self C.h
  obtain ⟨b, hb⟩ := Nat.even_mul_succ_self C.T.r
  have : (C.h + C.T.r) * (C.h + C.T.r + 1) = C.h * (C.h + 1) + C.T.r * (C.T.r + 1) + 2 * (C.T.r * C.h) := by ring
  rw [C.genus] at this
  omega

end GlobalTheory.TChart.ChartDim
