import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCover
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

namespace GlobalTheory.GenFinEt

private theorem generic_finite (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B] :
    ∃ a : A, a ≠ 0 ∧ ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
      [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'],
      IsLocalization.Away a A' → IsLocalization.Away (algebraMap A B a) B' → Module.Finite A' B' := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  obtain ⟨y, hy, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples A s
  refine ⟨y, hy, fun A' B' _ _ _ _ _ _ _ _ hA hB => ?_⟩
  obtain ⟨u, hu⟩ : IsUnit (algebraMap A A' y) := IsLocalization.Away.algebraMap_isUnit y
  have hyy : algebraMap B B' (algebraMap A B y) = algebraMap A' B' (u : A') := by
    rw [hu, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hcancel : ∀ (n : ℕ) (x : B'), _root_.IsIntegral A' (x * algebraMap A' B' (u : A') ^ n) →
      _root_.IsIntegral A' x := by
    intro n x hx
    have : x = ((u⁻¹ : A'ˣ) : A') ^ n • (x * algebraMap A' B' (u : A') ^ n) := by
      rw [Algebra.smul_def, map_pow, mul_left_comm, ← mul_pow, ← map_mul, Units.inv_mul, map_one,
        one_pow, mul_one]
    rw [this]
    exact hx.smul _
  have hB1 : ∀ b : B, _root_.IsIntegral A' (algebraMap B B' b) := by
    have hle : Algebra.adjoin A (s : Set B) ≤
        ((integralClosure A' B').restrictScalars A).comap (IsScalarTower.toAlgHom A B B') := by
      refine Algebra.adjoin_le fun z hz => ?_
      have h1 : _root_.IsIntegral A' (algebraMap B B' (y • z)) :=
        ((hint z hz).map (IsScalarTower.toAlgHom A B B')).tower_top
      refine hcancel 1 _ ?_
      rw [Algebra.smul_def, map_mul, hyy, mul_comm] at h1
      rw [pow_one]
      exact h1
    intro b
    exact hle (hs ▸ Algebra.mem_top)
  haveI : Algebra.IsIntegral A' B' := ⟨fun x => by
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (algebraMap A B y)) x
    refine hcancel n x ?_
    simp only [map_pow, hyy] at hx
    rw [hx]
    exact hB1 b⟩
  haveI : Algebra.FiniteType B B' := IsLocalization.finiteType_of_monoid_fg
    (Submonoid.powers (algebraMap A B y)) B'
  haveI : Algebra.FiniteType A B' := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  haveI : Algebra.FiniteType A' B' := Algebra.FiniteType.of_restrictScalars_finiteType A A' B'
  exact Algebra.IsIntegral.finite

private theorem generic_free (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] :
    ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
      [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'],
      IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' →
      Module.Free A' B' := by
  haveI : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) B) (FractionRing A)
  refine ⟨r, nonZeroDivisors.ne_zero hr, fun c A' B' _ _ _ _ _ _ _ _ hA hB => ?_⟩
  have hu : IsUnit (algebraMap A A' r) :=
    isUnit_of_mul_isUnit_left (y := algebraMap A A' c)
      (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (r * c))
  letI : Algebra (Localization.Away r) A' := (IsLocalization.Away.lift r hu).toAlgebra
  haveI : IsScalarTower A (Localization.Away r) A' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq r hu x).symm
  haveI : Module.Free (Localization.Away r) (TensorProduct A (Localization.Away r) B) :=
    Module.Free.of_equiv (IsLocalizedModule.isBaseChange (Submonoid.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) B)).equiv.symm
  haveI : Module.Free A' (TensorProduct A A' B) :=
    Module.Free.of_equiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away r) A' A' B)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers (r * c))) B' := by
    rw [Algebra.algebraMapSubmonoid_powers]; exact hB
  exact Module.Free.of_equiv (IsLocalizedModule.isBaseChange (Submonoid.powers (r * c)) A'
    (IsScalarTower.toAlgHom A B B').toLinearMap).equiv

private theorem generic_etale (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CharZero A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Module.Finite A B] :
    ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
      [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'],
      IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' →
      Algebra.Etale A' B' := by
  haveI : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
  haveI : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) := inferInstance
  haveI : Algebra.FormallyEtale (FractionRing A) (FractionRing B) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale A (FractionRing A) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  haveI : Algebra.FormallyEtale A (FractionRing B) :=
    Algebra.FormallyEtale.comp A (FractionRing A) (FractionRing B)
  haveI : IsLocalization (⊥ : Ideal B).primeCompl (FractionRing B) := by
    rw [Ideal.primeCompl_bot]; infer_instance
  haveI : Algebra.IsEtaleAt A (⊥ : Ideal B) :=
    Algebra.FormallyEtale.of_equiv ((IsLocalization.algEquiv (⊥ : Ideal B).primeCompl (FractionRing B)
      (Localization.AtPrime (⊥ : Ideal B))).restrictScalars A)
  obtain ⟨f, hf, het⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) (⊥ : Ideal B)
  have hf0 : f ≠ 0 := by simpa using hf
  obtain ⟨a, ha, hfa⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) f).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hf0)
  refine ⟨a, ha, fun c A' B' _ _ _ _ _ _ _ _ hA hB => ?_⟩
  have h1 : Algebra.Etale A (Localization.Away (algebraMap A B (a * c))) := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale] at het ⊢
    refine subset_trans ?_ het
    obtain ⟨g, hg⟩ := hfa
    rw [map_mul, hg, mul_assoc]
    exact PrimeSpectrum.basicOpen_mul_le_left _ _
  haveI : Algebra.Etale A B' :=
    Algebra.Etale.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (algebraMap A B (a * c)))
      (Localization.Away (algebraMap A B (a * c))) B').restrictScalars A)
  haveI : Algebra.FormallyEtale A' B' :=
    Algebra.FormallyEtale.localization_base (Submonoid.powers (a * c))
  haveI : Algebra.FiniteType A A' := IsLocalization.finiteType_of_monoid_fg
    (Submonoid.powers (a * c)) A'
  haveI : Algebra.FinitePresentation A' B' :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A A' B'
  exact ⟨inferInstance, inferInstance⟩

private theorem isFractionRing_evaluation (X : Scheme.{0}) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.residueField x) := by
  subst hx
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  let e : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

private theorem inj_alg_rank {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    (h : f (genericPoint Y) = genericPoint X) (hδ : f.residueDegree (genericPoint Y) ≠ 0)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hyV : genericPoint Y ∈ V) (e : V ≤ f ⁻¹ᵁ U) :
    letI := (f.appLE U V e).hom.toAlgebra
    FaithfulSMul Γ(X, U) Γ(Y, V) ∧ Algebra.IsAlgebraic Γ(X, U) Γ(Y, V) ∧
      Module.finrank Γ(X, U) Γ(Y, V) = f.residueDegree (genericPoint Y) := by
  have hxU : f (genericPoint Y) ∈ U := e hyV
  letI := (f.appLE U V e).hom.toAlgebra
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  letI : Algebra Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    (Y.evaluation V _ hyV).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Y)).hom.toAlgebra
  letI : Algebra Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (f.appLE U V e ≫ Y.evaluation V _ hyV).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hnat : X.evaluation U _ hxU ≫ f.residueFieldMap (genericPoint Y) =
      f.appLE U V e ≫ Y.evaluation V _ hyV := by
    rw [Scheme.evaluation_naturality f _ hxU]
    simp [Scheme.Hom.appLE, Scheme.evaluation]
  haveI : IsScalarTower Γ(X, U) (X.residueField (f (genericPoint Y)))
      (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' congr($(hnat).hom).symm
  haveI := isFractionRing_evaluation X hU h hxU
  haveI := isFractionRing_evaluation Y hV rfl hyV
  haveI : FiniteDimensional (X.residueField (f (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hδ)
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : Nonempty V := ⟨⟨_, hyV⟩⟩
  have hinj : Function.Injective (algebraMap Γ(X, U) (Y.residueField (genericPoint Y))) := by
    rw [IsScalarTower.algebraMap_eq Γ(X, U) (X.residueField (f (genericPoint Y)))]
    exact (f.residueFieldMap (genericPoint Y)).hom.injective.comp
      (IsFractionRing.injective Γ(X, U) (X.residueField (f (genericPoint Y))))
  refine ⟨?_, ?_, (IsFractionRing.finrank_eq Γ(X, U) (X.residueField (f (genericPoint Y)))
    Γ(Y, V) (Y.residueField (genericPoint Y))).symm⟩
  · rw [faithfulSMul_iff_algebraMap_injective]
    rw [IsScalarTower.algebraMap_eq Γ(X, U) Γ(Y, V)] at hinj
    exact Function.Injective.of_comp (f := algebraMap Γ(Y, V) (Y.residueField (genericPoint Y))) hinj
  · haveI : Algebra.IsAlgebraic Γ(X, U) (Y.residueField (genericPoint Y)) :=
      (IsFractionRing.comap_isAlgebraic_iff (K := X.residueField (f (genericPoint Y)))).2 inferInstance
    exact Algebra.IsAlgebraic.of_injective
      (IsScalarTower.toAlgHom Γ(X, U) Γ(Y, V) (Y.residueField (genericPoint Y)))
      (IsFractionRing.injective _ _)

set_option backward.isDefEq.respectTransparency.types false in
private theorem preimage_eq_of_finite {X Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) [IsSeparated π]
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hyV : genericPoint Y ∈ V) (e : V ≤ π ⁻¹ᵁ U) (hfin : (π.appLE U V e).hom.Finite) :
    π ⁻¹ᵁ U = V := by
  haveI : IsAffine U := hU
  haveI : IsAffine V := hV
  haveI : IsFinite (π.resLE U V e) := by
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    refine ⟨inferInstance, ?_⟩
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    simp only [CommRingCat.hom_comp]
    refine RingHom.Finite.comp (RingHom.Finite.comp ?_ hfin) ?_
    · exact RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    · exact RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
  haveI : IsFinite (Y.homOfLE e ≫ π ∣_ U) := this
  haveI : IsFinite (Y.homOfLE e) := IsFinite.of_comp _ (π ∣_ U)
  haveI : Nonempty (π ⁻¹ᵁ U : Y.Opens) := ⟨⟨_, e hyV⟩⟩
  have hcl : IsClopen (Set.range (Y.homOfLE e)) :=
    ⟨(Y.homOfLE e).isClosedMap.isClosed_range, (Y.homOfLE e).isOpenEmbedding.isOpen_range⟩
  have huniv := hcl.eq_univ ⟨_, ⟨⟨_, hyV⟩, rfl⟩⟩
  refine le_antisymm (fun y hy => ?_) e
  obtain ⟨z, hz⟩ : (⟨y, hy⟩ : (π ⁻¹ᵁ U : Y.Opens)) ∈ Set.range (Y.homOfLE e) := huniv ▸ trivial
  have : z.1 = y := by
    have := congrArg Subtype.val hz
    exact (Scheme.homOfLE_apply e z).symm.trans this
  exact this ▸ z.2

private theorem shrink {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) [IsSeparated π]
    (hg : π (genericPoint Y) = genericPoint X) {U₀ : X.Opens} {V₀ : Y.Opens} (hU₀ : IsAffineOpen U₀)
    (hV₀ : IsAffineOpen V₀) (hyV₀ : genericPoint Y ∈ V₀) (hVle : V₀ ≤ π ⁻¹ᵁ U₀)
    (P : ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A' B'], Prop)
    (a : Γ(X, U₀)) (ha : a ≠ 0)
    (H : letI := (π.appLE U₀ V₀ hVle).hom.toAlgebra
      ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra Γ(X, U₀) A'] [Algebra Γ(Y, V₀) B']
      [Algebra A' B'] [Algebra Γ(X, U₀) B'] [IsScalarTower Γ(X, U₀) A' B']
      [IsScalarTower Γ(X, U₀) Γ(Y, V₀) B'],
      IsLocalization.Away a A' → IsLocalization.Away (algebraMap Γ(X, U₀) Γ(Y, V₀) a) B' →
      Module.Finite A' B' ∧ P A' B') :
    ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧
      (letI := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
       Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ P Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
  letI : Algebra Γ(X, U₀) Γ(Y, V₀) := (π.appLE U₀ V₀ hVle).hom.toAlgebra
  have hUU₀ : X.basicOpen a ≤ U₀ := X.basicOpen_le _
  have hUa : IsAffineOpen (X.basicOpen a) := hU₀.basicOpen _
  have hxU : genericPoint X ∈ X.basicOpen a := by
    have hne : X.basicOpen a ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff _).1 h)
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen a).isOpen).2 ⟨z, trivial, hz⟩
  set U : X.Opens := X.basicOpen a with hU_def
  set V : Y.Opens := Y.basicOpen (π.appLE U₀ V₀ hVle a) with hV_def
  have hVV₀ : V ≤ V₀ := Y.basicOpen_le _
  have hVe : V = V₀ ⊓ π ⁻¹ᵁ U := Scheme.basicOpen_appLE π V₀ U₀ hVle _
  have hVU : V ≤ π ⁻¹ᵁ U := by rw [hVe]; exact inf_le_right
  have hVa : IsAffineOpen V := hV₀.basicOpen _
  have hyV : genericPoint Y ∈ V := by
    rw [hVe]; exact ⟨hyV₀, show π (genericPoint Y) ∈ U from hg ▸ hxU⟩
  letI iA : Algebra Γ(X, U₀) Γ(X, U) := (X.presheaf.map (homOfLE hUU₀).op).hom.toAlgebra
  letI iB : Algebra Γ(Y, V₀) Γ(Y, V) := (Y.presheaf.map (homOfLE hVV₀).op).hom.toAlgebra
  letI iAB : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V hVU).hom.toAlgebra
  letI iAB' : Algebra Γ(X, U₀) Γ(Y, V) := (π.appLE U₀ V (hVV₀.trans hVle)).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U₀) Γ(X, U) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.map_appLE hVU (homOfLE hUU₀).op).symm)
  haveI : IsScalarTower Γ(X, U₀) Γ(Y, V₀) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.appLE_map hVle (homOfLE hVV₀).op).symm)
  have hlA : IsLocalization.Away a Γ(X, U) :=
    hU₀.isLocalization_of_eq_basicOpen _ (homOfLE hUU₀) rfl
  have hlB : IsLocalization.Away (algebraMap Γ(X, U₀) Γ(Y, V₀) a) Γ(Y, V) :=
    hV₀.isLocalization_of_eq_basicOpen _ (homOfLE hVV₀) rfl
  obtain ⟨hfin, hP⟩ := H Γ(X, U) Γ(Y, V) hlA hlB
  have hpre : π ⁻¹ᵁ U = V := preimage_eq_of_finite π hUa hVa hyV hVU hfin
  have key : ∀ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U →
      (letI := (π.appLE U W hW).hom.toAlgebra
       Module.Finite Γ(X, U) Γ(Y, W) ∧ P Γ(X, U) Γ(Y, W)) →
      (letI := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
       Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ P Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
    rintro W hW rfl h1
    exact h1
  exact ⟨U, hUa, hxU, hpre ▸ hVa, key V hVU hpre.symm ⟨hfin, hP⟩⟩

end GlobalTheory.GenFinEt

theorem _root_.GlobalTheory.T.exists_affine_etale_finite_nbhd_generic : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧ (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  intro k _ X Y _ _ p q D hX hY π hπ hg hδ
  have hqP : IsProper q := by
    obtain ⟨N, j, _, hj⟩ := hY.isProjOver
    have := isProper_str k N
    exact hj ▸ inferInstance
  have : IsSeparated (π ≫ p) := hπ ▸ (inferInstance : IsSeparated q)
  have hsep : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ (inferInstance : LocallyOfFiniteType q)
  have hlft : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have := hX.isLocallyNoetherian
  obtain ⟨U₁, hU₁, hxU₁, hV₁, hfin₁, -⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧
      IsAffineOpen (π ⁻¹ᵁ U) ∧ (letI := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
       Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ True) := by
    obtain ⟨U₀, hU₀, hxU₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (genericPoint X))
    have hyU₀ : genericPoint Y ∈ π ⁻¹ᵁ U₀ := by
      show π (genericPoint Y) ∈ U₀
      rw [hg]; exact hxU₀
    obtain ⟨V₀, hV₀, hyV₀, hVle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hyU₀
    haveI : Nonempty U₀ := ⟨⟨_, hxU₀⟩⟩
    letI : Algebra Γ(X, U₀) Γ(Y, V₀) := (π.appLE U₀ V₀ hVle).hom.toAlgebra
    haveI : Algebra.FiniteType Γ(X, U₀) Γ(Y, V₀) :=
      HasRingHomProperty.appLE @LocallyOfFiniteType π hlft ⟨U₀, hU₀⟩ ⟨V₀, hV₀⟩ hVle
    haveI : Algebra.IsAlgebraic Γ(X, U₀) Γ(Y, V₀) :=
      (GenFinEt.inj_alg_rank π hg hδ hU₀ hV₀ hyV₀ hVle).2.1
    obtain ⟨a, ha, H⟩ := GenFinEt.generic_finite Γ(X, U₀) Γ(Y, V₀)
    exact GenFinEt.shrink π hg hU₀ hV₀ hyV₀ hVle (fun _ _ _ _ _ => True) a ha
      fun A' B' _ _ _ _ _ _ _ _ hA hB => ⟨H A' B' hA hB, trivial⟩
  have hyV₁ : genericPoint Y ∈ π ⁻¹ᵁ U₁ := by
    show π (genericPoint Y) ∈ U₁
    rw [hg]; exact hxU₁
  obtain ⟨U, hU, hxU, hV, hfin, hfree, het⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧
      IsAffineOpen (π ⁻¹ᵁ U) ∧ (letI := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
       Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧
        Algebra.Etale Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
    haveI : Nonempty U₁ := ⟨⟨_, hxU₁⟩⟩
    haveI : Nonempty (π ⁻¹ᵁ U₁ : Y.Opens) := ⟨⟨_, hyV₁⟩⟩
    letI : Algebra Γ(X, U₁) Γ(Y, π ⁻¹ᵁ U₁) := (π.appLE U₁ (π ⁻¹ᵁ U₁) le_rfl).hom.toAlgebra
    haveI : IsNoetherianRing Γ(X, U₁) := IsLocallyNoetherian.component_noetherian ⟨U₁, hU₁⟩
    haveI : CharZero Γ(X, U₁) :=
      ((resG X (le_top : U₁ ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hX.charZero
    haveI : FaithfulSMul Γ(X, U₁) Γ(Y, π ⁻¹ᵁ U₁) :=
      (GenFinEt.inj_alg_rank π hg hδ hU₁ hV₁ hyV₁ le_rfl).1
    obtain ⟨a, ha, Ha⟩ := GenFinEt.generic_free Γ(X, U₁) Γ(Y, π ⁻¹ᵁ U₁)
    obtain ⟨b, hb, Hb⟩ := GenFinEt.generic_etale Γ(X, U₁) Γ(Y, π ⁻¹ᵁ U₁)
    refine GenFinEt.shrink π hg hU₁ hV₁ hyV₁ le_rfl
      (fun A' B' _ _ _ => Module.Free A' B' ∧ Algebra.Etale A' B') (a * b) (mul_ne_zero ha hb)
      fun A' B' _ _ _ _ _ _ _ _ hA hB => ⟨?_, Ha b A' B' hA hB,
        Hb a A' B' (by rw [mul_comm]; exact hA) (by rw [mul_comm]; exact hB)⟩
    haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ U₁) (Submonoid.powers (a * b))) B' := by
      rw [Algebra.algebraMapSubmonoid_powers]; exact hB
    exact Module.Finite.of_isLocalization Γ(X, U₁) Γ(Y, π ⁻¹ᵁ U₁) (Submonoid.powers (a * b))
  have hyV : genericPoint Y ∈ π ⁻¹ᵁ U := by
    show π (genericPoint Y) ∈ U
    rw [hg]; exact hxU
  refine ⟨U, hU, hxU, hV, ?_⟩
  rw [Scheme.Hom.app_eq_appLE]
  exact ⟨het, hfin, hfree, (GenFinEt.inj_alg_rank π hg hδ hU hV hyV le_rfl).2.2⟩
