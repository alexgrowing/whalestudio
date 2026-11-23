import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.IsSemiAbelianUnit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNumberFieldPointSiegelFamilyKnownValue
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InputExistsOfMemberExists
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegelAway

open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw GlobalTheory.SiegelTor

theorem exists_section (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X : Scheme.{0}} (p : X ⟶ Sp O) [IsProper p] (x : Sp K ⟶ X) (hx : x ≫ p = spMap (algebraMap O K)) :
    ∃ g : Sp O ⟶ X, spMap (algebraMap O K) ≫ g = x := by
  let R : CommRingCat.{0} := CommRingCat.of O
  have hZ : ∀ z : Spec R, ValuationRing ((Spec R).presheaf.stalk z) := fun z => by
    letI : Algebra O ((Spec R).presheaf.stalk z) := StructureSheaf.stalkAlgebra O z
    have : z.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := O) z
    have : IsLocalization.AtPrime ((Spec R).presheaf.stalk z) z.asIdeal := StructureSheaf.IsLocalization.to_stalk O z
    have hd : IsDedekindDomain ((Spec R).presheaf.stalk z) := IsLocalization.AtPrime.isDedekindDomain O z.asIdeal _
    exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain ((Spec R).presheaf.stalk z)).out 2 1).1 hd
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField O K
  obtain ⟨U, hU, f, h1, h2⟩ := spread_out_of_isGermInjective' (𝟙 (Spec R)) p (x := genericPoint _) (e.inv ≫ x)
    (by rw [Category.assoc, hx, Category.comp_id, Iso.inv_comp_eq]; exact he.symm)
  have : Nonempty U.toScheme := ⟨⟨_, hU⟩⟩
  have : X.IsSeparated := ⟨by
    rw [← terminal.comp_from p]
    infer_instance⟩
  obtain ⟨g, g1, -⟩ := TorusConst.exists_extension hZ U.ι (𝟙 _) p f h2
  refine ⟨g, ?_⟩
  rw [Iso.inv_comp_eq, ← g1, ← Category.assoc (U.fromSpecStalkOfMem _ _), Scheme.Opens.fromSpecStalkOfMem_ι,
    ← Category.assoc, he] at h1
  exact h1.symm

theorem exists_point {o O K : Type} [CommRing o] [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] (κ : o →+* O) {X : Scheme.{0}} (s : X ⟶ Sp o) [IsProper s] (y : Sp K ⟶ X)
    (hy : y ≫ s = spMap ((algebraMap O K).comp κ)) : ∃ g : Sp O ⟶ X, spMap (algebraMap O K) ≫ g = y := by
  have hsq : y ≫ s = spMap (algebraMap O K) ≫ spMap κ := hy.trans (spMap_comp _ _)
  obtain ⟨t, ht⟩ := exists_section O K (pullback.snd s (spMap κ)) (pullback.lift _ _ hsq) (pullback.lift_snd _ _ _)
  exact ⟨t ≫ pullback.fst _ _, by rw [← Category.assoc, ht, pullback.lift_fst]⟩

theorem isIso_of_dim_zero {K : Type} [Field K] (P : Out.PolAV (Sp K)) (hg : P.g = 0) : IsIso P.A.hom := by
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have : Etale P.A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 (hg ▸ P.smoothDim)
  let e : Sp K ⟶ P.A.left := (1 : Out.baseOver (Sp K) ⟶ P.A).left
  have he : e ≫ P.A.hom = 𝟙 _ := Over.w _
  have := isOpenImmersion_of_section_of_etale P.A.hom e he
  have : IsClosedImmersion (e ≫ P.A.hom) := by rw [he]; infer_instance
  have : IsClosedImmersion e := IsClosedImmersion.of_comp e P.A.hom
  have : ConnectedSpace P.A.left := GeometricallyConnected.connectedSpace_of_subsingleton P.A.hom
  have hs : Function.Surjective e := by
    rw [← Set.range_eq_univ]
    exact IsClopen.eq_univ ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩
      ⟨_, (default : PrimeSpectrum K), rfl⟩
  have : IsIso e := (isIso_iff_isOpenImmersion_and_surjective e).2 ⟨inferInstance, ⟨hs⟩⟩
  have : IsIso (e ≫ P.A.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e P.A.hom

theorem isGrpPullback_unit {S S' : Scheme.{0}} (A : Over S') [GrpObj A] [IsIso A.hom] (f : S' ⟶ S) :
    IsGrpPullback A (𝟙_ (Over S)) f (A.hom ≫ f) := by
  haveI : IsIso (𝟙_ (Over S)).hom := inferInstanceAs (IsIso (𝟙 S))
  refine ⟨IsPullback.of_vert_isIso ⟨Category.comp_id _⟩, fun T x y x₀ y₀ _ _ => ?_⟩
  refine ((Category.comp_id _).symm.trans (Over.w (x₀ * y₀))).trans ?_
  rw [← Category.assoc, Over.w]
  rfl

theorem exists_siegel_point {h n : ℕ} (hn : 0 < n) (F : SFam h n (zetaAway n)) (K : Type) [Field K] [NumberField K]
    (P : Out.PolAV (Sp K)) (hP : P.g = h) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (j : K →+* K') (em : cycAway n →+* K') (Q : Out.PolAV (Sp K'))
      (φ : Q.A.left ⟶ P.A.left) (q : Sp K' ⟶ F.X) (χ : Q.A.left ⟶ F.univ.A.left),
      IsGrpPullback Q.A P.A (spMap j) φ ∧ q ≫ F.s = spMap em ∧ IsGrpPullback Q.A F.univ.A q χ := by
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  haveI : NeZero n := ⟨hn.ne'⟩
  have hζ : IsPrimitiveRoot (zeta n) n := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  let kσ : IntermediateField ℚ ℂ := σ.toRatAlgHom.fieldRange
  have : FiniteDimensional ℚ kσ := σ.toRatAlgHom.toLinearMap.finiteDimensional_range
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta n}) :=
    IntermediateField.adjoin.finiteDimensional ((hζ.isIntegral hn).tower_top)
  let k₀ : IntermediateField ℚ ℂ := kσ ⊔ IntermediateField.adjoin ℚ {zeta n}
  have : FiniteDimensional ℚ k₀ := IntermediateField.finiteDimensional_sup _ _
  let j₀ : K →+* k₀ := σ.codRestrict k₀.toSubfield fun a => (le_sup_left : kσ ≤ k₀) ⟨a, rfl⟩
  obtain ⟨y₁, φ₀, p₀⟩ := SameLam.exists_polPB P j₀
  obtain ⟨k₁, fin₁, le₁, tors⟩ := exists_numberField_torsion_points hL k₀ y₁ n hn
  have : NumberField k₁ := ⟨⟩
  obtain ⟨y, φ₁, p₁⟩ := SameLam.exists_polPB y₁ (IntermediateField.inclusion le₁).toRingHom
  obtain ⟨x, ψ, pψ⟩ := SameLam.exists_polPB y (algebraMap k₁ ℂ)
  have hg : y.g = h := p₁.2.1.trans (p₀.2.1.trans hP)
  have hsub : cycAway n ≤ k₁.toSubfield.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro z (rfl | rfl)
    · exact le₁ ((le_sup_right : IntermediateField.adjoin ℚ {zeta n} ≤ k₀)
        (IntermediateField.subset_adjoin ℚ _ rfl))
    · exact k₁.inv_mem (k₁.natCast_mem n)
  let em : cycAway n →+* k₁ := (cycAway n).subtype.codRestrict k₁.toSubfield fun a => hsub a.2
  have hem : Function.Injective em := fun a b e => Subtype.ext (congrArg (fun z : k₁ => (z : ℂ)) e)
  have hprim₁ : IsPrimitiveRoot (em (zetaAway n)) n := isPrimitiveRoot_map hn.ne' em
  let ze : k₁ˣ := Units.mk0 (em (zetaAway n)) (hprim₁.ne_zero hn.ne')
  obtain ⟨lv⟩ := nonempty_level_of_isAlgClosed ℂ x n (Units.map (algebraMap k₁ ℂ).toMonoidHom ze) hn'
    (IsPrimitiveRoot.coe_units_iff.1 hζ)
  have hx : x.g = h := pψ.2.1.trans hg
  subst hx
  have := x.isAb.comm
  let lev : (Fin x.g ⊕ Fin x.g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ x.A) := fun a =>
    LevelCompare.homOfBasis lv (Multiplicative.ofAdd (fun j => (a j : ZMod n)))
  have ltors : ∀ a, lev a ^ n = 1 := fun a => LevelCompare.hom_pow _ _
  have ladd : ∀ a b, lev (a + b) = lev a * lev b := fun a b => by
    simp only [lev]
    rw [← map_mul, ← ofAdd_add]
    exact congrArg _ (congrArg _ (funext fun j => Int.cast_add _ _))
  obtain ⟨ρ, ρinj, hρ, ρw⟩ := exists_secHom_field hL pψ
  have es : spMap (algebraMap k₁ ℂ) ≫ spMap (IntermediateField.inclusion le₁).toRingHom = spMap (algebraMap k₀ ℂ) :=
    (spMap_comp _ _).symm
  obtain ⟨b, hb⟩ := UnifPoint.exists_pointEquiv ((pψ.1.comp p₁.1).congr es rfl)
  obtain ⟨b₁, hb₁⟩ := UnifPoint.exists_pointEquiv p₁.1
  have desc : ∀ a, ∃ t, ρ t = lev a := fun a => by
    obtain ⟨x₂, hx₂, -⟩ := tors k₁ le₁ le_rfl (b (lev a)) (by rw [← map_pow, ltors, map_one])
    refine ⟨b₁.symm x₂, b.injective (Over.OverMorphism.ext ?_)⟩
    rw [← hx₂, hb, ← Category.assoc, hρ, Category.assoc, ← hb₁, b₁.apply_symm_apply]
  choose t ht using desc
  have ttors : ∀ a, t a ^ n = 1 := fun a => ρinj (by rw [map_pow, ht, ltors, map_one])
  obtain ⟨c, e, he, pr, iP, -⟩ := exists_siegPre_of_polAV hL Moduli.cube_of_isLB (cycAway n) k₁ em x.g n (zetaAway n)
    ze y t hg (Nat.cast_ne_zero.2 hn.ne') rfl (IsPrimitiveRoot.coe_units_iff.1 hprim₁)
    (fun a a' => ρinj (by rw [map_mul, ht, ht, ht, ladd])) ttors fun a a' =>
      ρw n _ _ _ (ttors a) (ttors a') (by
        rw [ht, ht, map_zpow]
        have w := LevelCompare.pairing_of_basis lv a a'
        unfold unitOn at w ⊢
        rw [map_zpow]
        exact w)
  obtain ⟨q, hq, pb⟩ := F.rep _ _ c inferInstance (fun z => subset_closure (by
    show (z.asIdeal.comap em) = ⊥
    rw [show z.asIdeal = ⊥ from congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (α := PrimeSpectrum k₁) _ ⊥)]
    exact Ideal.comap_bot_of_injective em hem)) pr
  obtain ⟨χ, sq, -⟩ := sqOf_of_iso_of_siegPB pb hg e iP
  exact ⟨k₁, inferInstance, inferInstance, (IntermediateField.inclusion le₁).toRingHom.comp j₀, em, y, φ₁ ≫ φ₀, q, χ,
    (p₁.1.comp p₀.1).congr (spMap_comp _ _).symm rfl, hq, sq.1⟩

theorem exists_factor {n : ℕ} (hn : 0 < n) {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra (𝓞 K) R]
    [IsLocalization.Away (n : 𝓞 K) R] (i : R →+* K) (hi : Function.Injective i)
    (hc : i.comp (algebraMap (𝓞 K) R) = algebraMap (𝓞 K) K) (em : cycAway n →+* K) :
    ∃ κ : cycAway n →+* R, i.comp κ = em := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hr : ∀ a, em a ∈ i.range := by
    rintro ⟨a, ha⟩
    induction ha using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨algebraMap (𝓞 K) R ⟨em (zetaAway n), (isPrimitiveRoot_map hn.ne' em).isIntegral hn⟩,
          RingHom.congr_fun hc _⟩
      · refine ⟨IsLocalization.Away.invSelf (n : 𝓞 K), mul_left_cancel₀ hnK ?_⟩
        have h₁ := congrArg i (IsLocalization.Away.mul_invSelf (S := R) (n : 𝓞 K))
        rw [map_mul, map_natCast, map_natCast, map_one] at h₁
        rw [h₁, ← map_natCast em, ← map_mul, ← map_one em]
        exact congrArg em (Subtype.ext (by simpa using (mul_inv_cancel₀ hn').symm))
    | zero => exact ⟨0, (map_zero i).trans (map_zero em).symm⟩
    | one => exact ⟨1, (map_one i).trans (map_one em).symm⟩
    | add x y hx hy h₁ h₂ => exact (map_add em ⟨x, hx⟩ ⟨y, hy⟩) ▸ add_mem h₁ h₂
    | neg x hx h₁ => exact (map_neg em ⟨x, hx⟩) ▸ neg_mem h₁
    | mul x y hx hy h₁ h₂ => exact (map_mul em ⟨x, hx⟩ ⟨y, hy⟩) ▸ mul_mem h₁ h₂
  let e : R ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun a b h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  exact ⟨e.symm.toRingHom.comp (em.codRestrict i.range hr),
    RingHom.ext fun a => congrArg Subtype.val (e.apply_symm_apply _)⟩

theorem exists_semiAbelian_model_away : GlobalTheory.Published.SiegelToroidalIntegral → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp K)), ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (j : K →+* K'), ∀ (K'' : Type) [Field K''] [NumberField K''] (j' : K' →+* K'') (A : Over (Sp K'')) [GrpObj A] (ψ : A.left ⟶ P.A.left), IsGrpPullback A P.A (spMap (j'.comp j)) ψ → ∃ (G : Over (Sp (Localization.Away (n : 𝓞 K'')))) (_ : GrpObj G) (θ : A.left ⟶ G.left) (i : Localization.Away (n : 𝓞 K'') →+* K''), IsSemiAbelian G ∧ i.comp (algebraMap (𝓞 K'') _) = algebraMap (𝓞 K'') K'' ∧ IsGrpPullback A G (spMap i) θ := by
  intro hS n hn hodd K _ _ P
  have hn0 : 0 < n := by omega
  have hu : ∀ (L : Type) [Field L] [NumberField L], IsUnit (algebraMap (𝓞 L) L (n : 𝓞 L)) := fun L _ _ => by
    rw [map_natCast]
    exact (Nat.cast_ne_zero.2 hn0.ne').isUnit
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · refine ⟨K, inferInstance, inferInstance, RingHom.id K, fun L _ _ j' A _ ψ hA => ?_⟩
    have := isIso_of_dim_zero P hg
    have : IsIso A.hom := hA.1.isIso_snd_of_isIso
    exact ⟨𝟙_ _, inferInstance, _, IsLocalization.Away.lift (n : 𝓞 L) (hu L),
      GlobalTheory.Published.SemiAbelianHomExtension.Edge.isSemiAbelian_unit _, IsLocalization.Away.lift_comp _ _,
      isGrpPullback_unit A _⟩
  obtain ⟨_, -, hS⟩ := hS P.g hg
  obtain ⟨F, S, s, j, _, G, _, e, _, _, _, hproj, -, hjs, -, hG, -, he, -⟩ := hS n hn hodd
  obtain ⟨K', _, _, j₀, em, Q, φ, q, χ, hφ, hq, hχ⟩ := exists_siegel_point hn0 F K P rfl
  refine ⟨K', inferInstance, inferInstance, j₀, fun L _ _ j' A _ ψ hA => ?_⟩
  let R := Localization.Away (n : 𝓞 L)
  let i : R →+* L := IsLocalization.Away.lift (n : 𝓞 L) (hu L)
  have hc : i.comp (algebraMap (𝓞 L) R) = algebraMap (𝓞 L) L := IsLocalization.Away.lift_comp _ _
  have hle : Submonoid.powers (n : 𝓞 L) ≤ nonZeroDivisors (𝓞 L) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.2 hn0.ne')
  letI : Algebra R L := i.toAlgebra
  haveI : IsScalarTower (𝓞 L) R L := IsScalarTower.of_algebraMap_eq' hc.symm
  haveI : IsDomain R := IsLocalization.isDomain_localization hle
  haveI : IsDedekindDomain R := IsLocalization.isDedekindDomain (𝓞 L) hle R
  haveI : IsFractionRing R L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (n : 𝓞 L)) R L
  obtain ⟨κ, hκ⟩ := exists_factor hn0 i (IsFractionRing.injective R L) hc (j'.comp em)
  haveI : IsProper s := GlobalTheory.SchemeWords.isProper_of_isProjOver hproj
  obtain ⟨g, hg⟩ := exists_point κ s (spMap j' ≫ q ≫ j) (by
    rw [Category.assoc, Category.assoc, hjs, hq, ← spMap_comp, ← hκ])
  have hA' : IsGrpPullback A P.A (spMap j' ≫ spMap j₀) ψ := hA.congr (spMap_comp _ _) rfl
  let a : A.left ⟶ Q.A.left := hφ.1.lift ψ (A.hom ≫ spMap j') (by rw [hA'.1.w, Category.assoc])
  have ha : IsGrpPullback A Q.A (spMap j') a :=
    hφ.cancel (hA'.congr rfl (hφ.1.lift_fst _ _ _).symm) (hφ.1.lift_snd _ _ _)
  have hAG : IsGrpPullback A G (spMap i ≫ g) (a ≫ χ ≫ e) := (ha.comp (hχ.comp he)).congr hg.symm rfl
  have hG' := isGrpPullback_pullback G g
  let θ := hG'.1.lift (a ≫ χ ≫ e) (A.hom ≫ spMap i) (by rw [hAG.1.w, Category.assoc])
  exact ⟨(Over.pullback g).obj G, inferInstance, θ, i, IsSemiAbelian.pullback g G hG, hc,
    hG'.cancel (hAG.congr rfl (hG'.1.lift_fst _ _ _).symm) (hG'.1.lift_snd _ _ _)⟩

end GlobalTheory.SiegelAway
