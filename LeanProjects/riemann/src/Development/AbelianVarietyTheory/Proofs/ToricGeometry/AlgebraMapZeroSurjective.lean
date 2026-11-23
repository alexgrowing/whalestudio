import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.ProjCone

theorem isIntegral_proj {A : Type} [CommRing A] [IsDomain A] [Algebra ℂ A] (𝒜 : ℕ → Submodule ℂ A) [GradedAlgebra 𝒜]
    {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m) (hf0 : f ≠ 0) : IsIntegral (Proj 𝒜) := by
  have hred : IsReduced (Proj 𝒜) := by
    have (x : Proj 𝒜) : _root_.IsReduced ((Proj 𝒜).presheaf.stalk x) := by
      let x' : ProjectiveSpectrum 𝒜 := x
      have h1 : _root_.IsReduced (HomogeneousLocalization.AtPrime 𝒜 x'.asHomogeneousIdeal.toIdeal) :=
        isReduced_of_injective (algebraMap _ (Localization.AtPrime x'.asHomogeneousIdeal.toIdeal))
          (HomogeneousLocalization.val_injective _)
      exact isReduced_of_injective (Proj.stalkIso' 𝒜 x') (Proj.stalkIso' 𝒜 x').injective
    exact isReduced_of_isReduced_stalk _
  let η : ProjectiveSpectrum 𝒜 := ⟨⊥, Ideal.isPrime_bot, fun h => hf0 (by
    have : f ∈ HomogeneousIdeal.irrelevant 𝒜 := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hf hm.ne']
    exact h this)⟩
  have hcl : closure ({η} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 η y).1 (by
      show η.asHomogeneousIdeal ≤ y.asHomogeneousIdeal
      exact bot_le)
  have hirr : IrreducibleSpace (ProjectiveSpectrum 𝒜) := by
    have := (isIrreducible_singleton (x := η)).closure
    rw [hcl] at this
    exact (irreducibleSpace_def _).2 this
  have : IrreducibleSpace (Proj 𝒜) := hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

variable {σ : Type} (I : Ideal (MvPolynomial σ ℂ)) [GradedAlgebra (quotGrading I)]

abbrev coord (c : σ) : MvPolynomial σ ℂ ⧸ I := Ideal.Quotient.mk I (X c)

omit [GradedAlgebra (quotGrading I)] in
theorem coord_mem (c : σ) : coord I c ∈ quotGrading I 1 :=
  ⟨X c, (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X ℂ c), rfl⟩

omit [GradedAlgebra (quotGrading I)] in
theorem coord_mem_one_smul (c : σ) : coord I c ∈ quotGrading I (1 • 1) := by
  simpa using coord_mem I c

def awayRatio (c c' : σ) : HomogeneousLocalization.Away (quotGrading I) (coord I c) :=
  HomogeneousLocalization.Away.mk (quotGrading I) (coord_mem I c) 1 (coord I c') (coord_mem_one_smul I c')

def dehom (c : σ) : MvPolynomial σ ℂ →+* HomogeneousLocalization.Away (quotGrading I) (coord I c) :=
  eval₂Hom ((algebraMap (quotGrading I 0) _).comp (algebraMap ℂ (quotGrading I 0))) (awayRatio I c)

abbrev invCoord (c : σ) : Localization.Away (coord I c) := Localization.mk 1 ⟨coord I c, 1, pow_one _⟩

omit [GradedAlgebra (quotGrading I)] in
theorem mk_pow_eq_mul_invCoord (c : σ) (a : MvPolynomial σ ℂ ⧸ I) (n : ℕ)
    (h : coord I c ^ n ∈ Submonoid.powers (coord I c)) :
    (Localization.mk a ⟨coord I c ^ n, h⟩ : Localization.Away (coord I c)) =
      Localization.mk a 1 * invCoord I c ^ n := by
  rw [Localization.mk_pow, Localization.mk_mul]
  congr 1
  · simp
  · ext; simp

omit [GradedAlgebra (quotGrading I)] in
theorem mk_one_mul_invCoord (c : σ) : Localization.mk (coord I c) 1 * invCoord I c = 1 := by
  rw [Localization.mk_mul, mul_one, one_mul]
  exact Localization.mk_self (⟨coord I c, 1, pow_one _⟩ : Submonoid.powers (coord I c))

theorem val_dehom (c : σ) (f : MvPolynomial σ ℂ) :
    (dehom I c f).val = eval₂ (algebraMap ℂ (Localization.Away (coord I c)))
      (fun q => Localization.mk (coord I q) 1 * invCoord I c) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp only [dehom, coe_eval₂Hom, eval₂_C, RingHom.coe_comp, Function.comp_apply]
    rw [HomogeneousLocalization.algebraMap_eq]
    rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial σ ℂ ⧸ I)
      (Localization.Away (coord I c)), ← Localization.mk_one_eq_algebraMap]
    rfl
  | add f g hf hg =>
    simp only [map_add, HomogeneousLocalization.val_add, hf, hg, eval₂_add]
  | mul_X f q hf =>
    rw [map_mul, HomogeneousLocalization.val_mul, hf, eval₂_mul, eval₂_X]
    congr 1
    simp only [dehom, coe_eval₂Hom, eval₂_X, awayRatio, HomogeneousLocalization.Away.val_mk]
    rw [mk_pow_eq_mul_invCoord, pow_one]

theorem val_dehom_of_isHomogeneous (c : σ) {f : MvPolynomial σ ℂ} {n : ℕ} (hf : f.IsHomogeneous n) :
    (dehom I c f).val = Localization.mk (Ideal.Quotient.mk I f) 1 * invCoord I c ^ n := by
  rw [val_dehom, eval₂_mul_const_of_isHomogeneous _ _ _ hf]
  congr 1
  rw [eval₂_mk_one I _ X f, aeval_X_left_apply]

theorem dehom_surjective (c : σ) : Function.Surjective (dehom I c) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (quotGrading I) (coord_mem I c) z
  obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp ha
  have hhom : h.IsHomogeneous n := by
    simpa [smul_eq_mul, mul_one] using (mem_homogeneousSubmodule _ h).mp hh
  refine ⟨h, HomogeneousLocalization.val_injective _ ?_⟩
  rw [val_dehom_of_isHomogeneous I c hhom, HomogeneousLocalization.Away.val_mk, mk_pow_eq_mul_invCoord]
  rfl

theorem dehom_X_self (c : σ) : dehom I c (X c) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [val_dehom, eval₂_X, mk_one_mul_invCoord, HomogeneousLocalization.val_one]

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem dehom_eq_zero_of_mem (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) (c : σ) {F : MvPolynomial σ ℂ}
    (hF : F ∈ I) : dehom I c F = 0 := by
  rw [← sum_homogeneousComponent F, map_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  apply HomogeneousLocalization.val_injective
  rw [val_dehom_of_isHomogeneous I c (homogeneousComponent_isHomogeneous n F),
    Ideal.Quotient.eq_zero_iff_mem.mpr (homogeneousComponent_mem_of_mem hI hF n), Localization.mk_zero, zero_mul,
    HomogeneousLocalization.val_zero]

theorem exists_evalAway (c : σ) (p : σ → ℂ) (hp : ∀ F ∈ I, eval p F = 0) (hc : p c ≠ 0) :
    ∃ e : HomogeneousLocalization.Away (quotGrading I) (coord I c) →+* ℂ,
      ∀ F, e (dehom I c F) = eval (fun c' => p c' / p c) F := by
  let ψA : (MvPolynomial σ ℂ ⧸ I) →+* ℂ := Ideal.Quotient.lift I (eval p) hp
  have hψA : ∀ q, ψA (coord I q) = p q := fun q => by simp [ψA, coord]
  have hu : IsUnit (ψA (coord I c)) := by rw [hψA]; exact hc.isUnit
  let ψL : Localization.Away (coord I c) →+* ℂ := IsLocalization.Away.lift (coord I c) hu
  have h1 : ∀ a, ψL (Localization.mk a 1) = ψA a := fun a => by
    rw [Localization.mk_one_eq_algebraMap]
    exact IsLocalization.Away.lift_eq _ _ _
  have h2 : ψL (invCoord I c) = (p c)⁻¹ := by
    have := congrArg ψL (mk_one_mul_invCoord I c)
    rw [map_mul, h1, hψA, map_one] at this
    exact eq_inv_of_mul_eq_one_right this
  refine ⟨ψL.comp (algebraMap _ (Localization.Away (coord I c))), fun F => ?_⟩
  show ψL (dehom I c F).val = _
  rw [val_dehom, eval₂_comp_left]
  have h3 : ψL.comp (algebraMap ℂ (Localization.Away (coord I c))) = RingHom.id ℂ := by
    ext a
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply ℂ (MvPolynomial σ ℂ ⧸ I) (Localization.Away (coord I c)),
      IsLocalization.Away.lift_eq]
    show eval p (C a) = a
    simp
  rw [h3, eval₂_id]
  congr 2
  funext q
  simp only [Function.comp_apply, map_mul, h1, h2, hψA, div_eq_mul_inv]

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem ringKrullDim_away_le (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) (hP : I.IsPrime) (c : σ) (g : ℕ)
    (hg : ringKrullDim (MvPolynomial σ ℂ ⧸ I) ≤ (g + 1 : ℕ)) :
    ringKrullDim (HomogeneousLocalization.Away (quotGrading I) (coord I c)) ≤ g := by
  let φ : (MvPolynomial σ ℂ ⧸ I) →+* HomogeneousLocalization.Away (quotGrading I) (coord I c) :=
    Ideal.Quotient.lift I (dehom I c) (fun F hF => dehom_eq_zero_of_mem I hI c hF)
  have hφ : Function.Surjective φ := fun z => by
    obtain ⟨F, rfl⟩ := dehom_surjective I c z
    exact ⟨Ideal.Quotient.mk I F, rfl⟩
  have h0 : Ideal.Quotient.mk I (X c - 1) ≠ 0 := by
    intro h
    have h1 := homogeneousComponent_mem_of_mem hI (Ideal.Quotient.eq_zero_iff_mem.mp h) 0
    rw [homogeneousComponent_zero] at h1
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using h1
  have hz : φ (Ideal.Quotient.mk I (X c - 1)) = 0 := by
    show dehom I c (X c - 1) = 0
    rw [map_sub, dehom_X_self, map_one, sub_self]
  have h := (ringKrullDim_succ_le_of_surjective φ hφ (mem_nonZeroDivisors_of_ne_zero h0) hz).trans hg
  generalize ringKrullDim (HomogeneousLocalization.Away (quotGrading I) (coord I c)) = d at h
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by norm_cast)
    | coe d =>
      norm_cast at h ⊢
      omega

def toSpecC : Proj (quotGrading I) ⟶ Sp ℂ :=
  Proj.toSpecZero (quotGrading I) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)))

theorem algebraMap_zero_surjective : Function.Surjective (algebraMap ℂ (quotGrading I 0)) := by
  rintro ⟨a, h, hh, rfl⟩
  have hC := (mem_homogeneousSubmodule 0 h).mp hh
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hC
  refine ⟨coeff 0 h, Subtype.ext ?_⟩
  show algebraMap ℂ (MvPolynomial σ ℂ ⧸ I) (coeff 0 h) = Ideal.Quotient.mkₐ ℂ I h
  conv_rhs => rw [hC]
  rfl

theorem adjoin_coord_eq_top : Algebra.adjoin (quotGrading I 0) (Set.range (coord I)) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction g using MvPolynomial.induction_on with
  | C a =>
    exact Subalgebra.algebraMap_mem _ (⟨Ideal.Quotient.mk _ (C a),
      ⟨C a, (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_C _ a), rfl⟩⟩ : quotGrading I 0)
  | add g h hg hh => rw [map_add]; exact add_mem hg hh
  | mul_X g q hg => rw [map_mul]; exact mul_mem hg (Algebra.subset_adjoin ⟨q, rfl⟩)

theorem isProper_toSpecC [Fintype σ] : IsProper (toSpecC I) := by
  classical
  haveI : Algebra.FiniteType (quotGrading I 0) (MvPolynomial σ ℂ ⧸ I) :=
    ⟨⟨Finset.univ.image (coord I), by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, adjoin_coord_eq_top]⟩⟩
  haveI h2 : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)))) :=
    IsClosedImmersion.spec_of_surjective _ (algebraMap_zero_surjective I)
  exact inferInstanceAs (IsProper (Proj.toSpecZero (quotGrading I) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)))))

abbrev chart (c : σ) : (Proj (quotGrading I)).Opens := Proj.basicOpen (quotGrading I) (coord I c)

theorem iSup_chart : ⨆ c, chart I c = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (quotGrading I) (coord I) (fun p => ⟨1, coord_mem I p⟩) (adjoin_coord_eq_top I)

theorem isAffineOpen_chart (c : σ) : IsAffineOpen (chart I c) :=
  Proj.isAffineOpen_basicOpen _ _ (coord_mem I c) one_pos

def awayEquiv (c : σ) : HomogeneousLocalization.Away (quotGrading I) (coord I c) ≃+* Γ(Proj (quotGrading I), chart I c) :=
  (Proj.basicOpenIsoAway (quotGrading I) (coord I c) (coord_mem I c) one_pos).commRingCatIsoToRingEquiv

theorem awayEquiv_apply (c : σ) (a : HomogeneousLocalization.Away (quotGrading I) (coord I c)) :
    awayEquiv I c a = (Proj.awayToSection (quotGrading I) (coord I c)).hom a := rfl

def ratio (c c' : σ) : Γ(Proj (quotGrading I), chart I c) := awayEquiv I c (awayRatio I c c')

theorem awayEquiv_dehom_C (c : σ) (a : ℂ) : awayEquiv I c (dehom I c (C a)) = constFn (toSpecC I) (chart I c) a := by
  have hk := toSpecZero_appLE_basicOpen (quotGrading I) (coord_mem I c) one_pos
  have hC : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (toSpecC I).appLE ⊤ (chart I c) le_top =
      CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)) ≫
        CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (quotGrading I)
          (Submonoid.powers (coord I c))) ≫ Proj.awayToSection (quotGrading I) (coord I c) := by
    have h3 := Scheme.Hom.comp_appLE (Proj.toSpecZero (quotGrading I))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)))) ⊤
      (Proj.basicOpen (quotGrading I) (coord I c)) le_top
    show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ Scheme.Hom.appLE (Proj.toSpecZero (quotGrading I) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)))) ⊤
      (Proj.basicOpen (quotGrading I) (coord I c)) le_top = _
    have h4 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)))
    rw [h3, ← Category.assoc]
    refine (congrArg (· ≫ _) h4.symm).trans ?_
    exact (Category.assoc _ _ _).trans (congrArg (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)) ≫ ·) hk)
  have hl : awayEquiv I c (dehom I c (C a)) =
      (Proj.awayToSection (quotGrading I) (coord I c)).hom
        (HomogeneousLocalization.fromZeroRingHom (quotGrading I) (Submonoid.powers (coord I c))
          (algebraMap ℂ (quotGrading I 0) a)) := by
    rw [awayEquiv_apply]
    simp only [dehom, coe_eval₂Hom, eval₂_C, RingHom.comp_apply]
    rfl
  rw [hl]
  show _ = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (toSpecC I).appLE ⊤ (chart I c) le_top).hom a
  rw [hC]
  rfl

theorem awayEquiv_dehom (c : σ) (F : MvPolynomial σ ℂ) :
    awayEquiv I c (dehom I c F) = eval₂ (RingHom.comp ((toSpecC I).appLE ⊤ (chart I c) le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (ratio I c) F := by
  have h : (awayEquiv I c).toRingHom.comp (dehom I c) =
      eval₂Hom (RingHom.comp ((toSpecC I).appLE ⊤ (chart I c) le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (ratio I c) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coe_eval₂Hom,
        eval₂_C]
      exact awayEquiv_dehom_C I c a
    · intro q
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coe_eval₂Hom,
        eval₂_X, dehom]
      rfl
  exact RingHom.congr_fun h F

theorem basicOpen_ratio_le (c c' : σ) : (Proj (quotGrading I)).basicOpen (ratio I c c') ≤ chart I c' := by
  intro x hx
  have hxc : x ∈ chart I c := (Proj (quotGrading I)).basicOpen_le _ hx
  have h1 := (Scheme.evaluation_ne_zero_iff_mem_basicOpen _ x hxc (ratio I c c')).2 hx
  intro h2
  exact h1 ((evaluation_awayToSection_eq_zero_iff (quotGrading I) (coord I c) x hxc _).2 h2)

theorem ratio_overlap (c c' q : σ) :
    resG _ (inf_le_left : chart I c ⊓ chart I c' ≤ _) (ratio I c q) *
      resG _ (inf_le_right : chart I c ⊓ chart I c' ≤ _) (ratio I c' c) =
    resG _ (inf_le_right : chart I c ⊓ chart I c' ≤ _) (ratio I c' q) := by
  have key : ∀ (V : (Proj (quotGrading I)).Opens) (h1 : V ≤ chart I c) (h2 : V ≤ chart I c'),
      V = Proj.basicOpen (quotGrading I) (coord I c * coord I c') →
      resG _ h1 (ratio I c q) * resG _ h2 (ratio I c' c) = resG _ h2 (ratio I c' q) := by
    rintro V h1 h2 rfl
    have e1 : ∀ a, resG _ h1 ((Proj.awayToSection (quotGrading I) (coord I c)).hom a) =
        (Proj.awayToSection (quotGrading I) (coord I c * coord I c')).hom
          (HomogeneousLocalization.awayMap (quotGrading I) (coord_mem I c') rfl a) := fun a =>
      (congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection (𝒜 := quotGrading I) (f := coord I c)
        (coord_mem I c') (hx := rfl))).symm
    have e2 : ∀ a, resG _ h2 ((Proj.awayToSection (quotGrading I) (coord I c')).hom a) =
        (Proj.awayToSection (quotGrading I) (coord I c * coord I c')).hom
          (HomogeneousLocalization.awayMap (quotGrading I) (coord_mem I c) (mul_comm _ _) a) := fun a =>
      (congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection (𝒜 := quotGrading I) (f := coord I c')
        (coord_mem I c) (hx := mul_comm _ _))).symm
    simp only [ratio, awayEquiv_apply]
    rw [e1, e2, e2]
    refine (map_mul (Proj.awayToSection (quotGrading I) (coord I c * coord I c')).hom _ _).symm.trans ?_
    congr 1
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.val_mul, awayRatio, HomogeneousLocalization.awayMap_mk,
      HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_mul, OneMemClass.coe_one, pow_one, one_mul]
    ring
  exact key _ inf_le_left inf_le_right (Proj.basicOpen_mul _ _ _).symm

end GlobalTheory.ProjCone

namespace GlobalTheory

open ProjCone

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem exists_projModel {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) (hP : I.IsPrime) (hX : ∃ c, X c ∉ I) (g : ℕ)
    (hg : ringKrullDim (MvPolynomial σ ℂ ⧸ I) ≤ (g + 1 : ℕ)) :
    ∃ (Y : Over (Sp ℂ)) (D : σ → Y.left.Opens) (r : ∀ c, σ → Γ(Y.left, D c)),
      IsIntegral Y.left ∧ IsProper Y.hom ∧ (⨆ c, D c = ⊤) ∧ (∀ c, IsAffineOpen (D c)) ∧
      (∀ c, ringKrullDim Γ(Y.left, D c) ≤ g) ∧
      (∀ c (f : Γ(Y.left, D c)), ∃ F : MvPolynomial σ ℂ, f = eval₂ (RingHom.comp (Y.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (r c) F) ∧
      (∀ c, ∀ F ∈ I, eval₂ (RingHom.comp (Y.hom.appLE ⊤ (D c) le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (r c) F = 0) ∧
      (∀ c, r c c = 1) ∧
      (∀ c (p : σ → ℂ), (∀ F ∈ I, eval p F = 0) → p c ≠ 0 → ∃ e : Γ(Y.left, D c) →+* ℂ,
        (∀ a, e (constFn Y.hom (D c) a) = a) ∧ ∀ c', e (r c c') = p c' / p c) ∧
      (∀ c c', Y.left.basicOpen (r c c') ≤ D c') ∧
      (∀ c c' q, resG _ (inf_le_left : D c ⊓ D c' ≤ _) (r c q) * resG _ (inf_le_right : D c ⊓ D c' ≤ _) (r c' c) =
        resG _ (inf_le_right : D c ⊓ D c' ≤ _) (r c' q)) := by
  letI : GradedAlgebra (quotGrading I) := Classical.choice (quot_gradedAlgebra I hI)
  obtain ⟨c₀, hc₀⟩ := hX
  refine ⟨Over.mk (toSpecC I), chart I, ratio I,
    isIntegral_proj (quotGrading I) (coord_mem I c₀) one_pos (fun h => hc₀ (Ideal.Quotient.eq_zero_iff_mem.mp h)),
    isProper_toSpecC I, iSup_chart I, isAffineOpen_chart I, fun c => ?_, fun c f => ?_, fun c F hF => ?_,
    fun c => ?_, fun c p hp hc => ?_, basicOpen_ratio_le I, ratio_overlap I⟩
  · exact (ringKrullDim_eq_of_ringEquiv (awayEquiv I c)).ge.trans (ringKrullDim_away_le I hI hP c g hg)
  · obtain ⟨a, rfl⟩ := (awayEquiv I c).surjective f
    obtain ⟨F, rfl⟩ := dehom_surjective I c a
    exact ⟨F, awayEquiv_dehom I c F⟩
  · refine (awayEquiv_dehom I c F).symm.trans ?_
    rw [dehom_eq_zero_of_mem I hI c hF, map_zero]
  · have := awayEquiv_dehom I c (X c)
    rw [dehom_X_self, map_one, eval₂_X] at this
    exact this.symm
  · obtain ⟨e, he⟩ := exists_evalAway I c p hp hc
    refine ⟨e.comp (awayEquiv I c).symm.toRingHom, fun a => ?_, fun c' => ?_⟩
    · have := he (C a)
      rw [eval_C] at this
      refine Eq.trans ?_ this
      show e ((awayEquiv I c).symm (constFn (toSpecC I) (chart I c) a)) = _
      rw [← awayEquiv_dehom_C, RingEquiv.symm_apply_apply]
    · have := he (X c')
      rw [eval_X] at this
      refine Eq.trans ?_ this
      show e ((awayEquiv I c).symm (awayEquiv I c (awayRatio I c c'))) = _
      rw [RingEquiv.symm_apply_apply]
      simp only [dehom, coe_eval₂Hom, eval₂_X]

end GlobalTheory
