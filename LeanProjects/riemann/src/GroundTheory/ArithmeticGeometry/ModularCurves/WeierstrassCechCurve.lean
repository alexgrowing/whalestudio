import Mathlib
import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassChartIso
import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassCechAlgebra
import GroundTheory.ArithmeticGeometry.ModularCurves.CechTwoOpens
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RiemannRoch
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasExtInstances

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

namespace GroundTheory.Arith.Modular

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Overlap

noncomputable abbrev varZY : HomRing W := var W 2 * var W 1

theorem varZY_mem : varZY W ∈ homGrading W 2 := SetLike.mul_mem_graded (var_mem W 2) (var_mem W 1)

noncomputable abbrev mapZ : Away (homGrading W) (var W 2) →+* Away (homGrading W) (varZY W) :=
  awayMap (homGrading W) (var_mem W 1) rfl

noncomputable abbrev mapY : Away (homGrading W) (var W 1) →+* Away (homGrading W) (varZY W) :=
  awayMap (homGrading W) (var_mem W 2) (mul_comm _ _)

theorem chartZEquiv_frac (k : Fin 3) : chartZEquiv W (frac W 2 k) = dehomZ W (X k) := by
  rw [chartZEquiv, awayEquiv_apply]
  exact awayTo_mk W (dehomZ W) (dehomZ_X_two W) (dehomZ_cubic W) 1 (X k) _

theorem chartYEquiv_frac (k : Fin 3) : chartYEquiv W (frac W 1 k) = dehomY W (X k) := by
  rw [chartYEquiv, awayEquiv_apply]
  exact awayTo_mk W (dehomY W) (dehomY_X_one W) (dehomY_cubic W) 1 (X k) _

theorem isLocalizationElem_eq :
    Away.isLocalizationElem (𝒜 := homGrading W) (var_mem W 2) (var_mem W 1) = frac W 2 1 := by
  apply HomogeneousLocalization.val_injective
  rw [val_frac, Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one, vinv,
    IsLocalization.Away.invSelf]
  simp

theorem chartZEquiv_isLocalizationElem :
    chartZEquiv W (Away.isLocalizationElem (𝒜 := homGrading W) (var_mem W 2) (var_mem W 1)) =
      yC W := by
  rw [isLocalizationElem_eq, chartZEquiv_frac]
  simp [dehomZ]

@[instance_reducible]
noncomputable def overlapAlgebra : Algebra (Away (homGrading W) (var W 2)) (Away (homGrading W) (varZY W)) :=
  (mapZ W).toAlgebra

attribute [local instance] overlapAlgebra

instance : IsLocalization.Away
    (Away.isLocalizationElem (𝒜 := homGrading W) (var_mem W 2) (var_mem W 1))
    (Away (homGrading W) (varZY W)) :=
  Away.isLocalization_mul (var_mem W 2) (var_mem W 1) rfl one_ne_zero

theorem map_powers_isLocalizationElem :
    (Submonoid.powers (Away.isLocalizationElem (𝒜 := homGrading W) (var_mem W 2)
      (var_mem W 1))).map (chartZEquiv W).toMonoidHom = Submonoid.powers (yC W) := by
  rw [Submonoid.map_powers]
  congr 1
  exact chartZEquiv_isLocalizationElem W

noncomputable def overlapEquiv : Away (homGrading W) (varZY W) ≃+* Overlap W :=
  IsLocalization.ringEquivOfRingEquiv _ _ (chartZEquiv W) (map_powers_isLocalizationElem W)

theorem overlapEquiv_mapZ (a : Away (homGrading W) (var W 2)) :
    overlapEquiv W (mapZ W a) = algebraMap _ (Overlap W) (chartZEquiv W a) :=
  IsLocalization.ringEquivOfRingEquiv_eq (map_powers_isLocalizationElem W) a

theorem mapY_frac_mul (k : Fin 3) :
    mapY W (frac W 1 k) * mapZ W (frac W 2 1) = mapZ W (frac W 2 k) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, frac, awayMap_mk, Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, pow_one]
  ring

theorem mapY_scalarAway (r : R) : mapY W (scalarAway W 1 r) = mapZ W (scalarAway W 2 r) := by
  simp only [scalarAway, RingHom.comp_apply, awayMap_fromZeroRingHom]

theorem chartYEquiv_symm_xI : (chartYEquiv W).symm (xI W) = frac W 1 0 := by
  rw [RingEquiv.symm_apply_eq, chartYEquiv_frac]
  simp [dehomY]

theorem chartYEquiv_symm_zI : (chartYEquiv W).symm (zI W) = frac W 1 2 := by
  rw [RingEquiv.symm_apply_eq, chartYEquiv_frac]
  simp [dehomY]

theorem chartYEquiv_symm_algebraMap (r : R) :
    (chartYEquiv W).symm (algebraMap R _ r) = scalarAway W 1 r := by
  rw [RingEquiv.symm_apply_eq, chartYEquiv_scalarAway]

theorem overlapEquiv_mapY_frac (k : Fin 3) :
    overlapEquiv W (mapY W (frac W 1 k)) =
      algebraMap _ (Overlap W) (dehomZ W (X k)) * yInv W := by
  have h := congrArg (overlapEquiv W) (mapY_frac_mul W k)
  rw [map_mul, overlapEquiv_mapZ, overlapEquiv_mapZ, chartZEquiv_frac, chartZEquiv_frac] at h
  have hy : dehomZ W (X 1) = yC W := by simp [dehomZ]
  rw [hy] at h
  rw [← h, mul_assoc, yC_mul_yInv, mul_one]

theorem overlapEquiv_mapY (b : Away (homGrading W) (var W 1)) :
    overlapEquiv W (mapY W b) = infToOverlap W (chartYEquiv W b) := by
  obtain ⟨t, rfl⟩ := (chartYEquiv W).symm.surjective b
  rw [RingEquiv.apply_symm_apply]
  change ((overlapEquiv W).toRingHom.comp ((mapY W).comp (chartYEquiv W).symm.toRingHom)) t =
    (infToOverlap W).toRingHom t
  congr 1
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [show AdjoinRoot.of (infPolynomial W) (Polynomial.C r) = algebraMap R (InfChart W) r from rfl,
        chartYEquiv_symm_algebraMap, mapY_scalarAway, overlapEquiv_mapZ, chartZEquiv_scalarAway,
        AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [show AdjoinRoot.of (infPolynomial W) Polynomial.X = zI W from rfl, chartYEquiv_symm_zI,
        overlapEquiv_mapY_frac, infToOverlap_zI]
      simp [dehomZ]
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [show AdjoinRoot.root (infPolynomial W) = xI W from rfl, chartYEquiv_symm_xI,
      overlapEquiv_mapY_frac, infToOverlap_xI]
    simp [dehomZ, xC]

end Overlap

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Cover

noncomputable abbrev cover : Fin 2 → (Curve W).Opens :=
  ![Proj.basicOpen (homGrading W) (var W 2), Proj.basicOpen (homGrading W) (var W 1)]

noncomputable abbrev strPresheaf : (Opens (Curve W).toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (modulesAb (structureSheafModule (Curve W))).obj

theorem inter_cover_zero : inter (cover W) ![(0 : Fin 2)] = Proj.basicOpen (homGrading W) (var W 2) := by
  simp [inter]

theorem inter_cover_one : inter (cover W) ![(1 : Fin 2)] = Proj.basicOpen (homGrading W) (var W 1) := by
  simp [inter]

theorem inter_cover_zero_one : inter (cover W) i01 = Proj.basicOpen (homGrading W) (varZY W) := by
  rw [Proj.basicOpen_mul]
  apply le_antisymm
  · exact le_inf (inter_le _ _ 0) (inter_le _ _ 1)
  · intro x hx
    rw [mem_inter_iff]
    intro a
    fin_cases a
    · exact hx.1
    · exact hx.2

noncomputable def secMap {f : HomRing W} {V : (Curve W).Opens}
    (h : V = Proj.basicOpen (homGrading W) f) : Away (homGrading W) f →+* Γ(Curve W, V) :=
  ((Curve W).presheaf.map (homOfLE h.le).op).hom.comp (Proj.awayToSection (homGrading W) f).hom

theorem secMap_bijective {f : HomRing W} {m : ℕ} (hf : f ∈ homGrading W m) (hm : 0 < m)
    {V : (Curve W).Opens} (h : V = Proj.basicOpen (homGrading W) f) :
    Function.Bijective (secMap W h) := by
  subst h
  have : IsIso (Proj.awayToSection (homGrading W) f) :=
    (Proj.basicOpenIsoAway (homGrading W) f hf hm).isIso_hom
  have e : secMap W (rfl : Proj.basicOpen (homGrading W) f = _) =
      (Proj.awayToSection (homGrading W) f).hom := by
    ext a
    simp only [secMap, RingHom.comp_apply]
    rw [show homOfLE (le_refl (Proj.basicOpen (homGrading W) f)) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  rw [e]
  exact ConcreteCategory.bijective_of_isIso _

end Cover

end Weierstrass

section TwoDiffGeneral

variable {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : Fin 2 → Opens X)

lemma comp_succAbove_zero' : i01 ∘ Fin.succAbove 0 = ![(1 : Fin 2)] := by
  funext x
  fin_cases x
  rfl

lemma comp_succAbove_one' : i01 ∘ Fin.succAbove 1 = ![(0 : Fin 2)] := by
  funext x
  fin_cases x
  rfl

lemma twoDiff_apply (τ : Cochain P U 0) :
    twoDiff P U τ =
      res P (by rw [← comp_succAbove_zero']; exact inter_le_comp U _ _) (τ ![1]) -
        res P (by rw [← comp_succAbove_one']; exact inter_le_comp U _ _) (τ ![0]) := by
  change d P U 0 τ i01 = _
  rw [d_apply, Fin.sum_univ_two,
    res_cochain_congr P U τ comp_succAbove_zero' _
      (by rw [← comp_succAbove_zero']; exact inter_le_comp U _ _),
    res_cochain_congr P U τ comp_succAbove_one' _
      (by rw [← comp_succAbove_one']; exact inter_le_comp U _ _)]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul]
  abel

end TwoDiffGeneral

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Restriction

theorem presheaf_map_map_eq {Y : Scheme.{u}} {A B C D : Y.Opens} (h1 : A ≤ B) (h2 : B ≤ C) (h3 : A ≤ D)
    (h4 : D ≤ C) (s : Γ(Y, C)) :
    Y.presheaf.map (homOfLE h1).op (Y.presheaf.map (homOfLE h2).op s) =
      Y.presheaf.map (homOfLE h3).op (Y.presheaf.map (homOfLE h4).op s) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  rfl

theorem secMap_restrict {f g x : HomRing W} {m : ℕ} (hg : g ∈ homGrading W m) (hx : x = f * g)
    {V V' : (Curve W).Opens} (hV : V = Proj.basicOpen (homGrading W) f)
    (hV' : V' = Proj.basicOpen (homGrading W) x) (hle : V' ≤ V) (a : Away (homGrading W) f) :
    (Curve W).presheaf.map (homOfLE hle).op (secMap W hV a) =
      secMap W hV' (awayMap (homGrading W) hg hx a) := by
  have h := congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection (homGrading W) hg hx)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
  simp only [secMap, RingHom.comp_apply]
  rw [h]
  exact presheaf_map_map_eq _ _ _ _ _

noncomputable def overlapSecEquiv : Γ(Curve W, inter (cover W) i01) ≃+* Overlap W :=
  (RingEquiv.ofBijective (secMap W (inter_cover_zero_one W))
    (secMap_bijective W (varZY_mem W) two_pos (inter_cover_zero_one W))).symm.trans (overlapEquiv W)

theorem overlapSecEquiv_secMap (a : Away (homGrading W) (varZY W)) :
    overlapSecEquiv W (secMap W (inter_cover_zero_one W) a) = overlapEquiv W a := by
  simp only [overlapSecEquiv, RingEquiv.trans_apply]
  congr 1
  exact (RingEquiv.ofBijective _ _).symm_apply_apply a

noncomputable def zSecEquiv : Γ(Curve W, inter (cover W) ![(0 : Fin 2)]) ≃+* W.toAffine.CoordinateRing :=
  (RingEquiv.ofBijective (secMap W (inter_cover_zero W))
    (secMap_bijective W (var_mem W 2) one_pos (inter_cover_zero W))).symm.trans (chartZEquiv W)

noncomputable def ySecEquiv : Γ(Curve W, inter (cover W) ![(1 : Fin 2)]) ≃+* InfChart W :=
  (RingEquiv.ofBijective (secMap W (inter_cover_one W))
    (secMap_bijective W (var_mem W 1) one_pos (inter_cover_one W))).symm.trans (chartYEquiv W)

theorem zSecEquiv_secMap (a : Away (homGrading W) (var W 2)) :
    zSecEquiv W (secMap W (inter_cover_zero W) a) = chartZEquiv W a := by
  simp only [zSecEquiv, RingEquiv.trans_apply]
  congr 1
  exact (RingEquiv.ofBijective _ _).symm_apply_apply a

theorem ySecEquiv_secMap (b : Away (homGrading W) (var W 1)) :
    ySecEquiv W (secMap W (inter_cover_one W) b) = chartYEquiv W b := by
  simp only [ySecEquiv, RingEquiv.trans_apply]
  congr 1
  exact (RingEquiv.ofBijective _ _).symm_apply_apply b

theorem overlapSecEquiv_twoDiff (τ : Cochain (strPresheaf W) (cover W) 0) :
    overlapSecEquiv W (twoDiff _ _ τ) =
      -cechMap W (zSecEquiv W (τ ![0]), ySecEquiv W (τ ![1])) := by
  obtain ⟨a, ha⟩ := (secMap_bijective W (var_mem W 2) one_pos (inter_cover_zero W)).2 (τ ![0])
  obtain ⟨b, hb⟩ := (secMap_bijective W (var_mem W 1) one_pos (inter_cover_one W)).2 (τ ![1])
  rw [twoDiff_apply]
  change overlapSecEquiv W (((Curve W).presheaf.map _ (τ ![1]) : Γ(Curve W, inter (cover W) i01)) -
    ((Curve W).presheaf.map _ (τ ![0]) : Γ(Curve W, inter (cover W) i01))) = _
  rw [← ha, ← hb, map_sub,
    secMap_restrict W (var_mem W 1) rfl (inter_cover_zero W) (inter_cover_zero_one W),
    secMap_restrict W (var_mem W 2) (mul_comm _ _) (inter_cover_one W) (inter_cover_zero_one W),
    overlapSecEquiv_secMap, overlapSecEquiv_secMap, zSecEquiv_secMap, ySecEquiv_secMap]
  change overlapEquiv W (mapY W b) - overlapEquiv W (mapZ W a) = _
  rw [overlapEquiv_mapZ, overlapEquiv_mapY, cechMap_apply, neg_sub]

end Restriction

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Quotient

noncomputable def overlapAddEquiv :
    (strPresheaf W).obj (op (inter (cover W) i01)) ≃+ Overlap W where
  toFun s := overlapSecEquiv W s
  invFun t := (overlapSecEquiv W).symm t
  left_inv s := (overlapSecEquiv W).symm_apply_apply s
  right_inv t := (overlapSecEquiv W).apply_symm_apply t
  map_add' s t := map_add (overlapSecEquiv W) s t

open Classical in

noncomputable def cochainOfPair (s₀ : (strPresheaf W).obj (op (inter (cover W) ![(0 : Fin 2)])))
    (s₁ : (strPresheaf W).obj (op (inter (cover W) ![(1 : Fin 2)]))) :
    Cochain (strPresheaf W) (cover W) 0 := fun i =>
  if h : i 0 = 0 then
    res (strPresheaf W) (by
      intro x hx
      rw [mem_inter_iff] at hx ⊢
      intro a
      have := hx 0
      rw [h] at this
      fin_cases a
      exact this) s₀
  else
    res (strPresheaf W) (by
      intro x hx
      rw [mem_inter_iff] at hx ⊢
      intro a
      have := hx 0
      have h1 : i 0 = 1 := by omega
      rw [h1] at this
      fin_cases a
      exact this) s₁

theorem cochainOfPair_zero (s₀ : (strPresheaf W).obj (op (inter (cover W) ![(0 : Fin 2)])))
    (s₁ : (strPresheaf W).obj (op (inter (cover W) ![(1 : Fin 2)]))) :
    cochainOfPair W s₀ s₁ ![0] = s₀ := by
  unfold cochainOfPair
  simp only [Matrix.cons_val_zero, ↓reduceDIte]
  exact res_refl _ _ _

theorem cochainOfPair_one (s₀ : (strPresheaf W).obj (op (inter (cover W) ![(0 : Fin 2)])))
    (s₁ : (strPresheaf W).obj (op (inter (cover W) ![(1 : Fin 2)]))) :
    cochainOfPair W s₀ s₁ ![1] = s₁ := by
  unfold cochainOfPair
  simp only [Matrix.cons_val_zero, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceDIte]
  exact res_refl _ _ _

theorem map_range_twoDiff :
    (twoDiff (strPresheaf W) (cover W)).range.map (overlapAddEquiv W).toAddMonoidHom =
      (LinearMap.range (cechMap W)).toAddSubgroup := by
  ext t
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup,
    LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨τ, rfl⟩, rfl⟩
    refine ⟨-(zSecEquiv W (τ ![0]), ySecEquiv W (τ ![1])), ?_⟩
    rw [map_neg]
    exact (overlapSecEquiv_twoDiff W τ).symm
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨_, ⟨cochainOfPair W ((zSecEquiv W).symm (-a)) ((ySecEquiv W).symm (-b)), rfl⟩, ?_⟩
    change overlapSecEquiv W _ = _
    rw [overlapSecEquiv_twoDiff]
    erw [cochainOfPair_zero, cochainOfPair_one]
    rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, ← map_neg]
    congr 1
    simp

noncomputable def cechOneQuotEquiv :
    cechH (strPresheaf W) (cover W) 1 ≃+ (Overlap W ⧸ LinearMap.range (cechMap W)) :=
  (cechOneEquiv _ _).trans (QuotientAddGroup.congr _ _ (overlapAddEquiv W) (map_range_twoDiff W))

end Quotient

end Weierstrass

end GroundTheory.Arith.Modular
