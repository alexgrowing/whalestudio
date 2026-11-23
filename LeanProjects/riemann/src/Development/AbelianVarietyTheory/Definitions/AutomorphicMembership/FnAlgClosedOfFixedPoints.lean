import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsometryOfConjSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitLatOfOneOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexLinearOfPureTypes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfDefinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPureTypePeriodOfSignatureSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PermutesPeriodSpacesIdOfFixesCmCurveTorsion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType
open scoped CategoryTheory.Obj
open GlobalTheory.CompRat (Curve wC wE IsSplit FixesCurve CurveOver SplitLat)

namespace GlobalTheory.ShFam.GeomComp

open GlobalTheory.AnyLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem actsBy_of_dvd {C : Curve H} {τ : ℂ ≃+* ℂ} {io : C.P.A.left ⟶ C.P.A.left} {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n)
    {s : ℤ × ℤ} (hC : C.ActsBy τ io n s) : C.ActsBy τ io m s := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨hC.1, fun a => ?_⟩
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (right_ne_zero_of_mul hn)
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (left_ne_zero_of_mul hn)
  have e : wC H (k * a.1, k * a.2) = k * wC H a := by
    simp only [wC]
    push_cast
    ring
  have := hC.2 (k * a.1, k * a.2)
  rw [e] at this
  convert this using 3
  · push_cast
    field_simp
  · push_cast
    field_simp

theorem splitLat_all (h1 : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) (D : Datum H) : SplitLat D := by
  by_cases h0 : D.p = 0 ∨ D.q = 0
  · exact GlobalTheory.CompRat.splitLat_of_definite E H D h0
  · by_cases h3 : 3 ≤ D.p + D.q
    · exact GlobalTheory.SplitGenus.splitLat_of_indefinite E H D h1 h3 (by omega) (by omega)
    · exact splitLat_of_one_one E H D h1 (by omega) (by omega)

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem congr_of_section (F : FamilyUnif Xo σ ty) (τ : ℂ ≃+* ℂ) {i i' : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)}
    {P' : (F.Di i').La →+ (Fin g → ℂ)} (hP' : IsPeriod (F.Di i') ty P')
    (hu : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P') {n : ℕ} (hn : 0 < n) (s : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G)
    {x : (F.Di i).La} {x' w : (F.Di i').La} (h1 : toUnit _ ≫ s = F.ex i P ((n : ℂ)⁻¹ • P x))
    (h2 : toUnit _ ≫ s = F.ex i' P' ((n : ℂ)⁻¹ • P' x'))
    (key : spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P x)).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' w)).left) :
    ∃ e, w = x' + n • e := by
  have hM' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have tu : ∀ y : Sp ℂ ⟶ Xo.X, (toUnit (Over.mk y) ≫ s).left = y ≫ s.left := by
    intro y
    rw [Over.comp_left]
    congr 1
  rw [← h1, tu, ← Category.assoc, hu, ← tu, h2] at key
  have e : F.ex i' P' ((n : ℂ)⁻¹ • P' x') = F.ex i' P' ((n : ℂ)⁻¹ • P' w) := Over.OverMorphism.ext key
  have e' := F.ex_add i' P' hP' ((n : ℂ)⁻¹ • P' (w - x')) ((n : ℂ)⁻¹ • P' x')
  rw [← smul_add, ← map_add, sub_add_cancel, e] at e'
  obtain ⟨y, hy⟩ := (F.ex_ker i' P' hP' _).1 (mul_eq_right.1 e'.symm)
  refine ⟨y, ?_⟩
  rw [← sub_eq_iff_eq_add']
  apply hP'.2.1
  rw [map_nsmul, hy, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hM', one_smul]

theorem conj_point_eq (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (τ : ℂ ≃+* ℂ) (hτσ : (τ : ℂ →+* ℂ).comp σ = σ) (hfix : FixesCurve H τ l.M')
    (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (hs : IsSplit hP) :
    spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P := by
  obtain ⟨C, io, hC⟩ := hfix
  have hτ : τ H.rt0 = H.rt0 := by
    rw [← hσ]
    exact RingHom.congr_fun hτσ _
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero hM.ne' l.A_pos.ne'
  obtain ⟨i', P', hP', hu⟩ := F.onto (spMap (τ : ℂ →+* ℂ) ≫ F.u i P)
    (by rw [Category.assoc, F.over_σ i P hP, GlobalTheory.ConjPermutes.spMap_comp, hτσ])
  obtain ⟨Φ, hE, hp, hm, hact⟩ := exists_isometry_of_conj_split E H D l Xo σ g ty F hD hσ hty τ hτ C io hC.1 i P hP
    i' P' hP' hs hu.symm
  obtain ⟨L, hL⟩ := GlobalTheory.CompRat.exists_complex_linear_of_pure_types E H _ _ g ty P P' hP hP' Φ hs
    (fun a ha => (hp a).2 ha) (fun a ha => (hm a).2 ha)
  have hw : wE H (1, 0) = 1 := by simp [wE]
  have key : ∀ n : ℕ, 0 < n → n ∣ l.M' → ∀ x, spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P x)).left =
      (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ x))).left := by
    intro n hn hd x
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := x)))
    have := hact n (1, 0) hn (actsBy_of_dvd hM' hd hC) a ha b hb
    rwa [hw, map_one, one_smul, one_smul] at this
  exact hu.symm.trans ((GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      E H D l Xo σ g ty hD hσ hty (F.Di i) (F.Di i')
      (F.t i) (F.t i') P P' (F.u i P) (F.u i' P') (F.ex i P) (F.ex i' P')
      ⟨F.over_σ i P hP, hP, ⟨F.ex_add i P hP, F.ex_onto i P hP, GlobalTheory.CompRat.isHolTo_ex_at_period F i P hP,
        (F.ex_diff i P hP).1, (F.ex_diff i P hP).2⟩, F.ex_ker i P hP, F.ex_lin i P hP, F.ex_weil i P hP,
        F.ex_eta i P hP, F.ex_etaA i P hP⟩
      ⟨F.over_σ i' P' hP', hP', ⟨F.ex_add i' P' hP', F.ex_onto i' P' hP', GlobalTheory.CompRat.isHolTo_ex_at_period F i' P' hP',
        (F.ex_diff i' P' hP').1, (F.ex_diff i' P' hP').2⟩, F.ex_ker i' P' hP', F.ex_lin i' P' hP',
        F.ex_weil i' P' hP', F.ex_eta i' P' hP', F.ex_etaA i' P' hP'⟩).2
      ⟨Φ, L, hE, fun v hv => congr_of_section F τ hP' hu.symm hM _ (F.ex_eta i P hP v hv) (F.ex_eta i' P' hP' v hv)
          (key _ hM (Nat.dvd_lcm_left _ _) _),
        fun v => congr_of_section F τ hP' hu.symm l.A_pos _ (F.ex_etaA i P hP v) (F.ex_etaA i' P' hP' v)
          (key _ l.A_pos (Nat.dvd_lcm_right _ _) _), hL⟩).symm

open Polynomial GlobalTheory.CompRat.FixedConst in

theorem fnAlgClosed_of_fixed_points (F : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (h1 : 1 ≤ D.p + D.q)
    (hty : IsTypeFn H D.p D.q ty) (c : Coeff l)
    (hfix : ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ∀ i, ∃ P, IsPeriod (F.Di i) ty P ∧
      spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P) : FnAlgClosed Xo c := by
  intro Z a ha
  obtain ⟨r, rfl⟩ := GlobalTheory.GeomIrr.mem_range_of_isAlgebraic_ratFun a (ha.tower_top (kap Z))
  have hr : IsIntegral c.F r := (isIntegral_algebraMap_iff (algebraMap (kap Z) (Om Z)).injective).1 ha.isIntegral
  suffices h : r ∈ (algebraMap c.F (kap Z)).range by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← hk, ← IsScalarTower.algebraMap_apply]⟩
  have hfin : FiniteDimensional ℚ c.F := c.fin
  have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
  have hk : Countable (kap Z) :=
    GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H D l Xo c).1 Z)
  obtain ⟨φ⟩ : Nonempty (kap Z →ₐ[c.F] ℂ) := GlobalTheory.nonempty_algHom_complex_of_countable c.F (kap Z)
  refine mem_range_of_fixed φ hr fun τ hτ => ?_
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := (GlobalTheory.isNormalScheme_iff _).2
    (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strK (Xo := Xo) (c := c))
      ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))
  let κ : c.F →+* Γ(Xo.XF c, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ (strK (Xo := Xo) (c := c)).appTop).hom
  let j : c.F →+* ℂ := algebraMap c.F ℂ
  have hκ : ∀ (x : Sp ℂ ⟶ Xo.XF c) (i : c.F →+* ℂ), x ≫ strK = spMap i → (ev x).comp κ = i := by
    intro x i hx
    ext k
    change ev x ((strK (Xo := Xo) (c := c)).appTop.hom _) = _
    rw [← ev_comp, hx, ev_spec]
    exact congrArg i ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv_hom_id_apply k)
  let x : Sp ℂ ⟶ Xo.XF c := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ genSp Z
  have hx : x ≫ strK = spMap j := by
    rw [Category.assoc, ← Spec.map_preimage (genSp Z ≫ strK), ← Spec.map_comp]
    congr 1
    ext k
    exact φ.commutes k
  have hev : ∀ f, ev x f = φ (((Xo.XF c).evaluation ⊤ (genPt Z) trivial).hom f) := ev_residue _ φ.toRingHom
  have hm := minpoly.monic hr
  obtain ⟨f, hf, hf0⟩ := exists_section Z (genPt Z)
    ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)) ((minpoly c.F r).map κ) (hm.map _) r (by
    apply φ.toRingHom.injective
    rw [hom_eval₂, ← (RingHom.ext hev : ev x = φ.toRingHom.comp _), eval₂_map, hκ x j hx, map_zero]
    exact (aeval_algHom_apply φ r _).trans (by rw [minpoly.aeval, map_zero]))
  have hS : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap j →
      valAt' y ⊤ f ∈ insert 0 ((minpoly c.F r).rootSet ℂ) := by
    intro y hy
    have h := congrArg (ev y) hf0
    rw [map_mul, ← eval₂_at_apply, eval₂_map, hκ y j hy, map_zero, mul_eq_zero] at h
    rw [valAt'_top]
    exact h.imp id fun h => mem_rootSet.2 ⟨hm.ne_zero, h⟩
  have hs : spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom = spMap (algebraMap (KA l) ℂ) := by
    rw [← Spec.map_comp]
    rfl
  obtain ⟨i, P, hP, hu⟩ := F.onto (x ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, hs])
  obtain ⟨P', hP', hu'⟩ := hfix τ (fun z hz => hτ ⟨z, hz⟩) i
  let x' : Sp ℂ ⟶ Xo.XF c := pullback.lift (F.u i P') (spMap j) ((F.over_σ i P' hP').trans hs.symm)
  have hx1 : x' ≫ pullback.fst _ _ = F.u i P' := pullback.lift_fst _ _ _
  have hx2 : x' ≫ pullback.snd _ _ = spMap j := pullback.lift_snd _ _ _
  have hx' : spMap (τ : ℂ →+* ℂ) ≫ x' = x' := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hx1, hu']
    · rw [Category.assoc, hx2, ← Spec.map_comp]
      congr 1
      ext k
      exact hτ k
  have key := valAt_eq_of_finite_values E H D l Xo _ g ty F h1 rfl hty c j f _ ((rootSet_finite _ _).insert 0) hS i
    P' P hP' hP x' x hx1 hx2 hu.symm hx
  rw [valAt'_top, valAt'_top, hev, hf] at key
  rw [← key]
  exact (ev_conj x' (τ : ℂ →+* ℂ) f).symm.trans (by rw [hx'])

theorem fnAlgClosed_of_curveOver (Xo : Moduli D l) (c : Coeff l) (hD : 1 ≤ D.p + D.q)
    (h1 : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) (hC : CurveOver H c.F l.M') : FnAlgClosed Xo c := by
  have hex : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
    have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
        (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩
  obtain ⟨g, ty, hty⟩ := hex
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (algebraMap (KA l) ℂ) g ty hD rfl hty
  refine fnAlgClosed_of_fixed_points F hD hty c fun τ hτ i => ?_
  obtain ⟨P, hP, hs⟩ := GlobalTheory.CompRat.exists_isSplit_of_splitLat E H (F.Di i) g ty
    (by rw [(F.sig i).1, (F.sig i).2]; exact hty) (splitLat_all h1 _)
  exact ⟨P, hP, conj_point_eq F hD rfl hty τ (RingHom.ext fun x => hτ _ (c.le x.2)) (hC τ hτ) i P hP hs⟩

end GlobalTheory.ShFam.GeomComp
