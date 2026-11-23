import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnivChartOfStandardSmooth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieTwo

section SlopeTestRemainingChoices

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_comp spMap_id comp_one' isTan_iff isLieComb_iff fB pushR pullR
  pushR_inj pushR_spMap pushR_pullR pushR_one fstD)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieBaseChange

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {S T : Type} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
  {v w u : Fin n → (epsR R ⟶ G)}

theorem tanExp_add (hw : ∀ i, IsTangent (w i)) (c c' : Fin n → S) :
    tanExp w (c + c') = tanExp w c * tanExp w c' := by
  rw [← lieExp_add hw _ _ _ _ (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)
    (fun _ => by rw [← TrivSqZeroExt.inr_add]; exact TrivSqZeroExt.inr_mul_inr _ _ _)]
  exact lieExp_congr _ (fun i => TrivSqZeroExt.inr_add _ _ _) _ _

omit [GrpObj G] [IsCommMonObj G] in
theorem epsTo_inr_comp (s : S) (x : epsR R ⟶ G) :
    spMap (epsTo R (inr s : DualNumber S) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ x =
      scl s (res (Algebra.ofId R S) x) := by
  rw [scl, res, ← Category.assoc, spMap_comp]
  congr 2
  refine DualNumber.algHom_ext ?_
  rw [epsTo_eps]
  ext <;> simp

theorem tanExp_eq_vecMul (hw : ∀ i, IsTangent (w i)) {M : Matrix (Fin n) (Fin n) S}
    (hM : ∀ i, res (Algebra.ofId R S) (v i) = tanExp w (M i)) (c : Fin n → S) :
    tanExp v c = tanExp w (Matrix.vecMul c M) := by
  let F : (Fin n → S) →+ Additive (sp (R₀ := R) (DualNumber S) ⟶ G) :=
    AddMonoidHom.mk' (fun c => Additive.ofMul (tanExp w c)) (fun c c' => by
      rw [← ofMul_mul, tanExp_add hw])
  rw [Matrix.vecMul_eq_sum]
  change _ = (F (∑ i, c i • M i)).toMul
  rw [map_sum, toMul_sum, tanExp, lieExp]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [epsTo_inr_comp, hM, scl_tanExp]
  change _ = tanExp w (c i • M i)
  congr 1
  funext j
  simp [mul_comm]

theorem isLieBasisOver_of_det (hw : ∀ i, IsTangent (w i)) (h : IsLieBasisOver S w)
    {M : Matrix (Fin n) (Fin n) S}
    (hM : ∀ i, res (Algebra.ofId R S) (v i) = tanExp w (M i)) (hdet : IsUnit M.det) :
    IsLieBasisOver S v := by
  rw [← Matrix.isUnit_iff_isUnit_det] at hdet
  refine ⟨fun s s' e => ?_, fun x hx => ?_⟩
  · rw [tanExp_eq_vecMul hw hM, tanExp_eq_vecMul hw hM] at e
    exact Matrix.vecMul_injective_of_isUnit hdet (h.1 _ _ e)
  · obtain ⟨d, rfl⟩ := h.2 x hx
    obtain ⟨c, hc⟩ := Matrix.vecMul_surjective_iff_isUnit.2 hdet d
    exact ⟨c, by rw [tanExp_eq_vecMul hw hM]; exact congrArg _ hc.symm⟩

theorem isLieBasisOver_of_expBij (h : ExpBij (DualNumber S) v) : IsLieBasisOver S v := by
  obtain ⟨h₁, h₂⟩ := h (RingHom.ker (fstS R S)) (ker_fst_sq (R := R) (S := S) S)
  refine ⟨fun c c' h => funext fun i => ?_, fun y hy => ?_⟩
  · exact congrArg TrivSqZeroExt.snd
      (congrFun (h₁ _ _ (fun i => (rfl : fstS R S (inr (c i)) = 0))
        (fun i => (rfl : fstS R S (inr (c' i)) = 0)) _ _ h) i)
  · obtain ⟨c, hc, hcJ, e⟩ := h₂ y (mem_redKer_of_section _ (inlS R S) (fun _ => rfl) hy)
    have hc' : ∀ i, c i = inr (c i).snd := fun i =>
      have h0 : (c i).fst = 0 := hcJ i
      TrivSqZeroExt.ext h0 rfl
    exact ⟨fun i => (c i).snd, e.trans (lieExp_congr v hc' _ _)⟩

theorem isLieBasis_bcVec_iff (hv : ∀ i, IsTangent (v i)) :
    IsLieBasis (bcVec S v) ↔ IsLieBasisOver S v := by
  refine ⟨fun h => ⟨fun s s' e => ?_, fun x hx => ?_⟩, fun h => isLieBasis_bcVec_of hv h.1
    fun y hy => h.2 y (comp_eq_one_of_mem_redKer hy _ fun a ha => ha)⟩
  · refine (isLieBasisOver_self h).1 s s' (pushR_inj G ?_)
    rw [tanExp, tanExp, ← prodPts_eq_lieExp, ← prodPts_eq_lieExp, pushR_prodPts, pushR_prodPts]
    exact e
  · obtain ⟨c, hc, -⟩ := h.2 (pullR (R' := S) G x) ((isTan_iff _).1 ((isTan_iff_mem G _).2 (by
      rw [pushR_pullR]
      exact mem_redKer_of_section _ (inlS R S) (fun _ => rfl) hx)))
    refine ⟨c, ?_⟩
    rw [tanExp, ← pushR_prodPts, ← (isLieComb_iff _ _ _).1 hc, pushR_pullR]

variable [Smooth G.hom]

theorem expBij_of_isLieBasisOver (hv : ∀ i, IsTangent (v i)) (h : IsLieBasisOver S v)
    (α : S →ₐ[R] T) : ExpBij T v := by
  refine expBij_of_span (s := α '' {g : S | UnitInChart G (Localization.Away g)}) ?_ ?_
  · rw [← Ideal.map_span, span_unitInChart, Ideal.map_top]
  · rintro _ ⟨g, hg, rfl⟩ T' _ _ φ hφ
    have hρ := isAway_awayHom (R := R) g
    obtain ⟨β, -⟩ := hρ.lift (φ.comp α) hφ
    exact expBij_of_unitInChart hv hg (h.away hv hρ) β

theorem expBij_of_isUnit (hv : ∀ i, IsTangent (v i)) {a : R}
    (h : IsLieBasisOver (Localization.Away a) v) (ha : IsUnit (algebraMap R T a)) : ExpBij T v := by
  obtain ⟨α, -⟩ := (isAway_awayHom (R := R) a).lift (Algebra.ofId R T) ha
  exact expBij_of_isLieBasisOver hv h α

theorem exists_global {a : R} {e : Fin n → (epsR (Localization.Away a) ⟶
      (Over.pullback (fB R (Localization.Away a))).obj G)} (he : IsLieBasis e) :
    ∃ w : Fin n → (epsR R ⟶ G), (∀ i, IsTangent (w i)) ∧
      IsLieBasisOver (Localization.Away a) w := by
  have hρ := isAway_awayHom (R := R) a
  choose N w hw hres using fun i => exists_res_eq hρ (w' := pushR G (e i))
    (comp_eq_one_of_mem_redKer ((isTan_iff_mem G _).1 ((isTan_iff _).2 (he.1 i))) _ fun a ha => ha)
  have hw' : ∀ i, IsTangent (G := G) (w i) := fun i => (isTan_iff _).1 (hw i)
  refine ⟨w, hw', (isLieBasis_bcVec_iff hw').1 ?_⟩
  have key := (LieComb.isLieBasis_iff_isUnit_det he
    (Matrix.diagonal fun i => awayHom R a a ^ N i)).2 (by
      rw [Matrix.det_diagonal]
      exact IsUnit.prod_univ_iff.2 fun i => hρ.unit.pow _)
  convert key using 2 with i
  have e₁ : (Matrix.diagonal fun i => awayHom R a a ^ N i) i = fun j =>
      (Pi.single i (1 : Localization.Away a) : Fin n → Localization.Away a) j * awayHom R a a ^ N i := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Matrix.diagonal_apply_ne' _ hj, Pi.single_eq_of_ne hj]
  rw [e₁, ← scl_tanExp, LieComb.tanExp_single he.1]
  refine pushR_inj G ?_
  rw [pushR_bcVec, scl, pushR_spMap]
  refine Eq.trans ?_ ((hres i).trans ?_)
  · congr 2
    refine DualNumber.algHom_ext ?_
    ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapA, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  · congr 2

theorem exists_away_comb (hw : ∀ i, IsTangent (w i)) (hu : ∀ i, IsTangent (u i)) {a b : R}
    (p : PrimeSpectrum R) (ha : a ∉ p.asIdeal) (hb : b ∈ p.asIdeal)
    (h : IsLieBasisOver (Localization.Away a) w)
    (hv : ∀ i, v i = scl (R := R) a (w i) * scl (R := R) b (u i)) :
    ∃ c ∉ p.asIdeal, IsLieBasisOver (Localization.Away c) v := by
  have hρ := isAway_awayHom (R := R) a
  choose M hM using fun i => h.2 (res (Algebra.ofId R (Localization.Away a)) (u i))
    (IsTanOver.res ((isTan_iff _).2 (hu i)) _)
  let A : Matrix (Fin n) (Fin n) (Localization.Away a) :=
    algebraMap R (Localization.Away a) a • (1 : Matrix (Fin n) (Fin n) (Localization.Away a)) +
      algebraMap R (Localization.Away a) b • Matrix.of M
  have hA : ∀ i, res (Algebra.ofId R (Localization.Away a)) (v i) = tanExp w (A i) := by
    intro i
    have e₁ : res (Algebra.ofId R (Localization.Away a)) (w i) = tanExp w (Pi.single i 1) := by
      conv_lhs => rw [← LieComb.tanExp_single hw i, res_tanExp]
      congr 1
      funext j
      by_cases hj : j = i <;> simp [hj]
    rw [hv, res, MonObj.comp_mul]
    change res (Algebra.ofId R (Localization.Away a)) (scl (R := R) (S := R) (G := G) a (w i)) *
      res (Algebra.ofId R (Localization.Away a)) (scl (R := R) (S := R) (G := G) b (u i)) =
        tanExp w (A i)
    rw [res_scl, res_scl, e₁, hM, scl_tanExp, scl_tanExp, ← tanExp_add hw]
    congr 1
    funext j
    simp [-algebraMap_smul, A, Matrix.one_apply, Pi.single_apply, mul_comm, eq_comm]
  obtain ⟨N, d, hd⟩ := hρ.surj A.det
  have hdp : d ∉ p.asIdeal := by
    have ha' : algebraMap R p.asIdeal.ResidueField a ≠ 0 := by
      rwa [Ne, Ideal.algebraMap_residueField_eq_zero]
    have hb' : algebraMap R p.asIdeal.ResidueField b = 0 := by
      rwa [Ideal.algebraMap_residueField_eq_zero]
    obtain ⟨φ, -⟩ := hρ.lift (Algebra.ofId R p.asIdeal.ResidueField) ha'.isUnit
    have e₁ : φ.mapMatrix A = algebraMap R p.asIdeal.ResidueField a • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [-algebraMap_smul, A, hb', Matrix.one_apply, hij]
    have e₂ := congrArg φ hd
    rw [map_mul, AlgHom.map_det, e₁, Matrix.det_smul, Matrix.det_one, mul_one, map_pow] at e₂
    simp only [IsScalarTower.coe_toAlgHom', AlgHom.commutes] at e₂
    rw [← Ideal.algebraMap_residueField_eq_zero, ← e₂]
    exact mul_ne_zero (pow_ne_zero _ ha') (pow_ne_zero _ ha')
  refine ⟨a * d, fun hc => (p.isPrime.mem_or_mem hc).elim ha hdp, ?_⟩
  have hc := (isAway_awayHom (R := R) (a * d)).unit
  rw [map_mul] at hc
  obtain ⟨α, -⟩ := hρ.lift (awayHom R (a * d)) (isUnit_of_mul_isUnit_left hc)
  refine isLieBasisOver_of_det hw (isLieBasisOver_of_expBij
    (expBij_of_isLieBasisOver hw h ((inlS R _).comp α))) (M := α.mapMatrix A) (fun i => ?_) ?_
  · rw [Subsingleton.elim (Algebra.ofId R (Localization.Away (a * d)))
      (α.comp (Algebra.ofId R (Localization.Away a))), ← res_res, hA, res_tanExp]
    rfl
  · rw [← AlgHom.map_det]
    have e₂ := congrArg α hd
    rw [map_mul] at e₂
    refine isUnit_of_mul_isUnit_left (y := α (awayHom R a a ^ N)) ?_
    rw [e₂]
    simpa only [IsScalarTower.coe_toAlgHom', AlgHom.commutes] using isUnit_of_mul_isUnit_right hc

theorem exists_away_two (hv : ∀ i, IsTangent (v i)) (p q : PrimeSpectrum R) {a b : R}
    (ha : a ∉ p.asIdeal) (hb : b ∉ q.asIdeal) (h₁ : IsLieBasisOver (Localization.Away a) v)
    (h₂ : IsLieBasisOver (Localization.Away b) v) :
    ∃ r, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ IsLieBasisOver (Localization.Away r) v := by
  by_cases haq : a ∈ q.asIdeal
  swap
  · exact ⟨a, ha, haq, h₁⟩
  by_cases hbp : b ∈ p.asIdeal
  swap
  · exact ⟨b, hbp, hb, h₂⟩
  refine ⟨a + b, fun h => ha ((Ideal.add_mem_iff_left _ hbp).1 h),
    fun h => hb ((Ideal.add_mem_iff_right _ haq).1 h), isLieBasisOver_of_expBij ?_⟩
  refine expBij_of_span (s := {algebraMap R _ a, algebraMap R _ b}) ?_ ?_
  · refine Ideal.eq_top_of_isUnit_mem _ (x := algebraMap R _ (a + b)) ?_ ?_
    · rw [map_add]
      exact add_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
    · have := ((isAway_awayHom (R := R) (a + b)).unit).map (inlS R (Localization.Away (a + b)))
      simpa only [IsScalarTower.coe_toAlgHom', AlgHom.commutes] using this
  · rintro _ (rfl | rfl) T _ _ φ hφ <;> rw [AlgHom.commutes] at hφ
    · exact expBij_of_isUnit hv h₁ hφ
    · exact expBij_of_isUnit hv h₂ hφ

theorem exists_global_two (hw : ∀ i, IsTangent (w i)) (hu : ∀ i, IsTangent (u i))
    (p q : PrimeSpectrum R) {a b : R} (ha : a ∉ p.asIdeal) (hb : b ∉ q.asIdeal)
    (h₁ : IsLieBasisOver (Localization.Away a) w) (h₂ : IsLieBasisOver (Localization.Away b) u) :
    ∃ r, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∃ v : Fin n → (epsR R ⟶ G), (∀ i, IsTangent (v i)) ∧
      IsLieBasisOver (Localization.Away r) v := by
  by_cases haq : a ∈ q.asIdeal
  swap
  · exact ⟨a, ha, haq, w, hw, h₁⟩
  by_cases hbp : b ∈ p.asIdeal
  swap
  · exact ⟨b, hbp, hb, u, hu, h₂⟩
  let v : Fin n → (epsR R ⟶ G) := fun i => scl (R := R) a (w i) * scl (R := R) b (u i)
  have hv : ∀ i, IsTangent (v i) := fun i => (isTan_iff _).1 (by
    change IsTanOver (R := R) (S := R) (v i)
    rw [IsTanOver, MonObj.comp_mul, IsTanOver.scl ((isTan_iff _).2 (hw i)) a,
      IsTanOver.scl ((isTan_iff _).2 (hu i)) b, mul_one])
  obtain ⟨c, hc, h₃⟩ := exists_away_comb (v := v) hw hu p ha hbp h₁ fun _ => rfl
  obtain ⟨d, hd, h₄⟩ := exists_away_comb (v := v) hu hw q hb haq h₂ fun _ => mul_comm _ _
  obtain ⟨r, h₅, h₆, h₇⟩ := exists_away_two hv p q hc hd h₃ h₄
  exact ⟨r, h₅, h₆, v, hv, h₇⟩

end SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem lie_free_near_two_primes :
    ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ),
      SmoothOfRelativeDimension n G.hom → ∀ p q : PrimeSpectrum R,
        ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∃ v : Fin n → (epsR (Localization.Away r) ⟶
          (Over.pullback (spMap (algebraMap R (Localization.Away r)))).obj G), IsLieBasis v := by
  intro R _ G _ _ n h p q
  have : Smooth G.hom := SmoothOfRelativeDimension.smooth n G.hom
  obtain ⟨a, ha, e, he⟩ := LieLoc.lie_locally_free R G n h p
  obtain ⟨b, hb, f, hf⟩ := LieLoc.lie_locally_free R G n h q
  obtain ⟨w, hw, h₁⟩ := exists_global he
  obtain ⟨u, hu, h₂⟩ := exists_global hf
  obtain ⟨r, h₃, h₄, v, hv, h₅⟩ := exists_global_two hw hu p q ha hb h₁ h₂
  exact ⟨r, h₃, h₄, _, (isLieBasis_bcVec_iff hv).2 h₅⟩

end GlobalTheory.LieTwo
