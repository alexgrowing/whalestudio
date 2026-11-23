import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEisensteinCurve
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

namespace AbVarRed

section Reduction

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

def IsAbove {L : Type} [Field L] [Algebra K L] (V : Subring L) : Prop :=
  V.comap (algebraMap K L) = (algebraMap R K).range

def HasGoodReduction (A : Over (Sp K)) [GrpObj A] : Prop :=
  ∃ (G : Over (Sp R)) (_ : GrpObj G), IsAbelianScheme G ∧
    ∃ e : (Over.pullback (spMap (algebraMap R K))).obj G ≅ A, IsMonHom e.hom

def HasPotentialGoodReduction (A : Over (Sp K)) [GrpObj A] : Prop :=
  ∃ (L W : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (_ : CommRing W) (_ : IsDomain W)
    (_ : IsDiscreteValuationRing W) (_ : Algebra W L) (_ : IsFractionRing W L),
    IsAbove R K (algebraMap W L).range ∧
      HasGoodReduction W L ((Over.pullback (spMap (algebraMap K L))).obj A)

end Reduction

section Galois

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

def specAut (σ : Ω ≃ₐ[K] Ω) : ptOver K Ω ⟶ ptOver K Ω :=
  Over.homMk (spMap (σ : Ω →+* Ω)) (by
    change spMap _ ≫ spMap _ = spMap _
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp)

theorem specAut_one : specAut (1 : Ω ≃ₐ[K] Ω) = 𝟙 _ :=
  Over.OverMorphism.ext (Spec.map_id (CommRingCat.of Ω))

theorem specAut_mul (σ τ : Ω ≃ₐ[K] Ω) : specAut (σ * τ) = specAut σ ≫ specAut τ :=
  Over.OverMorphism.ext (by
    change spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp]
    rfl)

variable (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]

def galPts (σ : Ω ≃ₐ[K] Ω) : (ptOver K Ω ⟶ A) →* (ptOver K Ω ⟶ A) :=
  MonoidHom.mk' (fun x => specAut σ ≫ x) fun x y => MonObj.comp_mul _ x y

omit [IsCommMonObj A] in
theorem galPts_left (σ : Ω ≃ₐ[K] Ω) (x : ptOver K Ω ⟶ A) :
    (galPts A σ x).left = spMap (σ : Ω →+* Ω) ≫ x.left := rfl

def galTate (l : ℕ) [Fact l.Prime] : (Ω ≃ₐ[K] Ω) →* Module.End ℤ_[l] (Tate l (ptOver K Ω ⟶ A)) where
  toFun σ := Tate.map l (galPts A σ)
  map_one' := LinearMap.ext fun t => Tate.ext fun n => by
    change specAut 1 ≫ t.lev n = t.lev n
    rw [specAut_one, Category.id_comp]
  map_mul' σ τ := LinearMap.ext fun t => Tate.ext fun n => by
    change specAut (σ * τ) ≫ t.lev n = specAut σ ≫ specAut τ ≫ t.lev n
    rw [specAut_mul, Category.assoc]

theorem lev_galTate (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[K] Ω) (t : Tate l (ptOver K Ω ⟶ A)) (n : ℕ) :
    (galTate A l σ t).lev n = galPts A σ (t.lev n) := rfl

variable (K) in

def inertia (V : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[K] Ω) :=
  (V.inertiaSubgroup K).map (V.decompositionSubgroup K).subtype

def TorsionUnramified (V : ValuationSubring Ω) (m : ℕ) : Prop :=
  ∀ σ ∈ inertia K V, ∀ x : ptOver K Ω ⟶ A, x ^ m = 1 → galPts A σ x = x

def TateUnramified (V : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ σ ∈ inertia K V, galTate A l σ = 1

end Galois

def HasCMBy {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (F : Type) [Field F] [NumberField F] : Prop :=
  (∃ d : ℕ, SmoothOfRelativeDimension d A.hom ∧ Module.finrank ℚ F = 2 * d) ∧
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra O F) (_ : IsFractionRing O F), Nonempty (OAct O A)

end AbVarRed

open AbVarRed IsLocalRing

def NeronOggShafarevichSt : Prop :=
  ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
      List.TFAE [HasGoodReduction R K A,
        ∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m,
        {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite,
        ∃ (l : ℕ) (_ : Fact l.Prime), (l : ResidueField R) ≠ 0 ∧ TateUnramified A V l]

def PotentialGoodReductionSt : Prop :=
  ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 →
      (HasPotentialGoodReduction R K A ↔ (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite)

def CMPotentialGoodReductionSt : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (F : Type) [Field F] [NumberField F], HasCMBy A F → HasPotentialGoodReduction R K A

def SerreTateGoodReductionSt : Prop :=
  NeronOggShafarevichSt ∧ PotentialGoodReductionSt ∧ CMPotentialGoodReductionSt

namespace AbVarRed

theorem mem_inertia_iff {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ inertia K V ↔ σ • V = V ∧ ∀ x ∈ V, V.valuation (σ x - x) < 1 := by
  have key : ∀ τ : V.decompositionSubgroup K, τ ∈ V.inertiaSubgroup K ↔
      ∀ x ∈ V, V.valuation ((τ : Ω ≃ₐ[K] Ω) x - x) < 1 := fun τ => by
    have h : ∀ x : V, τ • residue V x = residue V x ↔ V.valuation ((τ : Ω ≃ₐ[K] Ω) x - x) < 1 := fun x => by
      rw [← ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
        ValuationSubring.valuation_lt_one_iff]
      rfl
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    constructor
    · intro e x hx
      exact (h ⟨x, hx⟩).1 (DFunLike.congr_fun e (residue V ⟨x, hx⟩))
    · intro e
      refine RingEquiv.ext fun y => ?_
      obtain ⟨x, rfl⟩ := residue_surjective y
      exact (h x).2 (e x x.2)
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ.2, (key τ).1 hτ⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨σ, h1⟩, (key _).2 h2, rfl⟩

theorem exists_isAbove (R K Ω : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] : ∃ V : ValuationSubring Ω, IsAbove R K V.toSubring := by
  obtain ⟨V, -, -, -, h⟩ := exists_valuationSubring_dominating (V := R) (algebraMap K Ω)
  exact ⟨V, Subring.ext h⟩

theorem hasGoodReduction_genericFibre (R K : Type) [CommRing R] [Field K] [Algebra R K] (G : Over (Sp R))
    [GrpObj G] (hG : IsAbelianScheme G) :
    HasGoodReduction R K ((Over.pullback (spMap (algebraMap R K))).obj G) :=
  ⟨G, inferInstance, hG, Iso.refl _, inferInstanceAs (IsMonHom (𝟙 _))⟩

theorem hasGoodReduction_baseChange_iff {K W L : Type} [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L]
    (A : Over (Sp K)) [GrpObj A] :
    HasGoodReduction W L ((Over.pullback (spMap (algebraMap K L))).obj A) ↔
      ∃ (G : Over (Sp W)) (_ : GrpObj G), IsAbelianScheme G ∧ GlobalTheory.SS.IsModel (L := L) A G := Iff.rfl

theorem HasGoodReduction.potential {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {A : Over (Sp K)} [GrpObj A] (h : HasGoodReduction R K A) :
    HasPotentialGoodReduction R K A := by
  obtain ⟨G, _, hG, e, he⟩ := h
  refine ⟨K, R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Subring.ext fun _ => Iff.rfl, G, inferInstance, hG, ?_⟩
  have hh : spMap (algebraMap K K) = 𝟙 (Sp K) := by
    rw [← Spec.map_id]
    congr 1
  obtain ⟨e', he', -⟩ := grpPullback_iso ((isGrpPullback_of_iso e).congr hh.symm rfl)
    (isGrpPullback_pullback A (spMap (algebraMap K K)))
  exact ⟨e', he'⟩

theorem tateUnramified_of_torsionUnramified {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {A : Over (Sp K)}
    [GrpObj A] [IsCommMonObj A] {V : ValuationSubring Ω} {l : ℕ} [Fact l.Prime]
    (h : ∀ n, TorsionUnramified A V (l ^ n)) : TateUnramified A V l :=
  fun σ hσ => LinearMap.ext fun t => Tate.ext fun n => h n σ hσ _ (t.lev_pow n)

end AbVarRed

section Consequences

variable {R K Ω : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] {V : ValuationSubring Ω}
  {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]

theorem NeronOggShafarevichSt.iff_tateUnramified (h : NeronOggShafarevichSt) [PerfectField (ResidueField R)]
    (hV : IsAbove R K V.toSubring) (hA : IsAbelianScheme A) (l : ℕ) [Fact l.Prime]
    (hl : (l : ResidueField R) ≠ 0) : HasGoodReduction R K A ↔ TateUnramified A V l := by
  have t := h R K Ω V hV A hA
  have t01 : HasGoodReduction R K A ↔ ∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m := t.out 0 1
  have t03 : HasGoodReduction R K A ↔
      ∃ (l : ℕ) (_ : Fact l.Prime), (l : ResidueField R) ≠ 0 ∧ TateUnramified A V l := t.out 0 3
  exact ⟨fun hg => tateUnramified_of_torsionUnramified fun n =>
    t01.1 hg (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), fun ht => t03.2 ⟨l, _, hl, ht⟩⟩

theorem SerreTateGoodReductionSt.finite_image_of_hasCMBy (h : SerreTateGoodReductionSt)
    [Finite (ResidueField R)] (hV : IsAbove R K V.toSubring) (hA : IsAbelianScheme A) {F : Type} [Field F]
    [NumberField F] (hF : HasCMBy A F) (l : ℕ) [Fact l.Prime] (hl : (l : ResidueField R) ≠ 0) :
    (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite :=
  (h.2.1 R K Ω V hV A hA l hl).1 (h.2.2 R K A hA F hF)

end Consequences

namespace AbVarRed

open GlobalTheory.CMCurve GlobalTheory.WeierstrassCurve

def gaussEquiv : (ℤ × ℤ) ≃ₗ[ℤ] GaussianInt :=
  ({ toFun := fun p => ⟨p.1, p.2⟩, invFun := fun z => (z.re, z.im), map_add' := fun _ _ => rfl,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } : (ℤ × ℤ) ≃+ GaussianInt).toIntLinearEquiv

theorem finrank_eq_of_isFractionRing (O F : Type) [CommRing O] [Field F] [CharZero F] [Algebra O F]
    [IsFractionRing O F] : Module.finrank ℚ F = Module.finrank ℤ O :=
  IsFractionRing.finrank_eq ℤ ℚ O F

theorem finrank_gaussField : Module.finrank ℚ (FractionRing GaussianInt) = 2 := by
  rw [finrank_eq_of_isFractionRing GaussianInt, ← gaussEquiv.finrank_eq]
  simp

theorem numberField_gaussField : NumberField (FractionRing GaussianInt) where
  to_finiteDimensional := Module.finite_of_finrank_pos (by rw [finrank_gaussField]; norm_num)

theorem factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

attribute [local instance] factPrimeFive

theorem exists_sq_eq_neg_one : ∃ i : ℤ_[5], i ^ 2 = -1 := by
  have h5 : ‖(5 : ℤ_[5])‖ < 1 := by
    have := PadicInt.norm_p (p := 5)
    rw [show (5 : ℤ_[5]) = ((5 : ℕ) : ℤ_[5]) by norm_num, this]
    norm_num
  have h4 : ‖(4 : ℤ_[5])‖ = 1 := by
    have h := (PadicInt.norm_natCast_eq_one_iff (p := 5) (n := 4)).2 (by norm_num)
    exact_mod_cast h
  obtain ⟨z, hz, -⟩ := hensels_lemma (p := 5) (R := ℤ) (F := Polynomial.X ^ 2 + 1) (a := 2) (by
    have e1 : Polynomial.aeval (2 : ℤ_[5]) (Polynomial.X ^ 2 + 1 : Polynomial ℤ) = 5 := by simp; norm_num
    have e2 : Polynomial.aeval (2 : ℤ_[5]) (Polynomial.derivative (Polynomial.X ^ 2 + 1 : Polynomial ℤ)) = 4 := by
      simp [map_ofNat]; norm_num
    rw [e1, e2, h4]
    simpa using h5)
  exact ⟨z, eq_neg_of_add_eq_zero_left (by simpa using hz)⟩

theorem exists_cm_curve :
    Finite (ResidueField ℤ_[5]) ∧ ((2 : ℕ) : ResidueField ℤ_[5]) ≠ 0 ∧
    (∃ V : ValuationSubring (AlgebraicClosure ℚ_[5]), IsAbove ℤ_[5] ℚ_[5] V.toSubring) ∧
    IsSepClosure ℚ_[5] (AlgebraicClosure ℚ_[5]) ∧
    ∃ (A : Over (Sp ℚ_[5])) (_ : GrpObj A) (F : Type) (_ : Field F) (_ : NumberField F),
      IsAbelianScheme A ∧ SmoothOfRelativeDimension 1 A.hom ∧ HasCMBy A F ∧
      HasGoodReduction ℤ_[5] ℚ_[5] A ∧ HasPotentialGoodReduction ℤ_[5] ℚ_[5] A := by
  have h2 : IsUnit (2 : ℤ_[5]) := by
    rw [PadicInt.isUnit_iff]
    have h := (PadicInt.norm_natCast_eq_one_iff (p := 5) (n := 2)).2 (by norm_num)
    exact_mod_cast h
  refine ⟨Finite.of_equiv _ (PadicInt.residueField (p := 5)).symm.toEquiv, ?_, exists_isAbove _ _ _,
    inferInstance, ?_⟩
  · have := (h2.map (residue ℤ_[5])).ne_zero
    rwa [map_ofNat] at this
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one
  have := isElliptic_gaussianCurve h2
  have hG := isAbelianScheme_schemeOver _ (gaussianCurve ℤ_[5]) (gaussianCurve ℤ_[5]).isUnit_Δ inferInstance
  have hd : SmoothOfRelativeDimension 1
      ((Over.pullback (spMap (algebraMap ℤ_[5] ℚ_[5]))).obj (schemeOver (gaussianCurve ℤ_[5]))).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      (smoothOfRelativeDimension_toSpec_of_isUnit _ (gaussianCurve ℤ_[5]).isUnit_Δ)
  have := numberField_gaussField
  have hg := hasGoodReduction_genericFibre ℤ_[5] ℚ_[5] _ hG
  exact ⟨_, _, FractionRing GaussianInt, inferInstance, inferInstance, isAbelianScheme_pullback_obj _ _ hG, hd,
    ⟨⟨1, hd, finrank_gaussField⟩, GaussianInt, inferInstance, inferInstance, inferInstance,
      ⟨(gaussianAct hi).pullback _⟩⟩, hg, hg.potential⟩

end AbVarRed

end GlobalTheory.Published
