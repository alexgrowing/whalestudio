import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical

namespace GlobalTheory.WeilM

def SB (X : Type) [TopologicalSpace X] : Submodule ℂ (X → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun c f hf => ⟨hf.1.comp (fun z => c • z), hf.2.comp_left (g := fun z => c • z) (smul_zero c)⟩

theorem SB_eq (X : Type) [TopologicalSpace X] : SB X = GlobalTheory.SplitWeil.SB X := rfl

structure TestClass (R : Type) [CommRing R] where

  sp : ∀ (κ : Type) [Fintype κ], Submodule ℂ ((κ → R) → ℂ)

  adm : ∀ (κ : Type) [Fintype κ], Set (((κ → R) → ℂ) →ₗ[ℂ] ℂ)

  modu : Rˣ →* ℝ≥0

def sbClass (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] : TestClass R where
  sp κ _ := SB (κ → R)
  adm _ _ := Set.univ
  modu := distribHaarChar R

def schFun (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : Submodule ℂ (V → ℂ) :=
  Submodule.span ℂ (Set.range fun f : SchwartzMap V ℂ => (f : V → ℂ))

def realClass : TestClass ℝ where
  sp κ _ := schFun (κ → ℝ)
  adm κ _ := {l | ∃ T : SchwartzMap (κ → ℝ) ℂ →L[ℂ] ℂ, ∀ f : SchwartzMap (κ → ℝ) ℂ, l (f : (κ → ℝ) → ℂ) = T f}
  modu := distribHaarChar ℝ

def complexClass : TestClass ℂ where
  sp κ _ := schFun (κ → ℂ)
  adm κ _ := {l | ∃ T : SchwartzMap (κ → ℂ) ℂ →L[ℂ] ℂ, ∀ f : SchwartzMap (κ → ℂ) ℂ, l (f : (κ → ℂ) → ℂ) = T f}
  modu := distribHaarChar ℂ

section Unitary

variable {R : Type} [CommRing R] {κ : Type} [Fintype κ] {G : Type} [Group G]

def IsUnitaryOn [TopologicalSpace R] (C : TestClass R) (om : G →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  ∀ μ : @Measure (κ → R) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ g, ∀ φ ∈ C.sp κ, ∫⁻ x, ‖om g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

def IsContOn [TopologicalSpace G] (C : TestClass R) (om : G →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  ∀ l ∈ C.adm κ, ∀ φ ∈ C.sp κ, Continuous fun g => l (om g φ)

theorem IsUnitaryOn.comp [TopologicalSpace R] {C : TestClass R} {om : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUnitaryOn C om) {H : Type} [Group H] (f : H →* G) : IsUnitaryOn C (om.comp f) :=
  fun μ hμ g φ hφ => h μ hμ (f g) φ hφ

theorem IsContOn.comp [TopologicalSpace G] {C : TestClass R} {om : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsContOn C om) {H : Type} [Group H] [TopologicalSpace H] {f : H →* G} (hf : Continuous f) :
    IsContOn C (om.comp f) :=
  fun l hl φ hφ => (h l hl φ hφ).comp hf

theorem IsContOn.of_isLocallyConstant [TopologicalSpace G] {C : TestClass R} {om : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : ∀ φ ∈ C.sp κ, IsLocallyConstant fun g => om g φ) : IsContOn C om :=
  fun l _ φ hφ => ((h φ hφ).comp l).continuous

theorem norm_eq_one_of_lintegral_eq {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} {a : ℂ}
    (h : ∫⁻ x, ‖(a • f) x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) (h0 : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ 0)
    (h1 : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ⊤) : ‖a‖ = 1 := by
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow] at h
  rw [lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm])] at h
  have h2 : ‖a‖ₑ ^ 2 = 1 := (ENNReal.mul_left_inj h0 h1).mp (h.trans (one_mul _).symm)
  rw [enorm_eq_nnnorm, ← ENNReal.coe_pow, ENNReal.coe_eq_one, pow_eq_one_iff_of_nonneg zero_le' two_ne_zero] at h2
  exact congrArg NNReal.toReal h2

theorem IsUnitaryOn.norm_eq_one [TopologicalSpace R] {C : TestClass R} {om om' : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUnitaryOn C om) (h' : IsUnitaryOn C om') {μ : @Measure (κ → R) (borel _)}
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) {φ : (κ → R) → ℂ} (hφ : φ ∈ C.sp κ)
    (h0 : ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ ≠ 0) (h1 : ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ ≠ ⊤) {g : G} {a : ℂ} (ha : om' g φ = a • om g φ) :
    ‖a‖ = 1 := by
  have e := h μ hμ g φ hφ
  refine @norm_eq_one_of_lintegral_eq _ (borel _) μ (om g φ) a ?_ (e ▸ h0) (e ▸ h1)
  rw [← ha, e, h' μ hμ g φ hφ]

end Unitary

section Adelic

variable (F : Type) [Field F] [NumberField F]

def pureA {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    (κ → AdeleRing (𝓞 F) F) → ℂ :=
  fun x => f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * g (fun i => (x i).2)

def schA (κ : Type) [Fintype κ] : Submodule ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g}

def adeleClass [LocallyCompactSpace (AdeleRing (𝓞 F) F)] : TestClass (AdeleRing (𝓞 F) F) where
  sp κ _ := schA F κ
  adm κ _ := {l | ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
    ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f g) = T f}
  modu := distribHaarChar (AdeleRing (𝓞 F) F)

def thetaSum {κ : Type} (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : ℂ :=
  ∑' ξ : κ → F, Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))

end Adelic

section Heis

variable {R : Type} [CommRing R] [Invertible (2 : R)]

def schr (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) : (κ → R) → ℂ :=
  fun x => ψ (x ⬝ᵥ w.2 + ⅟(2 : R) * (w.1 ⬝ᵥ w.2)) * φ (x + w.1)

structure Darboux {W : Type} [AddCommGroup W] [Module R W] (B : W → W → R) (κ : Type) [Fintype κ] where

  e : W ≃ₗ[R] (κ → R) × (κ → R)
  form : ∀ w w', B w w' = (e w).1 ⬝ᵥ (e w').2 - (e w').1 ⬝ᵥ (e w).2

variable {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ]

def Darboux.rho (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) : ((κ → R) → ℂ) → ((κ → R) → ℂ) := schr ψ (d.e w)

structure IsSplitting (C : TestClass R) (ψ : AddChar R ℂ) (d : Darboux B κ) {G : Type} [Group G] (act : G → W → W)
    (om : G →* Module.End ℂ ((κ → R) → ℂ)) : Prop where
  pres : ∀ g, ∀ φ ∈ C.sp κ, om g φ ∈ C.sp κ
  impl : ∀ g w, ∀ φ ∈ C.sp κ, om g (d.rho ψ w φ) = d.rho ψ (act g w) (om g φ)
  adm : ∀ g, ∀ l ∈ C.adm κ, l ∘ₗ om g ∈ C.adm κ

structure IsUSplitting [TopologicalSpace R] (C : TestClass R) (ψ : AddChar R ℂ) (d : Darboux B κ) {G : Type} [Group G]
    [TopologicalSpace G] (act : G → W → W) (om : G →* Module.End ℂ ((κ → R) → ℂ)) : Prop
    extends IsSplitting C ψ d act om where
  unit : IsUnitaryOn C om
  cont : IsContOn C om

end Heis

section Pair

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)

def UG {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι E) : Subgroup (GL ι E) where
  carrier := {g | (g : Matrix ι ι E)ᵀ * J * (g : Matrix ι ι E).map c = J}
  one_mem' := by simp [Matrix.map_one _ (map_zero c) (map_one c)]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.transpose_mul] at *
    rw [show ((a : Matrix ι ι E) * (b : Matrix ι ι E)).map c = (a : Matrix ι ι E).map c * (b : Matrix ι ι E).map c from
      Matrix.map_mul (f := c.toRingHom)]
    calc _ = (b : Matrix ι ι E)ᵀ * ((a : Matrix ι ι E)ᵀ * J * (a : Matrix ι ι E).map c) * (b : Matrix ι ι E).map c := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : (a : Matrix ι ι E).map c * ((a⁻¹ : GL ι E) : Matrix ι ι E).map c = 1 := by
      rw [← show ((a : Matrix ι ι E) * ((a⁻¹ : GL ι E) : Matrix ι ι E)).map c =
        (a : Matrix ι ι E).map c * ((a⁻¹ : GL ι E) : Matrix ι ι E).map c from Matrix.map_mul (f := c.toRingHom),
        Units.mul_inv]
      exact Matrix.map_one _ (map_zero c) (map_one c)
    have h2 : ((a⁻¹ : GL ι E) : Matrix ι ι E)ᵀ * (a : Matrix ι ι E)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    calc _ = ((a⁻¹ : GL ι E) : Matrix ι ι E)ᵀ * ((a : Matrix ι ι E)ᵀ * J * (a : Matrix ι ι E).map c) *
            ((a⁻¹ : GL ι E) : Matrix ι ι E).map c := by rw [ha]
      _ = (((a⁻¹ : GL ι E) : Matrix ι ι E)ᵀ * (a : Matrix ι ι E)ᵀ) * J *
            ((a : Matrix ι ι E).map c * ((a⁻¹ : GL ι E) : Matrix ι ι E).map c) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

def IsHerm {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι E) : Prop := (∀ i j, c (J j i) = J i j) ∧ IsUnit J.det

structure IsQuad (ξ : E) : Prop where
  unit : IsUnit ξ
  anti : c ξ = -ξ
  basis : ∃ b : Module.Basis (Fin 2) R E, b 0 = 1 ∧ b 1 = ξ

def h90 : Eˣ →* Eˣ := MonoidHom.id Eˣ / Units.map (c : E →* E)

def normOne : Subgroup Eˣ := (MonoidHom.id Eˣ * Units.map (c : E →* E)).ker

def IsTilde (χ : Eˣ →* Circle) (u : Eˣ) (t : Circle) : Prop := ∃ z : Eˣ, (u : E) * c z = z ∧ t = χ z

def tilde (χ : Eˣ →* Circle) (hχ : ∀ z : Eˣ, c z = z → χ z = 1) : (h90 c).range →* Circle :=
  (h90 c).rangeRestrict.liftOfSurjective (h90 c).rangeRestrict_surjective ⟨χ, fun z hz => hχ z (by
    rw [MonoidHom.ker_rangeRestrict] at hz
    exact (congrArg Units.val (div_eq_one.mp hz)).symm)⟩

variable {c}

theorem mem_normOne {u : Eˣ} : u ∈ normOne c ↔ (u : E) * c u = 1 := Units.ext_iff

theorem hilbertNinetyQuotientHom_eq_iff {z u : Eˣ} : h90 c z = u ↔ (u : E) * c z = z :=
  div_eq_iff_eq_mul.trans (Units.ext_iff.trans eq_comm)

theorem tilde_norm_quotient (χ : Eˣ →* Circle) (hχ : ∀ z : Eˣ, c z = z → χ z = 1) (z : Eˣ) :
    tilde c χ hχ ⟨h90 c z, z, rfl⟩ = χ z :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z

theorem isTilde_iff (χ : Eˣ →* Circle) (hχ : ∀ z : Eˣ, c z = z → χ z = 1) (u : Eˣ) (t : Circle) :
    IsTilde c χ u t ↔ ∃ hu : u ∈ (h90 c).range, t = tilde c χ hχ ⟨u, hu⟩ := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain rfl := hilbertNinetyQuotientHom_eq_iff.mpr hz
    exact ⟨⟨z, rfl⟩, (tilde_norm_quotient χ hχ z).symm⟩
  · rintro ⟨⟨z, rfl⟩, rfl⟩
    exact ⟨z, hilbertNinetyQuotientHom_eq_iff.mp rfl, tilde_norm_quotient χ hχ z⟩

theorem IsTilde.unique {χ : Eˣ →* Circle} (hχ : ∀ z : Eˣ, c z = z → χ z = 1) {u : Eˣ} {t t' : Circle}
    (h : IsTilde c χ u t) (h' : IsTilde c χ u t') : t = t' := by
  obtain ⟨_, rfl⟩ := (isTilde_iff χ hχ u t).mp h
  obtain ⟨_, rfl⟩ := (isTilde_iff χ hχ u t').mp h'
  rfl

namespace IsQuad

variable {ξ : E} (h : IsQuad c ξ)
include h

theorem exists_eq (z : E) : ∃ a b : R, z = algebraMap R E a + algebraMap R E b * ξ := by
  obtain ⟨b, h0, h1⟩ := h.basis
  refine ⟨b.repr z 0, b.repr z 1, ?_⟩
  conv_lhs => rw [← b.sum_repr z, Fin.sum_univ_two, h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]

theorem algebraMap_injective : Function.Injective (algebraMap R E) := by
  obtain ⟨b, h0, -⟩ := h.basis
  intro x y hxy
  have : x • b 0 = y • b 0 := by rw [h0, Algebra.smul_def, Algebra.smul_def, hxy]
  simpa using congrArg (fun v => b.repr v 0) this

theorem invol (z : E) : c (c z) = z := by
  obtain ⟨a, b, rfl⟩ := h.exists_eq z
  simp [h.anti]

theorem range_h90_le_normOne : (h90 c).range ≤ normOne c := by
  rintro u ⟨z, hz⟩
  have h1 := hilbertNinetyQuotientHom_eq_iff.mp hz
  have h2 := congrArg c h1
  rw [map_mul, h.invol] at h2
  refine mem_normOne.mpr (z.isUnit.mul_right_cancel ?_)
  rw [mul_assoc, h2, h1, one_mul]

variable [Invertible (2 : R)]

theorem exists_of_fixed {z : E} (hz : c z = z) : ∃ a : R, z = algebraMap R E a := by
  obtain ⟨a, b, rfl⟩ := h.exists_eq z
  refine ⟨a, ?_⟩
  have h2 : algebraMap R E (⅟(2 : R)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap R E) 2, ← map_mul, invOf_mul_self, map_one]
  rw [map_add, map_mul, c.commutes, c.commutes, h.anti] at hz
  linear_combination (-algebraMap R E (⅟(2 : R))) * hz - algebraMap R E b * ξ * h2

theorem exists_unit_of_fixed {z : Eˣ} (hz : c z = z) : ∃ a : Rˣ, z = Units.map (algebraMap R E : R →* E) a := by
  have hz' : c (z⁻¹ : Eˣ) = (z⁻¹ : Eˣ) := by
    refine z.isUnit.mul_left_cancel ?_
    conv_lhs => rw [← hz, ← map_mul]
    rw [Units.mul_inv, map_one]
  obtain ⟨a, ha⟩ := h.exists_of_fixed hz
  obtain ⟨a', ha'⟩ := h.exists_of_fixed hz'
  have : a * a' = 1 := h.algebraMap_injective (by rw [map_mul, ← ha, ← ha', Units.mul_inv, map_one])
  exact ⟨Units.mkOfMulEqOne a a' this, Units.ext ha⟩

theorem triv_fixed {χ : Eˣ →* Circle} (hχ : ∀ a : Rˣ, χ (Units.map (algebraMap R E : R →* E) a) = 1) (z : Eˣ)
    (hz : c z = z) : χ z = 1 := by
  obtain ⟨a, rfl⟩ := h.exists_unit_of_fixed hz
  exact hχ a

theorem algebraMap_norm (z : E) : algebraMap R E (Algebra.norm R z) = z * c z := by
  obtain ⟨x, y, rfl⟩ := h.exists_eq z
  obtain ⟨d, hd⟩ := h.exists_of_fixed (z := ξ * ξ) (by rw [map_mul, h.anti, neg_mul_neg])
  obtain ⟨b, h0, h1⟩ := h.basis
  have e0 : (algebraMap R E x + algebraMap R E y * ξ) * b 0 = x • b 0 + y • b 1 := by
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def]; ring
  have e1 : (algebraMap R E x + algebraMap R E y * ξ) * b 1 = (y * d) • b 0 + x • b 1 := by
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, map_mul, ← hd]; ring
  rw [Algebra.norm_eq_matrix_det b, det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1]
  simp [h.anti, ← hd]
  ring

end IsQuad

theorem IsQuad.h90_range_eq_normOne_of_isQuad {R : Type} [Field R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
    {ξ : E} (h : IsQuad c ξ) : (h90 c).range = normOne c := by
  refine le_antisymm h.range_h90_le_normOne fun u hu => ?_
  have hu := mem_normOne.mp hu
  obtain ⟨a, b, hab⟩ := h.exists_eq u
  have hc : c u = algebraMap R E a - algebraMap R E b * ξ := by rw [hab]; simp [h.anti, sub_eq_add_neg]
  by_cases ha : 1 + a = 0
  · have ha' : 1 + algebraMap R E a = 0 := by simpa using congrArg (algebraMap R E) ha
    have hb : algebraMap R E (b * b) * (ξ * ξ) = 0 := by
      rw [hc, hab] at hu
      rw [map_mul]
      linear_combination -hu + (algebraMap R E a - 1) * ha'
    have hb0 : b = 0 := mul_self_eq_zero.mp (h.algebraMap_injective (by
      rw [(h.unit.mul h.unit).mul_left_eq_zero.mp hb, map_zero]))
    refine ⟨h.unit.unit, hilbertNinetyQuotientHom_eq_iff.mpr ?_⟩
    rw [IsUnit.unit_spec, h.anti, hab, hb0, map_zero]
    linear_combination (-ξ) * ha'
  · have hz : IsUnit ((1 + (u : E)) * (1 + c u)) := by
      have : (1 + (u : E)) * (1 + c u) = algebraMap R E (2 * (1 + a)) := by
        rw [map_mul, map_add, map_one, map_ofNat]
        linear_combination hu + hab + hc
      rw [this]
      exact (Ne.isUnit (mul_ne_zero (Invertible.ne_zero 2) ha)).map _
    refine ⟨(isUnit_of_mul_isUnit_left hz).unit, hilbertNinetyQuotientHom_eq_iff.mpr ?_⟩
    rw [IsUnit.unit_spec, map_add, map_one]
    linear_combination hu

theorem det_mem_normOne {ι : Type} [Fintype ι] [DecidableEq ι] {J : Matrix ι ι E} (hJ : IsHerm c J) (g : UG c J) :
    Matrix.GeneralLinearGroup.det (g : GL ι E) ∈ normOne c := by
  have h := congrArg Matrix.det (show ((g : GL ι E) : Matrix ι ι E)ᵀ * J * ((g : GL ι E) : Matrix ι ι E).map c = J from g.2)
  rw [det_mul, det_mul, det_transpose,
    show (((g : GL ι E) : Matrix ι ι E).map c).det = c ((g : GL ι E) : Matrix ι ι E).det from
      (c.toRingHom.map_det _).symm] at h
  refine mem_normOne.mpr (hJ.2.mul_left_cancel ?_)
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  linear_combination h

variable (c)

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

def hTens (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) : E :=
  ∑ i, ∑ j, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l)

def symp (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) : R :=
  Algebra.trace R E (ξ * hTens c JA JB x y)

def actB {JB : Matrix β β E} (h : UG c JB) (x : Matrix α β E) : Matrix α β E := x * ((h : GL β E) : Matrix β β E)ᵀ

def actAB {JA : Matrix α α E} {JB : Matrix β β E} (p : UG c JA × UG c JB) (x : Matrix α β E) : Matrix α β E :=
  ((p.1 : GL α E) : Matrix α α E) * x * ((p.2 : GL β E) : Matrix β β E)ᵀ

def dbl (JB : Matrix β β E) : Matrix (β ⊕ β) (β ⊕ β) E := Matrix.fromBlocks JB 0 0 (-JB)

def diagCols (β : Type) [DecidableEq β] : Matrix (β ⊕ β) β E := Matrix.fromRows 1 1

def IsLagr (J : Matrix β β E) {ν : Type} [Fintype ν] [DecidableEq ν] (Cy : Matrix β ν E) : Prop :=
  Cyᵀ * J * Cy.map c = 0 ∧ ∃ (Cx : Matrix β ν E) (M : Matrix (ν ⊕ ν) β E), Cxᵀ * J * Cx.map c = 0 ∧
    Matrix.fromCols Cy Cx * M = 1 ∧ M * Matrix.fromCols Cy Cx = 1

variable [Invertible (2 : R)]

theorem isLagr_diagCols (JB : Matrix β β E) : IsLagr c (dbl JB) (diagCols β : Matrix (β ⊕ β) β E) := by
  have h2 : algebraMap R E (⅟(2 : R)) + algebraMap R E (⅟(2 : R)) = 1 := by
    rw [← map_add, invOf_two_add_invOf_two, map_one]
  have h1 : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  have h1' : (-1 : Matrix β β E).map c = -1 := by rw [Matrix.map_neg _ (map_neg c), h1]
  have h3 : ∀ s : Matrix β β E, (fromRows 1 s : Matrix (β ⊕ β) β E).map c = fromRows 1 (s.map c) := fun s => by
    rw [fromRows_map, h1]
  refine ⟨?_, fromRows 1 (-1), algebraMap R E (⅟(2 : R)) • fromBlocks 1 1 1 (-1), ?_, ?_, ?_⟩
  · simp [diagCols, dbl, h3, h1, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  · simp [dbl, h3, h1', transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  · rw [diagCols, fromCols_fromRows_eq_fromBlocks, Matrix.mul_smul, fromBlocks_multiply, fromBlocks_smul, ← fromBlocks_one]
    simp [← add_smul, h2]
  · rw [diagCols, fromCols_fromRows_eq_fromBlocks, Matrix.smul_mul, fromBlocks_multiply, fromBlocks_smul, ← fromBlocks_one]
    simp [← add_smul, h2]

def SiegelRule (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (d : Darboux (symp c ξ JA JB) κ) (χ : Eˣ →* Circle) {ν : Type} [Fintype ν] [DecidableEq ν] (Cy : Matrix β ν E)
    (om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  ∀ l ∈ C.adm κ, (∀ z : Matrix α ν E, ∀ φ ∈ C.sp κ, l (d.rho ψ (z * Cyᵀ) φ) = l φ) →
    ∀ (p : UG c JB) (t : GL ν E), ((p : GL β E) : Matrix β β E) * Cy = Cy * (t : Matrix ν ν E) →
      ∀ φ ∈ C.sp κ, l (om p φ) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        (((C.modu (Units.map (Algebra.norm R : E →* R) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^
          ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) * l φ

def boxFun {κ κ' : Type} (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) : (κ ⊕ κ' → R) → ℂ :=
  fun x => φ₁ (x ∘ Sum.inl) * φ₂ (x ∘ Sum.inr)

def IsDblCoord (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ)
    (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)) : Prop :=
  ∀ w₁ w₂ : Matrix α β E, dd.e (Matrix.fromCols w₁ w₂) =
    (Sum.elim (d.e w₁).1 (d.e w₂).1, Sum.elim (d.e w₁).2 (-(d.e w₂).2))

def IsWeilB (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (d : Darboux (symp c ξ JA JB) κ) (χ : Eˣ →* Circle) (om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  IsSplitting C ψ d (actB c) om ∧
  ∃ (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)) (omd : UG c (dbl JB) →* Module.End ℂ ((κ ⊕ κ → R) → ℂ)),
    IsDblCoord c ξ JA JB d dd ∧ IsSplitting C ψ dd (actB c) omd ∧
    SiegelRule c C ψ ξ JA (dbl JB) dd χ (diagCols β) omd ∧
    ∀ (g : UG c JB) (gd : UG c (dbl JB)),
      ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 →
      ∀ φ₁ ∈ C.sp κ, ∀ φ₂ ∈ C.sp κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂

def IsWeilPair (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (d : Darboux (symp c ξ JA JB) κ) (χA χB : Eˣ →* Circle)
    (om : UG c JA × UG c JB →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  IsWeilB c C ψ ξ JA JB d χA (om.comp (MonoidHom.inr _ _)) ∧
  ∃ d' : Darboux (symp c ξ JB JA) κ, (∀ x : Matrix α β E, d'.e xᵀ = d.e x) ∧
    IsWeilB c C ψ ξ JB JA d' χB (om.comp (MonoidHom.inl _ _))

def ResEtaPow (K : Subgroup Rˣ) (χ : Eˣ →* Circle) (n : ℕ) : Prop :=
  ∀ a : Rˣ, (χ (Units.map (algebraMap R E : R →* E) a) : ℂ) =
    if a ∈ K ⊔ (Units.map (Algebra.norm R : E →* R)).range then 1 else (-1) ^ n

variable {c} in

theorem ResEtaPow.map_conj {ξ : E} (h : IsQuad c ξ) {K : Subgroup Rˣ} {χ : Eˣ →* Circle} {n : ℕ} (hχ : ResEtaPow K χ n)
    (z : Eˣ) : χ (Units.map (c : E →* E) z) = (χ z)⁻¹ := by
  have h1 := hχ (Units.map (Algebra.norm R : E →* R) z)
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨z, rfl⟩)), Circle.coe_eq_one,
    show Units.map (algebraMap R E : R →* E) (Units.map (Algebra.norm R : E →* R) z) = z * Units.map (c : E →* E) z from
      Units.ext (h.algebraMap_norm z), map_mul] at h1
  exact eq_inv_of_mul_eq_one_right h1

omit [Invertible (2 : R)] in

theorem ResEtaPow.triv_of_even {K : Subgroup Rˣ} {χ : Eˣ →* Circle} {n : ℕ} (hχ : ResEtaPow K χ n) (hn : Even n)
    (a : Rˣ) : χ (Units.map (algebraMap R E : R →* E) a) = 1 := by
  rw [← Circle.coe_eq_one, hχ a, hn.neg_one_pow, ite_self]

section Top

variable [TopologicalSpace R] [TopologicalSpace E]

def IsUWeilSplit [IsModuleTopology R E] (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E)
    (JB : Matrix β β E) {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ) (χ : Eˣ →* Circle) {ν : Type} [Fintype ν]
    [DecidableEq ν] (Cy : Matrix β ν E) (om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  IsLagr c JB Cy ∧ IsUSplitting C ψ d (actB c) om ∧ SiegelRule c C ψ ξ JA JB d χ Cy om

def IsUWeilB [IsModuleTopology R E] (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ) (χ : Eˣ →* Circle)
    (om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  IsUSplitting C ψ d (actB c) om ∧
  ∃ (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)) (omd : UG c (dbl JB) →* Module.End ℂ ((κ ⊕ κ → R) → ℂ)),
    IsDblCoord c ξ JA JB d dd ∧ IsUWeilSplit c C ψ ξ JA (dbl JB) dd χ (diagCols β) omd ∧
    ∀ (g : UG c JB) (gd : UG c (dbl JB)),
      ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 →
      ∀ φ₁ ∈ C.sp κ, ∀ φ₂ ∈ C.sp κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂

def IsUWeilPair [IsModuleTopology R E] (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E)
    (JB : Matrix β β E) {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ) (χA χB : Eˣ →* Circle)
    (om : UG c JA × UG c JB →* Module.End ℂ ((κ → R) → ℂ)) : Prop :=
  IsUWeilB c C ψ ξ JA JB d χA (om.comp (MonoidHom.inr _ _)) ∧
  (∃ d' : Darboux (symp c ξ JB JA) κ, (∀ x : Matrix α β E, d'.e xᵀ = d.e x) ∧
    IsUWeilB c C ψ ξ JB JA d' χB (om.comp (MonoidHom.inl _ _))) ∧
  IsContOn C om

variable {c} [IsModuleTopology R E] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
  {κ : Type} [Fintype κ] {d : Darboux (symp c ξ JA JB) κ}

theorem IsUWeilB.isWeilB {χ : Eˣ →* Circle} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUWeilB c C ψ ξ JA JB d χ om) : IsWeilB c C ψ ξ JA JB d χ om := by
  obtain ⟨h1, dd, omd, h2, ⟨-, h3, h4⟩, h5⟩ := h
  exact ⟨h1.toIsSplitting, dd, omd, h2, h3.toIsSplitting, h4, h5⟩

variable {χA χB : Eˣ →* Circle} {om : UG c JA × UG c JB →* Module.End ℂ ((κ → R) → ℂ)}

theorem IsUWeilPair.isWeilPair (h : IsUWeilPair c C ψ ξ JA JB d χA χB om) : IsWeilPair c C ψ ξ JA JB d χA χB om := by
  obtain ⟨h1, ⟨d', h2, h3⟩, -⟩ := h
  exact ⟨h1.isWeilB, d', h2, h3.isWeilB⟩

theorem IsUWeilPair.isUSplitting (h : IsUWeilPair c C ψ ξ JA JB d χA χB om) : IsUSplitting C ψ d (actAB c) om := by
  obtain ⟨⟨hB, -⟩, ⟨d', h2, hA, -⟩, hc⟩ := h
  have e : ∀ (p : UG c JA × UG c JB) φ, om p φ =
      om.comp (MonoidHom.inl _ _) p.1 (om.comp (MonoidHom.inr _ _) p.2 φ) := fun p φ => by
    rw [← Module.End.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]
    simp
  have r : ∀ w, d.rho ψ w = d'.rho ψ wᵀ := fun w => by rw [Darboux.rho, Darboux.rho, h2]
  refine ⟨⟨fun p φ hφ => ?_, fun p w φ hφ => ?_, fun p l hl => ?_⟩, fun μ hμ p φ hφ => ?_, hc⟩
  · rw [e]; exact hA.pres _ _ (hB.pres _ _ hφ)
  · rw [e, e, hB.impl _ _ _ hφ, r, hA.impl _ _ _ (hB.pres _ _ hφ), r]
    simp only [actB, actAB, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  · rw [show l ∘ₗ om p = (l ∘ₗ om.comp (MonoidHom.inl _ _) p.1) ∘ₗ om.comp (MonoidHom.inr _ _) p.2 from
      LinearMap.ext fun φ => congrArg l (e p φ)]
    exact hB.adm _ _ (hA.adm _ _ hl)
  · rw [e, hA.unit μ hμ _ _ (hB.pres _ _ hφ), hB.unit μ hμ _ _ hφ]

end Top

end Pair

example {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (x x₁ y : Unit → R) (φ : (Unit → R) → ℂ) :
    schr ψ (x₁, 0) φ x = φ (x + x₁) ∧ schr ψ (0, y) φ x = ψ (x () * y ()) * φ x := by
  simp [schr, dotProduct]

example (χ : ℂˣ →* Circle) : IsTilde (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) χ (Units.mk0 Complex.I Complex.I_ne_zero)
    (χ (Units.mk0 (1 + Complex.I) (by simp [Complex.ext_iff]))) :=
  ⟨_, by simp [Complex.ext_iff], rfl⟩

example (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsModuleTopology ℝ ℂ ∧ IsModuleTopology R (R × R) :=
  ⟨isModuleTopologyOfFiniteDimensional, inferInstance⟩

end GlobalTheory.WeilM

end
