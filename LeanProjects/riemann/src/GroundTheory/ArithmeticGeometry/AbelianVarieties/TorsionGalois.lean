import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.Torsion
import GroundTheory.ProfiniteCohomology.GaloisModules.Discrete
import GroundTheory.ProfiniteCohomology.GaloisModules.FixedField

namespace GroundTheory.Arith.Abelian

open GroundTheory.ProfCoh IntermediateField AddSubgroup WeierstrassCurve

universe w u

section Action

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)

noncomputable def galPointsHom : Gal(L/K) →* AddMonoid.End (W.baseChange L).toAffine.Point where
  toFun σ := Affine.Point.map (W' := W.toAffine) (σ : L →ₐ[K] L)
  map_one' := by
    refine AddMonoidHom.ext fun P => ?_
    cases P <;> rfl
  map_mul' σ τ := by
    refine AddMonoidHom.ext fun P => ?_
    cases P <;> rfl

@[simp]
theorem galPointsHom_zero (σ : Gal(L/K)) : galPointsHom K L W σ 0 = 0 :=
  rfl

theorem galPointsHom_some (σ : Gal(L/K)) {x y : L}
    (h : (W.baseChange L).toAffine.Nonsingular x y) :
    ∃ h' : (W.baseChange L).toAffine.Nonsingular (σ x) (σ y),
      galPointsHom K L W σ (.some x y h) = .some (σ x) (σ y) h' :=
  ⟨_, rfl⟩

theorem galPointsHom_some_eq_self {σ : Gal(L/K)} {x y : L}
    (h : (W.baseChange L).toAffine.Nonsingular x y) (hx : σ x = x) (hy : σ y = y) :
    galPointsHom K L W σ (.some x y h) = .some x y h := by
  obtain ⟨h', e⟩ := galPointsHom_some K L W σ h
  rw [e]
  simp only [Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

noncomputable def galTorsionHom (n : ℕ) :
    Gal(L/K) →* AddMonoid.End (torsionBy (W.baseChange L).toAffine.Point n) where
  toFun σ :=
    { toFun := fun P => ⟨galPointsHom K L W σ P, by
        rw [torsionBy.nsmul_iff, ← map_nsmul, torsionBy.nsmul_iff.mp P.2, map_zero]⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun P Q => Subtype.ext (map_add _ _ _) }
  map_one' := by
    refine AddMonoidHom.ext fun P => Subtype.ext ?_
    show galPointsHom K L W 1 P = P
    rw [map_one]
    rfl
  map_mul' σ τ := by
    refine AddMonoidHom.ext fun P => Subtype.ext ?_
    show galPointsHom K L W (σ * τ) P = galPointsHom K L W σ (galPointsHom K L W τ P)
    rw [map_mul]
    rfl

@[simp]
theorem coe_galTorsionHom_apply (n : ℕ) (σ : Gal(L/K))
    (P : torsionBy (W.baseChange L).toAffine.Point n) :
    ((galTorsionHom K L W n σ P : torsionBy (W.baseChange L).toAffine.Point n) :
      (W.baseChange L).toAffine.Point) = galPointsHom K L W σ P :=
  rfl

noncomputable abbrev galPoints : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRep.{w} (galPointsHom K L W))

noncomputable abbrev galPointsZ : Rep.{u} ℤ Gal(L/K) :=
  Rep.of ((addMonoidEndRingEquivInt (W.baseChange L).toAffine.Point).toRingHom.toMonoidHom.comp
    (galPointsHom K L W))

noncomputable abbrev galTorsion (n : ℕ) : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRep.{w} (galTorsionHom K L W n))

noncomputable abbrev galTorsionZ (n : ℕ) : Rep.{u} ℤ Gal(L/K) :=
  Rep.of ((addMonoidEndRingEquivInt
    (torsionBy (W.baseChange L).toAffine.Point n)).toRingHom.toMonoidHom.comp
    (galTorsionHom K L W n))

theorem galPoints_ρ_apply (σ : Gal(L/K)) (P : (W.baseChange L).toAffine.Point) :
    (galPoints.{w} K L W).ρ σ P = galPointsHom K L W σ P :=
  rfl

theorem galPointsZ_ρ_apply (σ : Gal(L/K)) (P : (W.baseChange L).toAffine.Point) :
    (galPointsZ K L W).ρ σ P = galPointsHom K L W σ P :=
  rfl

theorem galTorsion_ρ_apply (n : ℕ) (σ : Gal(L/K)) (P : torsionBy (W.baseChange L).toAffine.Point n) :
    (galTorsion.{w} K L W n).ρ σ P = galTorsionHom K L W n σ P :=
  rfl

theorem galTorsionZ_ρ_apply (n : ℕ) (σ : Gal(L/K))
    (P : torsionBy (W.baseChange L).toAffine.Point n) :
    (galTorsionZ K L W n).ρ σ P = galTorsionHom K L W n σ P :=
  rfl

end Action

section Discrete

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)

theorem isOpen_of_forall_apply_eq_apply_eq_mem [Algebra.IsIntegral K L] (H : Subgroup Gal(L/K))
    (x y : L) (h : ∀ σ : Gal(L/K), σ x = x → σ y = y → σ ∈ H) : IsOpen (H : Set Gal(L/K)) := by
  have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have : FiniteDimensional K K⟮y⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  refine Subgroup.isOpen_mono (H₁ := (K⟮x⟯).fixingSubgroup ⊓ (K⟮y⟯).fixingSubgroup)
    (fun σ hσ => h σ (apply_eq_of_mem_fixingSubgroup_adjoin hσ.1)
      (apply_eq_of_mem_fixingSubgroup_adjoin hσ.2)) ?_
  rw [Subgroup.coe_inf]
  exact (fixingSubgroup_isOpen _).inter (fixingSubgroup_isOpen _)

theorem isOpen_stabilizer_point [Algebra.IsIntegral K L] (H : Subgroup Gal(L/K))
    (P : (W.baseChange L).toAffine.Point) (h : ∀ σ, galPointsHom K L W σ P = P → σ ∈ H) :
    IsOpen (H : Set Gal(L/K)) := by
  rcases P with _ | ⟨x, y, hP⟩
  · have : H = ⊤ := eq_top_iff.mpr fun σ _ => h σ rfl
    rw [this]
    exact isOpen_univ
  · exact isOpen_of_forall_apply_eq_apply_eq_mem H x y fun σ hx hy =>
      h σ (galPointsHom_some_eq_self K L W hP hx hy)

variable [Algebra.IsIntegral K L]

instance isDiscreteRep_galPoints : IsDiscreteRep (galPoints.{w} K L W) :=
  ⟨fun P => isOpen_stabilizer_point W _ P fun _ h => h⟩

instance isDiscreteRep_galPointsZ : IsDiscreteRep (galPointsZ K L W) :=
  ⟨fun P => isOpen_stabilizer_point W _ P fun _ h => h⟩

instance isDiscreteRep_galTorsion (n : ℕ) : IsDiscreteRep (galTorsion.{w} K L W n) :=
  ⟨fun P => isOpen_stabilizer_point W _ (P : (W.baseChange L).toAffine.Point) fun _ h =>
    Subtype.ext h⟩

instance isDiscreteRep_galTorsionZ (n : ℕ) : IsDiscreteRep (galTorsionZ K L W n) :=
  ⟨fun P => isOpen_stabilizer_point W _ (P : (W.baseChange L).toAffine.Point) fun _ h =>
    Subtype.ext h⟩

end Discrete

section SepClosed

instance isElliptic_baseChange {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) [W.IsElliptic] : (W.baseChange A).IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DecidableEq L] [IsSepClosed L]
  (W : WeierstrassCurve K) [W.IsElliptic]

end SepClosed

end GroundTheory.Arith.Abelian
