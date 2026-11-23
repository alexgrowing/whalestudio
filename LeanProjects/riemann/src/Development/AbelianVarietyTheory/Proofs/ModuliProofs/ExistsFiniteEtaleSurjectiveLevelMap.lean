import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.LevelMap

theorem of_baseChange (P : MorphismProperty Scheme.{0})
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    {X₀ X₁ S₀ S₁ T : Scheme.{0}} (s₀ : X₀ ⟶ S₀) (s₁ : X₁ ⟶ S₁) (k : S₁ ⟶ S₀) (r : X₁ ⟶ X₀)
    (hr : r ≫ s₀ = s₁ ≫ k) (i₀ : T ⟶ S₀) (i₁ : T ⟶ S₁) (hi : i₁ ≫ k = i₀)
    [Surjective i₁] [Flat i₁] [QuasiCompact i₁]
    (rF : pullback s₁ i₁ ⟶ pullback s₀ i₀) (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r)
    (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _) (h : P rF) : P (pullback.lift r s₁ hr) := by
  subst hi
  let p : pullback s₀ (i₁ ≫ k) ⟶ pullback s₀ k :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i₁) (by simp [pullback.condition])
  have hp : IsPullback p (pullback.snd _ _) (pullback.snd s₀ k) i₁ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback s₀ k)
    have : p ≫ pullback.fst s₀ k = pullback.fst _ _ := pullback.lift_fst _ _ _
    rw [this]
    exact IsPullback.of_hasPullback _ _
  have hq : IsPullback (pullback.fst s₁ i₁) rF (pullback.lift r s₁ hr) p := by
    refine IsPullback.of_bot ?_ ?_ hp
    · rw [h₂, pullback.lift_snd]
      exact IsPullback.of_hasPullback _ _
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, h₁]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, reassoc_of% h₂, pullback.condition]
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := P)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hq.flip ⟨⟨?_, ?_⟩, ?_⟩ h
  · exact MorphismProperty.of_isPullback (P := @Surjective) hp.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hp.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip ‹_›

theorem isFinite_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsFinite : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := isAffineHom_descendsAlong_fpqc.{0}
  refine ⟨fun {A X Y Z fst snd f g} H hf hfst => ?_⟩
  have a2 : IsAffineHom g := MorphismProperty.of_isPullback_of_descendsAlong (P := @IsAffineHom) H hf inferInstance
  have a3 : UniversallyClosed g :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H hf inferInstance
  have a4 : LocallyOfFiniteType g :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) H hf inferInstance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩

theorem surjective_spMap {K L : Type} [Field K] [Field L] (k : K →+* L) : Surjective (spMap k) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨y⟩ : Nonempty (Sp L) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  exact ⟨y, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩

theorem flat_spMap {K L : Type} [Field K] [Field L] (k : K →+* L) : Flat (spMap k) := by
  rw [Flat.SpecMap_iff]
  algebraize [k]
  exact (inferInstance : Module.Flat K L)

theorem finite_etale_spMap {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [FiniteDimensional ℚ L]
    (k : K →+* L) : IsFinite (spMap k) ∧ Etale (spMap k) := by
  algebraize [k]
  have : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun x => by simp
  have hf : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  constructor
  · rw [IsFinite.SpecMap_iff]
    exact hf
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ : Algebra.Etale K L)

theorem exists_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H), l₀.Dvd l₁ → ∃ (k : KA l₀ →+* KA l₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (hr : r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k), IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ LevComp (Xo l₁).univ (Xo l₀).univ r ν ∧ IsFinite (pullback.lift r _ hr) ∧ Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) ∧ IsFinite r ∧ Etale r ∧ Surjective r := by
  intro E _ _ _ H D Xo hN l₀ l₁ hd
  obtain ⟨r, k, ν, hk, hr, h1, h2, -, hc⟩ := hN l₀ l₁ (Xo l₀) (Xo l₁) hd
  obtain ⟨c₁⟩ : Nonempty (Coeff l₁) := inferInstance
  have hle : KA l₀ ≤ c₁.F := fun x hx => by
    have := c₁.le (k ⟨x, hx⟩).2
    rwa [hk] at this
  let c₀ : Coeff l₀ :=
    { F := c₁.F
      fin := c₁.fin
      conj := c₁.conj
      zeta_mem := by
        obtain ⟨e, he⟩ := LevelExist.zeta_eq_pow_of_dvd (a := l₀.M') (LevelExist.M'_pos l₁)
          (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _)) (hd.2.2.trans (Nat.dvd_lcm_right _ _)) : l₀.M' ∣ l₁.M')
        rw [he]
        exact pow_mem c₁.zeta_mem e
      le := hle }
  obtain ⟨rF, e1, e2, f1, f2, f3, -⟩ := hc c₀ c₁ rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c₁.F)).toRingHom = 𝟙 (Sp c₁.F) := by
    rw [← Spec.map_id]
    rfl
  have e2' : rF ≫ pullback.snd _ _ = pullback.snd _ _ := e2.trans ((congrArg _ hid).trans (Category.comp_id _))
  have hi : spMap (IntermediateField.inclusion c₁.le).toRingHom ≫ spMap k =
      spMap (IntermediateField.inclusion c₀.le).toRingHom := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact hk x
  have := surjective_spMap (IntermediateField.inclusion c₁.le).toRingHom
  have := flat_spMap (IntermediateField.inclusion c₁.le).toRingHom
  have := isFinite_descendsAlong_fpqc
  have g1 : IsFinite (pullback.lift r _ hr) := of_baseChange @IsFinite _ _ _ r hr _ _ hi rF e1 e2' f1
  have g2 : Etale (pullback.lift r _ hr) := of_baseChange @Etale _ _ _ r hr _ _ hi rF e1 e2' f2
  have g3 : Surjective (pullback.lift r _ hr) := of_baseChange @Surjective _ _ _ r hr _ _ hi rF e1 e2' f3
  have := c₁.fin
  have : FiniteDimensional ℚ (KA l₁) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion c₁.le).toLinearMap
      (IntermediateField.inclusion c₁.le).injective
  obtain ⟨k1, k2⟩ := finite_etale_spMap k
  have k3 := surjective_spMap k
  have hfac : pullback.lift r _ hr ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  refine ⟨k, r, ν, hr, hk, ⟨h1, h2⟩, g1, g2, g3, ?_, ?_, ?_⟩
  all_goals
    rw [← hfac]
    infer_instance

end GlobalTheory.LevelMap

end
