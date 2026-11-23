import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

namespace GlobalTheory

theorem adjunction_homEquiv_symm_mul {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [R.Monoidal] {Y : C} {M : D} [MonObj M] (a b : Y ⟶ R.obj M) :
    (adj.homEquiv Y M).symm (a * b) = (adj.homEquiv Y M).symm a * (adj.homEquiv Y M).symm b := by
  rw [Hom.mul_def, Hom.mul_def, Functor.obj.μ_def, ← Category.assoc,
    adj.homEquiv_naturality_right_symm]
  congr 1
  ext
  · rw [← adj.homEquiv_naturality_right_symm]; simp
  · rw [← adj.homEquiv_naturality_right_symm]; simp

variable {k : Type} [Field k] {X : Type} [AddCommGroup X]

attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra

noncomputable def splitTorusPoint (t : Multiplicative X →* kˣ) :
    𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X :=
  Over.homMk (Spec.map (CommRingCat.ofHom (torusEval t).toRingHom) ≫ (torusIso k X).hom) (by
    erw [Category.assoc, torusIso_hom_hom, ← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp]
    have : (torusEval t).toRingHom.comp (algebraMap k (AddMonoidAlgebra k X)) = RingHom.id k :=
      (torusEval t).comp_algebraMap
    rw [this]
    exact Spec.map_id _)

theorem splitTorusPoint_left (t : Multiplicative X →* kˣ) :
    (splitTorusPoint t).left =
      Spec.map (CommRingCat.ofHom (torusEval t).toRingHom) ≫ (torusIso k X).hom := rfl

theorem splitTorusPoint_bijective :
    Function.Bijective (splitTorusPoint : (Multiplicative X →* kˣ) → _) := by
  constructor
  · intro s t h
    have h1 := congrArg (·.left) h
    simp only [splitTorusPoint_left] at h1
    have h2 := Spec.map_injective ((cancel_mono _).1 h1)
    exact torusEval_bijective.1 (AlgHom.coe_ringHom_injective (congrArg (·.hom) h2))
  · intro x
    let g : Spec (.of k) ⟶ Spec (.of (AddMonoidAlgebra k X)) := x.left ≫ (torusIso k X).inv
    have hg : CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k X)) ≫ Spec.preimage g = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, ← torusIso_hom_hom, Spec.map_id]
      simp only [g]
      erw [Category.assoc, Iso.inv_hom_id_assoc]
      exact Over.w x
    obtain ⟨t, ht⟩ := torusEval_bijective.2 ⟨(Spec.preimage g).hom, fun r => congr($hg r)⟩
    refine ⟨t, Over.OverMorphism.ext ?_⟩
    rw [splitTorusPoint_left, ht]
    change Spec.map (Spec.preimage g) ≫ _ = _
    rw [Spec.map_preimage]
    simp only [g]
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

noncomputable def splitTorusDown (x : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    (Spec (.of k)).asOver (Spec ZU) ⟶ splitTorusAff ZU X :=
  (Over.homMk (𝟙 (Sp k)) (specULiftZIsTerminal.hom_ext _ _) :
    (Spec (.of k)).asOver (Spec ZU) ⟶ (Over.map (toZ (Sp k))).obj (𝟙_ (Over (Sp k)))) ≫
    ((Over.mapPullbackAdj (toZ (Sp k))).homEquiv _ _).symm x

theorem splitTorusDown_left (x : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    (splitTorusDown x).left = x.left ≫ torusFst (Sp k) X := by
  simp [splitTorusDown, Adjunction.homEquiv_symm_apply, torusFst]
  rfl

theorem splitTorusDown_mul (x y : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    splitTorusDown (x * y) = splitTorusDown x * splitTorusDown y := by
  unfold splitTorusDown
  rw [← comp_mul]
  exact congrArg _ (adjunction_homEquiv_symm_mul (Over.mapPullbackAdj _) x y)

theorem splitTorusDown_injective :
    Function.Injective (splitTorusDown : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) → _) := by
  intro x y h
  have h1 := congrArg (·.left) h
  simp only [splitTorusDown_left] at h1
  exact Over.OverMorphism.ext (pullback.hom_ext h1 ((Over.w x).trans (Over.w y).symm))

noncomputable def torusEvalInt (t : Multiplicative X →* kˣ) :
    AddMonoidAlgebra ZU.{0} X →ₐ[ZU.{0}] k :=
  AddMonoidAlgebra.lift _ k X ((Units.coeHom k).comp t)

theorem splitTorusDown_point (t : Multiplicative X →* kˣ) :
    splitTorusDown (splitTorusPoint t) = Spec.mapMulEquiv (WithConv.toConv (torusEvalInt t)) := by
  refine Over.OverMorphism.ext ?_
  rw [splitTorusDown_left, splitTorusPoint_left]
  erw [Category.assoc, torusIso_hom_fst, ← Spec.map_comp]
  change _ = Spec.map (CommRingCat.ofHom (torusEvalInt t).toRingHom)
  rw [← CommRingCat.ofHom_comp]
  congr 2
  refine ringHom_ext_ZU fun y => ?_
  simp [torusEvalInt]

theorem torusEvalInt_mul (s t : Multiplicative X →* kˣ) :
    WithConv.toConv (torusEvalInt (s * t)) =
      WithConv.toConv (torusEvalInt s) * WithConv.toConv (torusEvalInt t) := by
  apply WithConv.ofConv_injective
  apply AlgHom.coe_ringHom_injective
  refine ringHom_ext_ZU fun y => ?_
  simp [torusEvalInt, AlgHom.convMul_def]

theorem splitTorusPoint_mul (s t : Multiplicative X →* kˣ) :
    splitTorusPoint (s * t) = splitTorusPoint s * splitTorusPoint t := by
  apply splitTorusDown_injective
  rw [splitTorusDown_mul, splitTorusDown_point, splitTorusDown_point, splitTorusDown_point,
    torusEvalInt_mul, map_mul]

variable (k X) in

noncomputable def splitTorusPointEquiv :
    (Multiplicative X →* kˣ) ≃* (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :=
  { Equiv.ofBijective _ splitTorusPoint_bijective with map_mul' := splitTorusPoint_mul }

theorem range_splitTorusPoint_left (t : Multiplicative X →* kˣ) :
    Set.range (splitTorusPoint t).left = {(torusIso k X).hom (torusPrime t)} := by
  have h : ∀ p, (splitTorusPoint t).left p = (torusIso k X).hom (torusPrime t) := fun p => by
    have hp : p = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [hp]
    rfl
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact h p
  · rintro rfl
    exact ⟨_, h (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)⟩

theorem finite_of_isClosed_splitTorus_of_pow_eq_one :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X] (n : ℕ), n.Prime → (n : k) ≠ 0 →
      ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X))
        (Z : Set (splitTorus (Sp k) X).left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) →
        (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C := by
  intro k _ _ X _ _ _ n hp hn C Z hZ hC htors
  haveI : NeZero (n : k) := ⟨hn⟩
  let e := splitTorusPointEquiv k X
  have hcl : @IsClosed _ (torusZariski k X)
      (C.comap e.toMonoidHom : Set (Multiplicative X →* kˣ)) := by
    refine isClosed_induced_iff.2 ⟨(torusIso k X).hom ⁻¹' Z,
      hZ.preimage (torusIso k X).hom.continuous, ?_⟩
    ext t
    change _ ↔ splitTorusPoint t ∈ C
    rw [hC, range_splitTorusPoint_left, Set.singleton_subset_iff]
    rfl
  have h := finite_of_isClosed_torusZariski_of_pow_eq_one hp.two_le hcl fun s hs h1 =>
    e.injective (by rw [map_one]; exact htors _ hs (by rw [← map_pow, h1, map_one]))
  have e' : C.comap e.toMonoidHom ≃ C := e.toEquiv.subtypeEquiv fun _ => Iff.rfl
  exact e'.finite_iff.1 h.1

end GlobalTheory
