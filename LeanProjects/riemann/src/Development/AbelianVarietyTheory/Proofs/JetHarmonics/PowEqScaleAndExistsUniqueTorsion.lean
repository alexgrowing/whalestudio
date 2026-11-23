import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ThmASt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TangentPow

variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]

theorem ptMap_comp_ptMap {A B C : Type} [CommRing A] [Algebra O A] [CommRing B] [Algebra O B]
    [CommRing C] [Algebra O C] (φ : A →ₐ[O] B) (ψ : B →ₐ[O] C) :
    ptMap ψ ≫ ptMap φ = ptMap (ψ.comp φ) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem ptMap_id' (A : Type) [CommRing A] [Algebra O A] : ptMap (AlgHom.id O A) = 𝟙 _ := by
  ext1
  exact Spec.map_id _

variable (O) in

noncomputable abbrev scale (a : R) : specO O (DualNumber R) ⟶ specO O (DualNumber R) :=
  ptMap ((TrivSqZeroExt.map (a • (LinearMap.id : R →ₗ[R] R))).restrictScalars O)

theorem scale_one : scale O (1 : R) = 𝟙 _ := by
  rw [← ptMap_id', scale]
  congr 1
  refine AlgHom.ext fun x => ?_
  ext <;> simp

theorem scale_zero : scale O (0 : R) =
    ptMap (TrivSqZeroExt.inlAlgHom O R R) ≫ ptMap (TrivSqZeroExt.fstHom O R R) := by
  rw [ptMap_comp_ptMap, scale]
  congr 1
  refine AlgHom.ext fun x => ?_
  ext <;> simp

variable (O) in

noncomputable abbrev toTwo (l : R →ₗ[R] R × R) :
    specO O (TrivSqZeroExt R (R × R)) ⟶ specO O (DualNumber R) :=
  ptMap ((TrivSqZeroExt.map l).restrictScalars O)

variable (O) in

noncomputable abbrev ofTwo (l : R × R →ₗ[R] R) :
    specO O (DualNumber R) ⟶ specO O (TrivSqZeroExt R (R × R)) :=
  ptMap ((TrivSqZeroExt.map l).restrictScalars O)

theorem ofTwo_toTwo (l : R →ₗ[R] R × R) (l' : R × R →ₗ[R] R) :
    ofTwo O l' ≫ toTwo O l = scale O (l' (l 1)) := by
  rw [ofTwo, toTwo, ptMap_comp_ptMap, scale]
  congr 1
  refine AlgHom.ext fun x => ?_
  have : l' (l x.snd) = l' (l 1) * x.snd := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
  ext <;> simp [this]

variable {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {y : specO O (DualNumber R) ⟶ G}

theorem scale_zero_comp (hy : ptMap (TrivSqZeroExt.fstHom O R R) ≫ y = 1) :
    scale O (0 : R) ≫ y = 1 := by
  rw [scale_zero, Category.assoc, hy, comp_one]

theorem scale_add_comp (hy : ptMap (TrivSqZeroExt.fstHom O R R) ≫ y = 1) (a b : R) :
    scale O (a + b) ≫ y = (scale O a ≫ y) * (scale O b ≫ y) := by
  let i₁ := LinearMap.inl R R R
  let i₂ := LinearMap.inr R R R
  have key : toTwo O (i₁ + i₂) ≫ y = (toTwo O i₁ ≫ y) * (toTwo O i₂ ≫ y) := by
    ext1
    refine GlobalTheory.TangentCrit.hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R R R)).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom
        (fun x => ⟨1, one_pos, TrivSqZeroExt.map i₁ x, by ext <;> simp [i₁]⟩)
        fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : ofTwo O (LinearMap.fst R R R) ≫ _ = ofTwo O (LinearMap.fst R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, ofTwo_toTwo]
      have e₁ : LinearMap.fst R R R ((i₁ + i₂) 1) = 1 := by simp [i₁, i₂]
      have e₂ : LinearMap.fst R R R (i₁ 1) = 1 := rfl
      have e₃ : LinearMap.fst R R R (i₂ 1) = 0 := rfl
      rw [e₁, e₂, e₃, scale_zero_comp hy, _root_.mul_one]
    · refine congrArg Over.Hom.left
        (?_ : ofTwo O (LinearMap.snd R R R) ≫ _ = ofTwo O (LinearMap.snd R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, ofTwo_toTwo]
      have e₁ : LinearMap.snd R R R ((i₁ + i₂) 1) = 1 := by simp [i₁, i₂]
      have e₂ : LinearMap.snd R R R (i₁ 1) = 0 := rfl
      have e₃ : LinearMap.snd R R R (i₂ 1) = 1 := rfl
      rw [e₁, e₂, e₃, scale_zero_comp hy, _root_.one_mul]
  let l := a • LinearMap.fst R R R + b • LinearMap.snd R R R
  have := congrArg (ofTwo O l ≫ ·) key
  simp only [comp_mul, ← Category.assoc, ofTwo_toTwo] at this
  have e₁ : l ((i₁ + i₂) 1) = a + b := by simp [l, i₁, i₂]
  have e₂ : l (i₁ 1) = a := by simp [l, i₁]
  have e₃ : l (i₂ 1) = b := by simp [l, i₂]
  rwa [e₁, e₂, e₃] at this

theorem pow_eq_scale_comp (hy : ptMap (TrivSqZeroExt.fstHom O R R) ≫ y = 1) (N : ℕ) :
    y ^ N = scale O (N : R) ≫ y := by
  induction N with
  | zero => rw [pow_zero, Nat.cast_zero, scale_zero_comp hy]
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, scale_add_comp hy, ih, scale_one, Category.id_comp]

theorem pow_eq_scale_and_existsUnique_torsion :
    ∀ (O : Type) [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] (R : Type)
      [CommRing R] [Algebra O R] (N : ℕ) (y : specO O (DualNumber R) ⟶ G),
      ptMap (TrivSqZeroExt.fstHom O R R) ≫ y = 1 →
      y ^ N = ptMap ((TrivSqZeroExt.map ((N : R) • (LinearMap.id : R →ₗ[R] R))).restrictScalars O)
          ≫ y ∧
        ((N : R) = 0 → ∃! w : specO O (DualNumber R) ⟶ torsion G N, w ≫ torsion.ι G N = y) := by
  intro O _ G _ R _ _ N y hy
  refine ⟨pow_eq_scale_comp hy N, fun hN => ?_⟩
  have h : y ^ N = 1 := by rw [pow_eq_scale_comp hy, hN, scale_zero_comp hy]
  exact ⟨KernelNoTorsion.torsionLift y h, KernelNoTorsion.torsionLift_ι y h, fun w hw =>
    KernelNoTorsion.torsion_hom_ext (hw.trans (KernelNoTorsion.torsionLift_ι y h).symm)⟩

end GlobalTheory.TangentPow
