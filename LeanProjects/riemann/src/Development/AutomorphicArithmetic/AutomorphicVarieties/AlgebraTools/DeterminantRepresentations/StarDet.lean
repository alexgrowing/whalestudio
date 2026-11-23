import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.StarApi

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

private theorem star_mapRingHom_algHom_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (B B' : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] [CommRing B'] [Algebra R B'] [Algebra O B'] [IsScalarTower O R B'] (f : B →ₐ[R] B') (x : MonoidAlgebra B F.G₀) : F.star O B' n (MonoidAlgebra.mapRingHom F.G₀ (f : B →+* B') x) = MonoidAlgebra.mapRingHom F.G₀ (f : B →+* B') (F.star O B n x) := by
  have he : ∀ g : F.G₀, Units.map (f : B →* B') (F.eps O B g) = F.eps O B' g := by
    intro g
    ext
    simp [GFrame.eps, pushCh, IsScalarTower.algebraMap_apply O R B, IsScalarTower.algebraMap_apply O R B']
  have hs : ∀ (C : Type) [CommRing C] [Algebra O C] (g : F.G₀) (b : C), F.star O C n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ↑(F.eps O C g ^ (1 - (n:ℤ)))) := by
    intro C _ _ g b
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single']
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add x y hx hy => simp only [map_add] at hx hy ⊢; simp [GFrame.star, map_add] at hx hy ⊢; rw [hx, hy]
  | single g b =>
    rw [MonoidAlgebra.mapRingHom_single, hs, hs, MonoidAlgebra.mapRingHom_single, map_mul, ← he g, ← map_zpow]
    rfl

theorem UpperTheory.V.AlgebraTools.Det.starDet :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀), ∃ D' : GDet n R F.G₀,
    ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀), D'.D B y = D.D B (F.star O B n y) := by
  intro l _ F O _ _ R _ _ n D
  let E : ∀ (B : Type) [CommRing B] [Algebra R B], MonoidAlgebra B F.G₀ →* B := fun B _ _ =>
    letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
    { toFun := fun y => D.D B (F.star O B n y)
      map_one' := by simp [GFrame.star]
      map_mul' := fun x y => by
        have hm : F.star O B n (x * y) = F.star O B n y * F.star O B n x := by simp [GFrame.star, map_mul]
        simp only [hm, map_mul, mul_comm] }
  have hE : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀), E B y = D.D B (F.star O B n y) := by
    intro B _ _ iO _ y
    have hi : ((algebraMap R B).comp (algebraMap O R)).toAlgebra = iO :=
      Algebra.algebra_ext _ _ (fun r => (IsScalarTower.algebraMap_apply O R B r).symm)
    subst hi
    rfl
  refine ⟨{ D := E, nat := ?_, homog := ?_ }, fun B _ _ _ _ y => hE B y⟩
  · intro B B' _ _ _ _ f x
    letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
    haveI : IsScalarTower O R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : Algebra O B' := ((algebraMap R B').comp (algebraMap O R)).toAlgebra
    haveI : IsScalarTower O R B' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    rw [hE B', hE B, star_mapRingHom_algHom_eq F O R n B B' f x, D.nat]
  · intro B _ _ b x
    letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
    haveI : IsScalarTower O R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hsm : F.star O B n (b • x) = b • F.star O B n x := by simp [GFrame.star, map_smul]
    rw [hE B, hE B, hsm, D.homog]
