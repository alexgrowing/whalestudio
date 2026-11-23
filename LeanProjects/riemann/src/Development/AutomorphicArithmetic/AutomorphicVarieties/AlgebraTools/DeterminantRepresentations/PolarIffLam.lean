import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.StarDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.StarApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

private theorem star_single_X_sub_mapRingHom_C {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (x : MonoidAlgebra R F.G₀) :
    F.star O R[X] n (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom F.G₀ C x) = MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom F.G₀ C (F.star O R n x) := by
  have h1 : pushCh (C : R →+* R[X]) (F.eps O R) = F.eps O R[X] := by
    ext x
    simp [GFrame.eps, pushCh, Polynomial.algebraMap_apply]
  have he : ∀ (h : F.G₀) (k : ℤ), (C : R →+* R[X]) ((F.eps O R h ^ k : Rˣ) : R) = ((F.eps O R[X] h ^ k : R[X]ˣ) : R[X]) := by
    intro h k
    rw [← h1, pushCh, MonoidHom.comp_apply, ← map_zpow (Units.map ((C : R →+* R[X]) : R →* R[X]))]
    rfl
  have hs : ∀ (S : Type) [CommRing S] [Algebra O S] (h : F.G₀) (r : S), F.star O S n (MonoidAlgebra.single h r) = MonoidAlgebra.single (F.conj h)⁻¹ (r * ((F.eps O S h ^ (1 - (n : ℤ)) : Sˣ) : S)) := by
    intro S _ _ h r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hadd : ∀ (S : Type) [CommRing S] [Algebra O S] (a b : MonoidAlgebra S F.G₀), F.star O S n (a + b) = F.star O S n a + F.star O S n b := by
    intro S _ _ a b
    simp [GFrame.star]
  have hsub : ∀ a b : MonoidAlgebra R[X] F.G₀, F.star O R[X] n (a - b) = F.star O R[X] n a - F.star O R[X] n b := by
    intro a b
    simp [GFrame.star]
  have hz : ∀ (S : Type) [CommRing S] [Algebra O S], F.star O S n 0 = 0 := by
    intro S _ _
    simp [GFrame.star]
  have hone : F.star O R[X] n (MonoidAlgebra.single 1 X) = MonoidAlgebra.single 1 X := by
    rw [hs]
    simp
  have hmap : MonoidAlgebra.mapRingHom F.G₀ C (F.star O R n x) = F.star O R[X] n (MonoidAlgebra.mapRingHom F.G₀ C x) := by
    induction x using MonoidAlgebra.induction_linear with
    | zero => rw [hz, map_zero, hz]
    | add a b ha hb => rw [hadd, map_add, ha, hb, map_add, hadd]
    | single h r =>
      rw [hs, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, hs, map_mul, he]
  rw [hsub, hone, hmap]

theorem UpperTheory.V.AlgebraTools.Det.polarIffLam :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀), F.IsPolar O D ↔
    ∀ i g, D.lam i (F.star O R n (MonoidAlgebra.single g 1)) = D.lam i (MonoidAlgebra.single g 1) := by
  intro l _ F O _ _ R _ _ n D
  obtain ⟨D', hD'⟩ := AlgebraTools.Det.starDet F O R n D
  have hchi : ∀ y, D'.chi y = D.chi (F.star O R n y) := by
    intro y
    simp only [GDet.chi]
    rw [hD' R[X], star_single_X_sub_mapRingHom_C]
  have hlam : ∀ i y, D'.lam i y = D.lam i (F.star O R n y) := by
    intro i y
    simp only [GDet.lam, hchi]
  constructor
  · intro hP i g
    have hc : D.chi (F.star O R n (MonoidAlgebra.single g 1)) = D.chi (MonoidAlgebra.single g 1) := by
      simp only [GDet.chi]
      rw [← star_single_X_sub_mapRingHom_C]
      exact hP R[X] _
    simp only [GDet.lam, hc]
  · intro h
    have hDD : D' = D := by
      apply CA.d_gext
      intro g i _ _
      rw [hlam]
      exact h i g
    intro B _ _ _ _ y
    rw [← hD' B y, hDD]
