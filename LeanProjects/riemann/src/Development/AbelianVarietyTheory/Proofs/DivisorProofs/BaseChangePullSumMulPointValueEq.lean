import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsPullbackChStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsAdditiveLiStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem ptAlg_apply_of_left {R D E : Type} [CommRing R] [CommRing D] [Algebra R D] [CommRing E] [Algebra R E]
    (z : Pt (SpAlg R D) E) (f : D →+* E) (h : z.left = spMap f) (a : D) : ptAlg z a = f a := by
  change (Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left).hom a = f a
  rw [h, Spec.preimage_map]
  rfl

end GlobalTheory.PtExt

theorem GlobalTheory.PtExt.bcPull_sumMul_fv : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] (B : Over (Sp R)) (B' : Over (Sp D)) (q : B'.left ⟶ (SpAlg R D ⊗ B).left) (w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D)) (π : B'.left ⟶ B.left), q ≫ (fst (SpAlg R D) B).left = B'.hom → q ≫ (snd (SpAlg R D) B).left = π → ∀ (mB : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 D) (B'.hom ≫ 𝟙 _) (algebraMap R D) π) (J : Type) [Fintype J] (d : J → D) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))), bcPull w (sumMul d fun i ↦ fv (β i)) = fv (∑ i, d i • mB.coef.pullbackOneCocycle (β i)) := by
  classical
  intro R D _ _ _ B B' q w π hfst hsnd mB J _ d β
  have w' : π ≫ B.hom = B'.hom ≫ spMap (algebraMap R D) := by
    rw [← hsnd, Category.assoc, Over.w (snd (SpAlg R D) B), w]
  obtain ⟨hadd, hsmul, -⟩ := GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear D B'
  funext E i1 i2 E' i3 i4 ψ y
  have hzero : fv (0 : Z1 (O (dp0 D) (B'.hom ≫ 𝟙 _))) E E' ψ y = 0 := by
    have h := congrArg (fun u : Fn1 B' ↦ u E E' ψ y) (hadd 0 0)
    simp only [add_zero, Fn1.add] at h
    linear_combination -h
  have hsum : ∀ s : Finset J, fv (∑ i ∈ s, d i • mB.coef.pullbackOneCocycle (β i)) E E' ψ y =
      ∑ i ∈ s, algebraMap D E' (d i) * fv (mB.coef.pullbackOneCocycle (β i)) E E' ψ y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      have h := congrArg (fun u : Fn1 B' ↦ u E E' ψ y) (hadd (d j • mB.coef.pullbackOneCocycle (β j)) (∑ i ∈ s, d i • mB.coef.pullbackOneCocycle (β i)))
      simp only [Fn1.add] at h
      rw [h, ih, hsmul]
  rw [hsum]
  simp only [bcPull, sumMul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback_changeOfBase R D (algebraMap R D) B B' π w' mB (β i)]
  congr 1
  · letI : Algebra R E := algVia (algebraMap R D) E
    have hl : (ptVia w y ≫ fst (SpAlg R D) B).left = spMap (algebraMap D E) := by
      rw [Over.comp_left]
      change (y.left ≫ q) ≫ (fst (SpAlg R D) B).left = _
      rw [Category.assoc, hfst]
      exact Over.w y
    rw [ptAlg_apply_of_left _ _ hl]
    exact ψ.commutes (d i)
  · simp only [bcPull]
    congr 1
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    change (y.left ≫ q) ≫ (snd (SpAlg R D) B).left = y.left ≫ π
    rw [Category.assoc, hsnd]
