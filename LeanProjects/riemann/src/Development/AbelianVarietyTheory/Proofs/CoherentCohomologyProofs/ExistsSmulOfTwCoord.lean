import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem GrSum.apply_eq_eval₂Hom_mul {ι R B : Type*} [CommRing R] [CommRing B]
    {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x) (c : R →+* B) (b : ι → B)
    (φ : ∀ n, A n → B) (hadd : ∀ n a a', φ n (a + a') = φ n a + φ n a')
    (hsmul : ∀ n (r : R) a, φ n (r • a) = c r * φ n a)
    (hop : ∀ i n a, φ (n + 1) (x i n a) = b i * φ n a)
    (F : MvPolynomial ι R) {t t' : ℤ} {a : A t} {a' : A t'}
    (h : F • GrSum.of hx t a = GrSum.of hx t' a') :
    φ t' a' = MvPolynomial.eval₂Hom c b F * φ t a := by
  letI : Algebra R B := c.toAlgebra
  letI : Algebra (MvPolynomial ι R) B := (MvPolynomial.eval₂Hom c b).toAlgebra
  haveI : IsScalarTower R (MvPolynomial ι R) B :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C c b r).symm
  let ψ : ∀ n, A n →ₗ[R] B := fun n => ⟨⟨φ n, hadd n⟩, hsmul n⟩
  have hψ : ∀ i n a, ψ (n + 1) (x i n a) = (MvPolynomial.X i : MvPolynomial ι R) • ψ n a :=
    fun i n a => (hop i n a).trans
      (congrArg (· * φ n a) (MvPolynomial.eval₂Hom_X' c b i).symm)
  have e := congrArg (GrSum.lift hx ψ hψ) h
  rw [map_smul, GrSum.lift_of, GrSum.lift_of] at e
  exact e.symm

theorem AbLaw.exists_smul_of_twCoord :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (V : Y.Opens) (F : MvPolynomial (Fin (m + 1)) R) (d t t' : ℤ) (y : SecOn (tw M H t) V), F ∈ polyGrading (Fin (m + 1)) R d → t' = t + d → ∃ y' : SecOn (tw M H t') V, F • GrSum.of (hx V) t (SecOnR.of f _ V y) = GrSum.of (hx V) t' (SecOnR.of f _ V y') ∧ ∀ (p : M.ι) (l : H.ι), SecOn.twCoord y' p l = rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (MvPolynomial.eval₂Hom (cst f (H.U l)) (fun j => (s j).f l) F) * SecOn.twCoord y p l := by
  intro R _ Y f H m s M hx V F d t t' y hF ht
  subst ht
  obtain ⟨a, ha⟩ := (GrSum.mem_grading (hx V)).1
    (grSMul_mem (GrSum.grading (hx V)) hF (GrSum.of_mem_grading (hx V) t (SecOnR.of f _ V y)))
  refine ⟨(SecOnR.of f _ V).symm a, ha.symm, fun p l => ?_⟩
  have h₀ : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l := inf_le_right.trans inf_le_right
  have e := GrSum.apply_eq_eval₂Hom_mul (hx V) (cst f (V ⊓ (M.U p ⊓ H.U l)))
    (fun j => rs Y h₀ ((s j).f l))
    (fun n z => SecOn.twCoord ((SecOnR.of f _ V).symm z) p l) (fun _ _ _ => rfl)
    (fun n r z => SecOnR.coord_base_smul r z (p, l)) (fun _ _ _ => rfl) F ha.symm
  refine e.trans (congrArg (· * SecOn.twCoord y p l) ?_)
  rw [MvPolynomial.map_eval₂Hom]
  congr 2
  exact RingHom.ext fun r => (rs_cst f h₀ r).symm

end GlobalTheory
