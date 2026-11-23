import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.TiDeriv

abbrev archT (Y : ArchMatrix ℚ 3) : ArchMatrix ℚ 3 :=
  Matrix.transpose (show Matrix (Fin 3) (Fin 3) (mixedEmbedding.mixedSpace ℚ) from Y)

theorem exp_archT (Y : ArchMatrix ℚ 3) : NormedSpace.exp (archT Y) = archT (NormedSpace.exp Y) :=
  Matrix.exp_transpose _

theorem ti_mul' (a b : G3) : ti (a * b) = ti a * ti b := by
  apply Units.ext
  change (b.inv * a.inv).transpose = a.inv.transpose * b.inv.transpose
  rw [Matrix.transpose_mul]

theorem prodEquiv_ti (g : G3) : AdelicGLn.prodEquiv ℚ 3 (ti g) =
    (ti (AdelicGLn.prodEquiv ℚ 3 g).1, ti (AdelicGLn.prodEquiv ℚ 3 g).2) := by
  have e : (AdelicGLn.prodEquiv ℚ 3 g)⁻¹ = AdelicGLn.prodEquiv ℚ 3 g⁻¹ := (map_inv _ _).symm
  have e1 : ((AdelicGLn.prodEquiv ℚ 3 g).1)⁻¹ = (AdelicGLn.prodEquiv ℚ 3 g⁻¹).1 := congrArg Prod.fst e
  have e2 : ((AdelicGLn.prodEquiv ℚ 3 g).2)⁻¹ = (AdelicGLn.prodEquiv ℚ 3 g⁻¹).2 := congrArg Prod.snd e
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · refine Matrix.ext fun a b => ?_
    change (Units.val (g⁻¹ : G3) b a).1 = Units.val ((AdelicGLn.prodEquiv ℚ 3 g).1)⁻¹ b a
    rw [e1]; rfl
  · refine Matrix.ext fun a b => ?_
    change (Units.val (g⁻¹ : G3) b a).2 = Units.val ((AdelicGLn.prodEquiv ℚ 3 g).2)⁻¹ b a
    rw [e2]; rfl

theorem ti_infEmb (x y : archGroup ℚ 3)
    (hxy : ((y : (ArchMatrix ℚ 3)ˣ) : ArchMatrix ℚ 3) =
      archT (((x⁻¹ : archGroup ℚ 3) : (ArchMatrix ℚ 3)ˣ) : ArchMatrix ℚ 3)) :
    ti (infEmb ℚ 3 x) = infEmb ℚ 3 y := by
  apply (AdelicGLn.prodEquiv ℚ 3).injective
  rw [prodEquiv_ti, prodEquiv_infEmb, prodEquiv_infEmb]
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · refine Matrix.ext fun a b => ?_
    change Units.val ((archEquiv ℚ 3).symm x)⁻¹ b a = Units.val ((archEquiv ℚ 3).symm y) a b
    rw [← map_inv]
    change (archMatrixEquiv ℚ 3).symm (((x⁻¹ : archGroup ℚ 3) : (ArchMatrix ℚ 3)ˣ) : ArchMatrix ℚ 3) b a =
      (archMatrixEquiv ℚ 3).symm ((y : (ArchMatrix ℚ 3)ˣ) : ArchMatrix ℚ 3) a b
    rw [hxy]; rfl
  · refine Matrix.ext fun a b => ?_
    change Units.val (1 : AdelicGLn.FiniteAdelicGL ℚ 3)⁻¹ b a = Units.val (1 : AdelicGLn.FiniteAdelicGL ℚ 3) a b
    rw [inv_one]
    exact congrFun (congrFun (Matrix.transpose_one (n := Fin 3) (α := FiniteAdeleRing (𝓞 ℚ) ℚ)) a) b

theorem ti_infEmb_expG (Y Z : archLie ℚ 3)
    (hZ : (Z : ArchMatrix ℚ 3) = archT (-(Y : ArchMatrix ℚ 3))) :
    ti (infEmb ℚ 3 ((isExpLieAlgebra ℚ 3).expG Y)) = infEmb ℚ 3 ((isExpLieAlgebra ℚ 3).expG Z) := by
  apply ti_infEmb
  have e : ((((isExpLieAlgebra ℚ 3).expG Y)⁻¹ : archGroup ℚ 3) : (ArchMatrix ℚ 3)ˣ).val =
      NormedSpace.exp (-(Y : ArchMatrix ℚ 3)) := coe_expUnit_inv ℝ (ArchMatrix ℚ 3) _
  rw [e, IsExpLieAlgebra.coe_expG, hZ, exp_archT]

def eL (i j : Fin 3) : archLie ℚ 3 :=
  ⟨(Matrix.single i j 1 : Matrix (Fin 3) (Fin 3) (mixedEmbedding.mixedSpace ℚ)), Submodule.mem_top⟩

theorem eL_smul (i j : Fin 3) (t : ℝ) :
    (((-t) • eL j i : archLie ℚ 3) : ArchMatrix ℚ 3) = archT (-((t • eL i j : archLie ℚ 3) : ArchMatrix ℚ 3)) := by
  change (-t) • (Matrix.single j i 1 : Matrix (Fin 3) (Fin 3) (mixedEmbedding.mixedSpace ℚ)) =
    Matrix.transpose (-(t • (Matrix.single i j 1 : Matrix (Fin 3) (Fin 3) (mixedEmbedding.mixedSpace ℚ))))
  rw [Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_single, neg_smul]

theorem EA_comp_ti : ∀ (F : archSmooth ℚ 3) (c : G3) (i j : Fin 3) (h : IsArchSmooth (fun g : G3 => (F : G3 → ℂ) (c * ti g))),
    ((EA i j ⟨fun g : G3 => (F : G3 → ℂ) (c * ti g), h⟩ : archSmooth ℚ 3) : G3 → ℂ) =
      fun g : G3 => -((EA j i F : archSmooth ℚ 3) : G3 → ℂ) (c * ti g) := by
  intro F c i j h
  funext g
  have h1 := (isExpLieAlgebra ℚ 3).hasDerivAt_rightDeriv (h g) (eL i j) 1
  have h2 := (isExpLieAlgebra ℚ 3).hasDerivAt_rightDeriv (F.2 (c * ti g)) (eL j i) 1
  have h2' : HasDerivAt (fun t : ℝ => archSlice (F : G3 → ℂ) (c * ti g) (1 * (isExpLieAlgebra ℚ 3).expG (t • eL j i)))
      ((isExpLieAlgebra ℚ 3).rightDeriv (eL j i) (archSlice (F : G3 → ℂ) (c * ti g)) 1) (-(0 : ℝ)) := by
    simpa using h2
  have h3 := h2'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have hfun : (fun t : ℝ => archSlice (fun g : G3 => (F : G3 → ℂ) (c * ti g)) g (1 * (isExpLieAlgebra ℚ 3).expG (t • eL i j))) =
      (fun t : ℝ => archSlice (F : G3 → ℂ) (c * ti g) (1 * (isExpLieAlgebra ℚ 3).expG (t • eL j i))) ∘ Neg.neg := by
    funext t
    simp only [one_mul, archSlice_apply, Function.comp]
    rw [ti_mul', ti_infEmb_expG _ _ (eL_smul i j t), mul_assoc]
  rw [hfun] at h1
  have h4 := h1.unique h3
  have eL1 : ((EA i j ⟨fun g : G3 => (F : G3 → ℂ) (c * ti g), h⟩ : archSmooth ℚ 3) : G3 → ℂ) g =
      (isExpLieAlgebra ℚ 3).rightDeriv (eL i j) (archSlice (fun g : G3 => (F : G3 → ℂ) (c * ti g)) g) 1 :=
    uAction_ι_apply _ _ g
  have eL2 : ((EA j i F : archSmooth ℚ 3) : G3 → ℂ) (c * ti g) =
      (isExpLieAlgebra ℚ 3).rightDeriv (eL j i) (archSlice (F : G3 → ℂ) (c * ti g)) 1 :=
    uAction_ι_apply _ _ _
  rw [eL1, eL2, h4]
  simp

end GlobalTheory.CompanionTheory.UnfoldingAlt.TiDeriv

end
