import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.Smooth
import GroundTheory.AutomorphicForms.HarishChandraCentre
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.SmoothKZ

open NumberField Matrix

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

attribute [local instance 100] LieRing.ofAssociativeRing

def archRealEquiv : ArchMatrix ℚ 2 ≃+* Matrix (Fin 2) (Fin 2) ℝ :=
  (archMatrixEquiv ℚ 2).symm.trans (RingEquiv.mapMatrix GroundTheory.Global.RationalIdeles.realEquiv)

theorem archRealEquiv_apply (M : ArchMatrix ℚ 2) (i j : Fin 2) :
    archRealEquiv M i j = archLin M i j := rfl

theorem archRealEquiv_smul (r : ℝ) (M : ArchMatrix ℚ 2) :
    archRealEquiv (r • M) = r • archRealEquiv M := by
  ext i j
  rw [archRealEquiv_apply, map_smul, Matrix.smul_apply, archRealEquiv_apply]
  rfl

def lieRealMat (X : (isExpLieAlgebra ℚ 2).lieSubalgebra) : Matrix (Fin 2) (Fin 2) ℝ :=
  archRealEquiv (X : ArchMatrix ℚ 2)

def lieOfRealMat (A : Matrix (Fin 2) (Fin 2) ℝ) : (isExpLieAlgebra ℚ 2).lieSubalgebra :=
  ⟨archRealEquiv.symm A, (isExpLieAlgebra ℚ 2).mem_lieSubalgebra.2 Submodule.mem_top⟩

@[simp] theorem lieRealMat_lieOfRealMat (A : Matrix (Fin 2) (Fin 2) ℝ) :
    lieRealMat (lieOfRealMat A) = A :=
  archRealEquiv.apply_symm_apply A

@[simp] theorem lieOfRealMat_lieRealMat (X : (isExpLieAlgebra ℚ 2).lieSubalgebra) :
    lieOfRealMat (lieRealMat X) = X :=
  Subtype.ext (archRealEquiv.symm_apply_apply _)

theorem lieRealMat_add (X Y : (isExpLieAlgebra ℚ 2).lieSubalgebra) :
    lieRealMat (X + Y) = lieRealMat X + lieRealMat Y :=
  map_add archRealEquiv _ _

theorem lieRealMat_smul (r : ℝ) (X : (isExpLieAlgebra ℚ 2).lieSubalgebra) :
    lieRealMat (r • X) = r • lieRealMat X :=
  archRealEquiv_smul r _

theorem lieRealMat_lie (X Y : (isExpLieAlgebra ℚ 2).lieSubalgebra) :
    lieRealMat ⁅X, Y⁆ = lieRealMat X * lieRealMat Y - lieRealMat Y * lieRealMat X := by
  simp only [lieRealMat, LieSubalgebra.coe_bracket, Ring.lie_def, map_sub, map_mul]

theorem lieOfRealMat_add (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    lieOfRealMat (A + B) = lieOfRealMat A + lieOfRealMat B := by
  rw [← lieOfRealMat_lieRealMat (lieOfRealMat A + lieOfRealMat B), lieRealMat_add]
  simp

theorem lieOfRealMat_smul (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    lieOfRealMat (r • A) = r • lieOfRealMat A := by
  rw [← lieOfRealMat_lieRealMat (r • lieOfRealMat A), lieRealMat_smul]
  simp

theorem lieOfRealMat_zero : lieOfRealMat 0 = 0 := by
  rw [← lieOfRealMat_lieRealMat 0]
  simp [lieRealMat]

theorem lieOfRealMat_lie (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    lieOfRealMat (A * B - B * A) = ⁅lieOfRealMat A, lieOfRealMat B⁆ := by
  rw [← lieOfRealMat_lieRealMat ⁅lieOfRealMat A, lieOfRealMat B⁆, lieRealMat_lie]
  simp

def realOpGL2 (A : Matrix (Fin 2) (Fin 2) ℝ) : Module.End ℂ (archSmooth ℚ 2) :=
  uAction (UniversalEnvelopingAlgebra.ι ℝ (lieOfRealMat A))

theorem realOpGL2_add (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    realOpGL2 (A + B) = realOpGL2 A + realOpGL2 B := by
  simp only [realOpGL2, lieOfRealMat_add, map_add]

theorem realOpGL2_zero : realOpGL2 0 = 0 := by
  simp [realOpGL2, lieOfRealMat_zero]

theorem realOpGL2_smul (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    realOpGL2 (r • A) = (r : ℂ) • realOpGL2 A := by
  simp only [realOpGL2, lieOfRealMat_smul, map_smul]
  ext φ g
  simp

theorem realOpGL2_lie (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    realOpGL2 (A * B - B * A) = realOpGL2 A * realOpGL2 B - realOpGL2 B * realOpGL2 A := by
  simp only [realOpGL2, lieOfRealMat_lie, LieHom.map_lie, Ring.lie_def, map_sub, map_mul]

def reMat (B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℝ := B.map Complex.re

def imMat (B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℝ := B.map Complex.im

@[simp] theorem reMat_apply (B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : reMat B i j = (B i j).re := rfl

@[simp] theorem imMat_apply (B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : imMat B i j = (B i j).im := rfl

theorem reMat_add (B C : Matrix (Fin 2) (Fin 2) ℂ) : reMat (B + C) = reMat B + reMat C := by
  ext i j; simp

theorem imMat_add (B C : Matrix (Fin 2) (Fin 2) ℂ) : imMat (B + C) = imMat B + imMat C := by
  ext i j; simp

theorem reMat_smul (c : ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    reMat (c • B) = c.re • reMat B + (-c.im) • imMat B := by
  ext i j; simp; ring

theorem imMat_smul (c : ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    imMat (c • B) = c.re • imMat B + c.im • reMat B := by
  ext i j; simp

theorem reMat_mul (B C : Matrix (Fin 2) (Fin 2) ℂ) :
    reMat (B * C) = reMat B * reMat C + (-1 : ℝ) • (imMat B * imMat C) := by
  ext i j; simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem imMat_mul (B C : Matrix (Fin 2) (Fin 2) ℂ) :
    imMat (B * C) = reMat B * imMat C + imMat B * reMat C := by
  ext i j; simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem reMat_map_ofReal (A : Matrix (Fin 2) (Fin 2) ℝ) : reMat (A.map (↑)) = A := by
  ext i j; simp

theorem imMat_map_ofReal (A : Matrix (Fin 2) (Fin 2) ℝ) : imMat (A.map (↑)) = 0 := by
  ext i j; simp

theorem map_ofReal_reMat_add_imMat (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (reMat B).map (↑) + Complex.I • (imMat B).map (↑) = B := by
  ext i j
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, reMat_apply, imMat_apply, smul_eq_mul]
  rw [mul_comm]
  exact Complex.re_add_im _

def complexOpGL2 (B : Matrix (Fin 2) (Fin 2) ℂ) : Module.End ℂ (archSmooth ℚ 2) :=
  realOpGL2 (reMat B) + Complex.I • realOpGL2 (imMat B)

theorem complexOpGL2_map_ofReal (A : Matrix (Fin 2) (Fin 2) ℝ) :
    complexOpGL2 (A.map (↑)) = realOpGL2 A := by
  rw [complexOpGL2, reMat_map_ofReal, imMat_map_ofReal, realOpGL2_zero, smul_zero, add_zero]

theorem complexOpGL2_add (B C : Matrix (Fin 2) (Fin 2) ℂ) :
    complexOpGL2 (B + C) = complexOpGL2 B + complexOpGL2 C := by
  simp only [complexOpGL2, reMat_add, imMat_add, realOpGL2_add, smul_add]
  abel

theorem complexOpGL2_smul (c : ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    complexOpGL2 (c • B) = c • complexOpGL2 B := by
  simp only [complexOpGL2, reMat_smul, imMat_smul, realOpGL2_add, realOpGL2_smul, smul_add, smul_smul]
  conv_rhs => rw [← Complex.re_add_im c]
  simp only [add_smul, Complex.ofReal_neg]
  match_scalars
  all_goals ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals ring

theorem complexOpGL2_lie (B C : Matrix (Fin 2) (Fin 2) ℂ) :
    complexOpGL2 (B * C - C * B) = complexOpGL2 B * complexOpGL2 C - complexOpGL2 C * complexOpGL2 B := by
  have hre : reMat (B * C - C * B) = (reMat B * reMat C - reMat C * reMat B) +
      (-1 : ℝ) • (imMat B * imMat C - imMat C * imMat B) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, ← neg_one_smul ℂ (C * B), reMat_add, reMat_smul,
      reMat_mul, reMat_mul]
    ext i j; simp; ring
  have him : imMat (B * C - C * B) = (reMat B * imMat C - imMat C * reMat B) +
      (imMat B * reMat C - reMat C * imMat B) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (C * B), imMat_add, imMat_smul, imMat_mul, imMat_mul]
    ext i j; simp; ring
  simp only [complexOpGL2, hre, him, realOpGL2_add, realOpGL2_smul, realOpGL2_lie]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, Complex.I_mul_I]
  push_cast
  match_scalars <;> ring_nf

def complexOpGL2Lie : HarishChandra.gl 2 →ₗ⁅ℂ⁆ Module.End ℂ (archSmooth ℚ 2) where
  toFun := complexOpGL2
  map_add' := complexOpGL2_add
  map_smul' := complexOpGL2_smul
  map_lie' {B C} := by
    simp only [Ring.lie_def]
    exact complexOpGL2_lie B C

def gl2ArchRep : HarishChandra.U 2 →ₐ[ℂ] Module.End ℂ (archSmooth ℚ 2) :=
  UniversalEnvelopingAlgebra.lift ℂ complexOpGL2Lie

@[simp] theorem gl2ArchRep_ι (B : HarishChandra.gl 2) :
    gl2ArchRep (UniversalEnvelopingAlgebra.ι ℂ B) = complexOpGL2 B :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ complexOpGL2Lie B

def gl2ComplexifyLie : (isExpLieAlgebra ℚ 2).lieSubalgebra →ₗ⁅ℝ⁆ HarishChandra.U 2 where
  toFun X := UniversalEnvelopingAlgebra.ι ℂ ((lieRealMat X).map (↑))
  map_add' X Y := by
    rw [lieRealMat_add, Matrix.map_add _ Complex.ofReal_add, map_add]
  map_smul' r X := by
    rw [lieRealMat_smul, RingHom.id_apply]
    have : (r • lieRealMat X).map ((↑) : ℝ → ℂ) = (r : ℂ) • (lieRealMat X).map (↑) := by
      ext i j; simp
    rw [this, map_smul, Complex.coe_smul]
  map_lie' {X Y} := by
    have e : (lieRealMat ⁅X, Y⁆).map ((↑) : ℝ → ℂ) =
        ⁅(lieRealMat X).map ((↑) : ℝ → ℂ), (lieRealMat Y).map ((↑) : ℝ → ℂ)⁆ := by
      rw [lieRealMat_lie, Ring.lie_def]
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    show UniversalEnvelopingAlgebra.ι ℂ ((lieRealMat ⁅X, Y⁆).map ((↑) : ℝ → ℂ)) = _
    rw [e, LieHom.map_lie]

def gl2Complexify : UEnv ℚ 2 →ₐ[ℝ] HarishChandra.U 2 :=
  UniversalEnvelopingAlgebra.lift ℝ gl2ComplexifyLie

@[simp] theorem gl2Complexify_ι (X : (isExpLieAlgebra ℚ 2).lieSubalgebra) :
    gl2Complexify (UniversalEnvelopingAlgebra.ι ℝ X) =
      UniversalEnvelopingAlgebra.ι ℂ ((lieRealMat X).map (↑)) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℝ gl2ComplexifyLie X

theorem gl2ArchRep_gl2Complexify (u : UEnv ℚ 2) : gl2ArchRep (gl2Complexify u) = uAction u := by
  induction u using UEnv.induction with
  | halg r =>
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply ℝ ℂ (HarishChandra.U 2),
      AlgHom.commutes]
    ext φ g
    simp [Algebra.algebraMap_eq_smul_one]
  | hι X =>
    rw [gl2Complexify_ι, gl2ArchRep_ι, complexOpGL2_map_ofReal, realOpGL2, lieOfRealMat_lieRealMat]
  | hmul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul]
  | hadd a b ha hb => rw [map_add, map_add, ha, hb, map_add]

theorem ι_eq_gl2Complexify_add (B : HarishChandra.gl 2) :
    UniversalEnvelopingAlgebra.ι ℂ B =
      gl2Complexify (UniversalEnvelopingAlgebra.ι ℝ (lieOfRealMat (reMat B))) +
        Complex.I • gl2Complexify (UniversalEnvelopingAlgebra.ι ℝ (lieOfRealMat (imMat B))) := by
  rw [gl2Complexify_ι, gl2Complexify_ι, lieRealMat_lieOfRealMat, lieRealMat_lieOfRealMat, ← map_smul,
    ← map_add, map_ofReal_reMat_add_imMat]

theorem gl2Complexify_mem_center {z : UEnv ℚ 2} (hz : z ∈ (isExpLieAlgebra ℚ 2).centerU) :
    gl2Complexify z ∈ Subalgebra.center ℂ (HarishChandra.U 2) := by
  have hc : ∀ X : (isExpLieAlgebra ℚ 2).lieSubalgebra,
      gl2Complexify (UniversalEnvelopingAlgebra.ι ℝ X) * gl2Complexify z =
        gl2Complexify z * gl2Complexify (UniversalEnvelopingAlgebra.ι ℝ X) := by
    intro X
    rw [← map_mul, ← map_mul, (Subalgebra.mem_center_iff.1 hz) (UniversalEnvelopingAlgebra.ι ℝ X)]
  refine HarishChandra.mem_center_of_commute_e fun a => ?_
  rw [HarishChandra.e, ι_eq_gl2Complexify_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hc, hc]

theorem exists_uAction_center_eq_smul_of_gl2ArchRep_conj {φ : archSmooth ℚ 2}
    (g : (HarishChandra.gl 2)ˣ) (lam : Fin 2 → ℂ)
    (hup : ∀ a, HarishChandra.IsUpper a → gl2ArchRep (HarishChandra.conjU g (HarishChandra.e a)) φ = 0)
    (hH : ∀ k, gl2ArchRep (HarishChandra.conjU g (HarishChandra.e (k, k))) φ = lam k • φ)
    {z : UEnv ℚ 2} (hz : z ∈ (isExpLieAlgebra ℚ 2).centerU) :
    ∃ c : ℂ, uAction z φ = c • φ := by
  rw [← gl2ArchRep_gl2Complexify]
  exact HarishChandra.rep_center_apply_mem_span_of_conj gl2ArchRep g lam hup hH (gl2Complexify_mem_center hz)

theorem isZFinite_of_gl2ArchRep_conj {φ : archSmooth ℚ 2} (g : (HarishChandra.gl 2)ˣ) (lam : Fin 2 → ℂ)
    (hup : ∀ a, HarishChandra.IsUpper a → gl2ArchRep (HarishChandra.conjU g (HarishChandra.e a)) φ = 0)
    (hH : ∀ k, gl2ArchRep (HarishChandra.conjU g (HarishChandra.e (k, k))) φ = lam k • φ) :
    IsZFinite φ := by
  unfold IsZFinite
  have hle : Submodule.span ℂ ((fun z => uAction z φ) '' ((isExpLieAlgebra ℚ 2).centerU : Set (UEnv ℚ 2))) ≤
      ℂ ∙ φ := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c, hc⟩ := exists_uAction_center_eq_smul_of_gl2ArchRep_conj g lam hup hH hz
    show uAction z φ ∈ ℂ ∙ φ
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self φ)
  exact Submodule.finiteDimensional_of_le hle

end GL2Classical

end

end GroundTheory.Automorphic
