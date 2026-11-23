import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerLeviPlaces

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace StabilizerLevi

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def mat {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v) (w : InfinitePlace E) :
    Matrix ι ι ℂ :=
  ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)

section Mat

variable {h : HermitianForm F E W} {v : Basis ι E W}

theorem mat_mul (g g' : archUnitary h v) (w : InfinitePlace E) :
    mat (g * g') w = mat g w * mat g' w := rfl

theorem mat_one (w : InfinitePlace E) : mat (1 : archUnitary h v) w = 1 := rfl

theorem mat_mul_inv (g : archUnitary h v) (w : InfinitePlace E) : mat g w * mat g⁻¹ w = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem mat_inv_mul (g : archUnitary h v) (w : InfinitePlace E) : mat g⁻¹ w * mat g w = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem unitary_mat (g : archUnitary h v) (w : InfinitePlace E) :
    (mat g w)ᴴ * gramAt h v w * mat g w = gramAt h v w := by
  have := mem_archUnitary.1 g.2 w
  rwa [conjT_eq] at this

theorem continuous_mat (w : InfinitePlace E) : Continuous fun g : archUnitary h v => mat g w :=
  Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)

end Mat

variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W} {n : ℕ}
  (hp : IsHyperbolicPair h x₀ w₀) {h' : HermitianForm F E (hypComplement h x₀ w₀)}
  (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y) {v' : Basis (Fin n) E (hypComplement h x₀ w₀)}

abbrev bMat (v : Basis ι E W) (v' : Basis (Fin n) E (hypComplement h x₀ w₀)) (w : InfinitePlace E) :
    Matrix ι (Fin n) ℂ :=
  colMat v (fun k => (v' k : W)) w

include hp hh'

theorem q_mul (g g' : archUnitary h v) (hg : g ∈ vecFixGroup h v x₀)
    (hg' : g' ∈ vecFixGroup h v x₀) (w : InfinitePlace E) :
    leviProj (gramAt h v w) (bMat v v' w) (mat (g * g') w) =
      leviProj (gramAt h v w) (bMat v v' w) (mat g w) *
        leviProj (gramAt h v w) (bMat v v' w) (mat g' w) := by
  obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
  rw [mat_mul]
  exact leviProj_mul hH hG hBX hBY hXX hYY hXY hspan (unitary_mat g w) (hg w) (unitary_mat g' w)
    (hg' w)

theorem q_one (w : InfinitePlace E) :
    leviProj (gramAt h v w) (bMat v v' w) (mat (1 : archUnitary h v) w) = 1 := by
  obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
  rw [mat_one, leviProj, Matrix.mul_one]
  exact leftInv_mul hG

def qUnit (g : vecFixGroup h v x₀) (w : InfinitePlace E) : GL (Fin n) ℂ where
  val := leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w)
  inv := leviProj (gramAt h v w) (bMat v v' w) (mat ((g⁻¹ : vecFixGroup h v x₀) : archUnitary h v) w)
  val_inv := by
    rw [← q_mul hp hh' _ _ g.2 (g⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      q_one hp hh']
  inv_val := by
    rw [← q_mul hp hh' _ _ (g⁻¹).2 g.2, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      q_one hp hh']

theorem qUnit_mem (g : vecFixGroup h v x₀) :
    (fun w => qUnit hp hh' (v' := v') g w) ∈ archUnitary h' v' := by
  rw [mem_archUnitary]
  intro w
  obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
  rw [conjT_eq]
  change (leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w))ᴴ * gramAt h' v' w *
    leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w) = gramAt h' v' w
  rw [gramAt_complement v h' hh' v' w]
  exact leviProj_unitary hH hG hBX hBY hXX hYY hXY hspan (unitary_mat _ w) (g.2 w)

def qHom : vecFixGroup h v x₀ →* archUnitary h' v' where
  toFun g := ⟨fun w => qUnit hp hh' g w, qUnit_mem hp hh' g⟩
  map_one' := Subtype.ext (funext fun w => Units.ext (q_one hp hh' w))
  map_mul' g g' := Subtype.ext (funext fun w => Units.ext (q_mul hp hh' _ _ g.2 g'.2 w))

def iUnit (m : archUnitary h' v') (w : InfinitePlace E) : GL ι ℂ where
  val := leviSec (gramAt h v w) (bMat v v' w) (mat m w)
  inv := leviSec (gramAt h v w) (bMat v v' w) (mat m⁻¹ w)
  val_inv := by
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    rw [← leviSec_mul hG, mat_mul_inv, leviSec_one]
  inv_val := by
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    rw [← leviSec_mul hG, mat_inv_mul, leviSec_one]

theorem iUnit_mem (m : archUnitary h' v') : (fun w => iUnit hp hh' (v := v) m w) ∈ archUnitary h v := by
  rw [mem_archUnitary]
  intro w
  obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
  rw [conjT_eq]
  change (leviSec (gramAt h v w) (bMat v v' w) (mat m w))ᴴ * gramAt h v w *
    leviSec (gramAt h v w) (bMat v v' w) (mat m w) = gramAt h v w
  refine leviSec_unitary hH hG _ ?_
  rw [← gramAt_complement v h' hh' v' w]
  exact unitary_mat m w

theorem iUnit_mem_vecFixGroup (m : archUnitary h' v') :
    (⟨fun w => iUnit hp hh' (v := v) m w, iUnit_mem hp hh' m⟩ : archUnitary h v) ∈ vecFixGroup h v x₀ := by
  intro w
  obtain ⟨hH, hG, hBX, -⟩ := frame v hp h' hh' v' w
  exact leviSec_mulVec_of hBX _

def iHom : archUnitary h' v' →* vecFixGroup h v x₀ where
  toFun m := ⟨⟨fun w => iUnit hp hh' (v := v) m w, iUnit_mem hp hh' m⟩, iUnit_mem_vecFixGroup hp hh' m⟩
  map_one' := Subtype.ext (Subtype.ext (funext fun w => Units.ext (by
    change leviSec (gramAt h v w) (bMat v v' w) (mat (1 : archUnitary h' v') w) = 1
    rw [mat_one, leviSec_one])))
  map_mul' m m' := Subtype.ext (Subtype.ext (funext fun w => Units.ext (by
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    change leviSec (gramAt h v w) (bMat v v' w) (mat (m * m') w) =
      leviSec (gramAt h v w) (bMat v v' w) (mat m w) * leviSec (gramAt h v w) (bMat v v' w) (mat m' w)
    rw [mat_mul, leviSec_mul hG])))

theorem continuous_qHom : Continuous (qHom hp hh' (v := v) (v' := v')) := by
  refine continuous_induced_rng.2 (continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩)
  · change Continuous fun g : vecFixGroup h v x₀ =>
      leftInv (gramAt h v w) (bMat v v' w) * mat (g : archUnitary h v) w * bMat v v' w
    exact (continuous_const.matrix_mul ((continuous_mat w).comp continuous_subtype_val)).matrix_mul
      continuous_const
  · change Continuous fun g : vecFixGroup h v x₀ =>
      leftInv (gramAt h v w) (bMat v v' w) * mat ((g⁻¹ : vecFixGroup h v x₀) : archUnitary h v) w *
        bMat v v' w
    exact (continuous_const.matrix_mul (((continuous_mat w).comp continuous_subtype_val).comp
      continuous_inv)).matrix_mul continuous_const

theorem continuous_iHom : Continuous (iHom hp hh' (v := v) (v' := v')) := by
  refine continuous_induced_rng.2 (continuous_induced_rng.2
    (continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩))
  · change Continuous fun m : archUnitary h' v' =>
      1 - bMat v v' w * leftInv (gramAt h v w) (bMat v v' w) +
        bMat v v' w * mat m w * leftInv (gramAt h v w) (bMat v v' w)
    exact continuous_const.add ((continuous_const.matrix_mul (continuous_mat w)).matrix_mul
      continuous_const)
  · change Continuous fun m : archUnitary h' v' =>
      1 - bMat v v' w * leftInv (gramAt h v w) (bMat v v' w) +
        bMat v v' w * mat m⁻¹ w * leftInv (gramAt h v w) (bMat v v' w)
    exact continuous_const.add ((continuous_const.matrix_mul
      ((continuous_mat w).comp continuous_inv)).matrix_mul continuous_const)

end StabilizerLevi

open StabilizerLevi

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem StabilizerLevi.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    StabilizerLevi.Statement h v := by
  intro x₀ w₀ hp h' hh' n v'
  refine ⟨iHom hp hh', qHom hp hh', continuous_iHom hp hh', continuous_qHom hp hh', ?_, ?_, ?_, ?_⟩
  · intro m
    apply Subtype.ext
    funext w
    apply Units.ext
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    exact leviProj_leviSec hG (mat m w)
  · intro g
    rw [mem_unipRadical]
    constructor
    · intro h1 w
      obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
      have e : leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w) = 1 :=
        congrArg (fun u : archUnitary h' v' =>
          ((u : InfinitePlace E → GL (Fin n) ℂ) w : Matrix (Fin n) (Fin n) ℂ)) h1
      exact ⟨g.2 w, (leviProj_eq_one_iff hH hG hBX hBY hXX hYY hXY hspan (unitary_mat _ w)
        (g.2 w)).1 e⟩
    · intro h1
      apply Subtype.ext
      funext w
      apply Units.ext
      obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
      exact (leviProj_eq_one_iff hH hG hBX hBY hXX hYY hXY hspan (unitary_mat _ w) (g.2 w)).2
        (h1 w).2
  · intro m w
    obtain ⟨hH, hG, hBX, hBY, -⟩ := frame v hp h' hh' v' w
    exact leviSec_mulVec_of hBY _
  · intro γ m hx hw hW
    apply Subtype.ext
    funext w
    apply Units.ext
    obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
    change leviSec (gramAt h v w) (bMat v v' w) (mat (archEmbed h' v' m) w) = mat (archEmbed h v γ) w
    symm
    apply eq_leviSec hH hG hBX hBY hXX hYY hXY hspan
    · rw [mat, archEmbed_apply, map_toMatrix_mulVec_vecAt]
      exact congrArg (fun x => vecAt v x w) hx
    · rw [mat, archEmbed_apply, map_toMatrix_mulVec_vecAt]
      exact congrArg (fun x => vecAt v x w) hw
    · apply ext_of_mulVec_single
      intro k
      rw [← mulVec_mulVec, ← mulVec_mulVec, ← vecAt_basis v' k w, ← vecAt_coe, mat, mat,
        archEmbed_apply, archEmbed_apply, map_toMatrix_mulVec_vecAt, map_toMatrix_mulVec_vecAt,
        ← vecAt_coe]
      exact congrArg (fun x => vecAt v x w) (hW (v' k))

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
