import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.HHInt
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTrm
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CoveringOfTransferenceVariant
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def rho0 : ℝ := Real.sqrt (finrank ℚ D.host.E) * D.host.rdE

theorem one_le_rdE : 1 ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow _ (by positivity)
  have h : (NumberField.discr D.host.E) ≠ 0 := NumberField.discr_ne_zero D.host.E
  have h1 : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h
  have h2 : ((1 : ℤ) : ℝ) ≤ ((|NumberField.discr D.host.E| : ℤ) : ℝ) := by exact_mod_cast h1
  simpa [Int.cast_abs] using h2

theorem one_le_rho0 : 1 ≤ rho0 D := by
  unfold rho0
  have h1 : (1 : ℝ) ≤ finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
  have h2 : 1 ≤ Real.sqrt (finrank ℚ D.host.E) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1
  nlinarith [one_le_rdE D]

theorem norm_embS_eq (τ : D.what₂.Tau) (x : D.host.E) :
    ‖embS D τ x‖ = (Formalism.MainNotions.BesselShellMomentBounds.plOf D τ) x := rfl

def boxS : Set D.host.E := {x | ∀ τ, ‖embS D τ x‖ ≤ rho0 D}

theorem boxS_cover : ∀ x : D.host.E, ∃ a ∈ intS D, x + a ∈ boxS D := by
  intro x
  have hc : ∀ w : InfinitePlace D.host.E, w.IsComplex := by
    haveI := Formalism.MainNotions.BesselShellMomentBounds.instCM D
    exact fun w => NumberField.IsTotallyComplex.isComplex w
  obtain ⟨a, ha⟩ := Formalism.HermitianLatticeCounting.P.covering_of_transference D.host.E hc (fun w => - w.embedding x)
  refine ⟨(a : D.host.E), coe_mem_intS D a, fun τ => ?_⟩
  rw [norm_embS_eq, ← InfinitePlace.norm_embedding_eq]
  have := ha (Formalism.MainNotions.BesselShellMomentBounds.plOf D τ)
  rw [map_add, show (Formalism.MainNotions.BesselShellMomentBounds.plOf D τ).embedding x + (Formalism.MainNotions.BesselShellMomentBounds.plOf D τ).embedding (a : D.host.E) =
    -(-(Formalism.MainNotions.BesselShellMomentBounds.plOf D τ).embedding x - (Formalism.MainNotions.BesselShellMomentBounds.plOf D τ).embedding (a : D.host.E)) by ring, norm_neg]
  exact this

theorem mem_boxS_one : (1 : D.host.E) ∈ boxS D := fun τ => by simpa using one_le_rho0 D

theorem mem_boxS_zero : (0 : D.host.E) ∈ boxS D := fun τ => by
  simpa using le_trans zero_le_one (one_le_rho0 D)

def liftO {N : ℕ} (n : Matrix (Fin N) (Fin N) D.host.E) (h : ∀ i j, n i j ∈ intS D) :
    Matrix (Fin N) (Fin N) (𝓞 D.host.E) :=
  fun i j => ⟨n i j, h i j⟩

theorem liftO_map {N : ℕ} (n : Matrix (Fin N) (Fin N) D.host.E) (h : ∀ i j, n i j ∈ intS D) :
    (liftO D n h).map (fun x => (x : D.host.E)) = n := by
  ext i j; rfl

theorem reduce_up {N : ℕ} (U : Matrix (Fin N) (Fin N) D.host.E) (hU : IsUpUni U) :
    ∃ B : Matrix (Fin N) (Fin N) (𝓞 D.host.E), (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = 1) ∧
      ∀ i j, (U * B.map (fun x => (x : D.host.E))) i j ∈ boxS D := by
  obtain ⟨n, hn1, hn0, hnO, hnF⟩ := Formalism.HermitianLatticeCounting.P.unitriangularReduction D.host.E (intS D) (boxS D) N U
    (boxS_cover D) (fun i => (hU i i).2 rfl) (fun i j h => (hU i j).1 h)
  refine ⟨liftO D n hnO, fun a b h => Subtype.ext (hn0 a b h), fun a => Subtype.ext (hn1 a), ?_⟩
  rw [liftO_map]
  have hnU : IsUpUni n := fun i j => ⟨hn0 i j, fun h => h ▸ hn1 i⟩
  have hP := rows_upUni_mul hU hnU
  intro i j
  rcases lt_trichotomy i j with h | h | h
  · exact hnF i j h
  · rw [(hP i j).2 h]; exact mem_boxS_one D
  · rw [(hP i j).1 h]; exact mem_boxS_zero D

theorem reduce_lo {N : ℕ} (L : Matrix (Fin N) (Fin N) D.host.E) (hL : IsLoUni L) :
    ∃ A : Matrix (Fin N) (Fin N) (𝓞 D.host.E), (∀ a b, a < b → A a b = 0) ∧ (∀ a, A a a = 1) ∧
      ∀ i j, (A.map (fun x => (x : D.host.E)) * L) i j ∈ boxS D := by
  have hU : IsUpUni L.transpose := fun i j => ⟨fun h => (hL j i).1 h, fun h => h ▸ (hL i i).2 rfl⟩
  obtain ⟨B, hB0, hB1, hBF⟩ := reduce_up D L.transpose hU
  refine ⟨B.transpose, fun a b h => hB0 b a h, fun a => hB1 a, fun i j => ?_⟩
  have e : (B.transpose.map (fun x => (x : D.host.E)) * L) =
      (L.transpose * B.map (fun x => (x : D.host.E))).transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map]
  rw [e]
  exact hBF j i

end Formalism.MainNotions.S.Pv.HH

end
