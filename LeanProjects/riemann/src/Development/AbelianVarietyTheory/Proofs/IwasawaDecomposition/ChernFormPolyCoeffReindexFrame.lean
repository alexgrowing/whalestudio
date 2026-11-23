import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.ChernReindex

variable {n a b : ℕ}

theorem mdel_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.mdel (fun u => Matrix.reindex e e (H u)) z ξ = Matrix.reindex e e (GlobalTheory.HermFrame.mdel H z ξ) := by
  ext i j; rfl

theorem conn_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.conn (fun u => Matrix.reindex e e (H u)) z ξ = Matrix.reindex e e (GlobalTheory.HermFrame.conn H z ξ) := by
  rw [GlobalTheory.HermFrame.conn, GlobalTheory.HermFrame.conn, mdel_reindex, Matrix.transpose_reindex, Matrix.transpose_reindex,
    Matrix.inv_reindex, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]

theorem curv_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ η : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.curv (fun u => Matrix.reindex e e (H u)) z ξ η = Matrix.reindex e e (GlobalTheory.HermFrame.curv H z ξ η) := by
  unfold GlobalTheory.HermFrame.curv
  simp_rw [conn_reindex]
  ext i j; rfl

theorem curvPoly_reindex (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.GoodMetric.curvPoly (fun u => Matrix.reindex e e (F u)) v = Matrix.reindex e e (GlobalTheory.GoodMetric.curvPoly F v) := by
  refine Matrix.ext fun i j => ?_
  simp only [GlobalTheory.GoodMetric.curvPoly, curv_reindex]
  rfl

theorem charpolyRev_reindex {R : Type} [CommRing R] (e : Fin a ≃ Fin b) (M : Matrix (Fin a) (Fin a) R) :
    (Matrix.reindex e e M).charpolyRev = M.charpolyRev := by
  rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly, Matrix.charpoly_reindex]

theorem chernPoly_reindex : ∀ {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ), chernPoly (fun u => Matrix.reindex e e (F u)) v k = chernPoly F v k := by
  intro n a b e F v k
  rw [GlobalTheory.GoodMetric.chernPoly, GlobalTheory.GoodMetric.chernPoly, curvPoly_reindex,
    show -(Matrix.reindex e e (GlobalTheory.GoodMetric.curvPoly F v)) = Matrix.reindex e e (-GlobalTheory.GoodMetric.curvPoly F v) from by
      ext i j; rfl, charpolyRev_reindex]

end GlobalTheory.ChernReindex
