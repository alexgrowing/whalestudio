import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionNonsplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalIwasawaBlockTriangularStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeviElementExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicMatrixCoordinatesTriangularStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.IwFinFlag

theorem matrix_map_ringHom_add_smul_sandwich {n r : Type} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r] {A : Type} [CommRing A]
    (P Q Mi M : Matrix n n A) (X : Matrix n r A) (β b α αi : Matrix r r A) (hP : P = Q * Mi) (hβ : Q * X = X * β)
    (hba : β = b * α) (hm : M * X = X * α) (N : Matrix n n A) (hN : N = Mi * M) (e1 : N = 1) (hα : α * αi = 1) :
    P * X = X * b := by
  have hinv : Mi * X = X * αi := by
    calc Mi * X = Mi * X * (α * αi) := by rw [hα, Matrix.mul_one]
      _ = Mi * (M * X) * αi := by rw [hm]; simp only [Matrix.mul_assoc]
      _ = X * αi := by rw [← Matrix.mul_assoc, ← hN, e1, Matrix.one_mul]
  rw [hP, Matrix.mul_assoc, hinv, ← Matrix.mul_assoc, hβ, hba, Matrix.mul_assoc, Matrix.mul_assoc, hα, Matrix.mul_one]

theorem mat_mul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : HA R σ J) :
    (HA.mat R σ J (x * y)).1 = (HA.mat R σ J x).1 * (HA.mat R σ J y).1 := rfl

theorem mat_one {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : (HA.mat R σ J 1).1 = 1 := rfl

set_option maxHeartbeats 1000000 in

theorem iwasawa_minPar_fin : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ v (g : GLoc D.sp.cm.sig V.gram v), ∃ p ∈ PLoc Φ.flag0 v, ∃ k ∈ stabLoc D.sp.cm.sig V.gram L v, g = p * k := by
  intro D V Φ L a hG v g
  rcases (em (Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v)).elim (GlobalTheory.T.local_decomposition_split_place D V Φ L a hG v · g)
    (GlobalTheory.T.local_decomposition_nonsplit_place D V Φ L a hG v · g) with ⟨q, k, hk, rfl, β, hβ⟩
  obtain ⟨b, α, hb, hα, hα', rfl⟩ := GlobalTheory.T.local_iwasawa_block_triangular D v (wittIndex V) β
  obtain ⟨m, hm, hmα⟩ := GlobalTheory.T.integral_levi_element_exists D V Φ L a hG v α hα hα'
  have hg : q * k = (q * m⁻¹) * (m * k) := by rw [mul_assoc, inv_mul_cancel_left]
  have e1 : (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram (m⁻¹ * m)).1 = 1 := by rw [inv_mul_cancel]; exact mat_one _ _ _
  exact ⟨q * m⁻¹, GlobalTheory.T.parabolic_matrix_coordinates_triangular D V Φ v (q * m⁻¹) b.1 hb (matrix_map_ringHom_add_smul_sandwich _ _ _ _ _ _ b.1 α.1 (α⁻¹).1 (mat_mul _ _ _ _ _) hβ
    (Units.val_mul b α) hmα _ (mat_mul _ _ _ _ _) e1 α.mul_inv), m * k, mul_mem hm hk, hg⟩

end GlobalTheory.IwFinFlag

end
