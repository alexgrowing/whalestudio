import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellVal

section Blocks

variable {R : Type} [CommRing R] {n r t : ℕ} (hn : r + t = n)

theorem block_mul₂ (a a' : Matrix (Fin r) (Fin r) R) (b b' : Matrix (Fin r) (Fin t) R)
    (c c' : Matrix (Fin t) (Fin r) R) (d d' : Matrix (Fin t) (Fin t) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one : bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 1 = 1 := by
  simp only [bl]
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrix_zero : bl hn (0 : Matrix (Fin r) (Fin r) R) 0 0 0 = 0 := by
  simp only [bl, Matrix.fromBlocks_zero]
  rfl

theorem det_bl_unip (y : Matrix (Fin r) (Fin t) R) : (bl hn 1 y 0 1).det = 1 := by
  simp only [bl]
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem trace_bl_last (b : Matrix (Fin t) (Fin t) R) (Z : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (bl hn 0 0 0 b * Z) =
      Matrix.trace (b * Z.submatrix (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr)
        (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr)) := by
  set e := finSumFinEquiv.trans (finCongr hn) with he
  have h1 : Z = (Matrix.fromBlocks (Z.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)) (Z.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr))
      (Z.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)) (Z.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr))).submatrix e.symm e.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp
  conv_lhs => rw [h1]
  simp only [bl, ← he]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  rw [Equiv.sum_comp e.symm (fun s => Matrix.fromBlocks _ _ _ _ s s), Fintype.sum_sum_type]
  simp

end Blocks

section Frames

variable {D : D7} {a n r t : ℕ} (hn : r + t = n)

theorem jn_mul_unip (x : Mx D a r) (y : Mx D r t) :
    (HMul.hMul (jn hn x 0) (bl hn 1 y 0 1) : Mx D a n) = jn hn x (mm x y) := by
  simp only [jn, bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp [mm]

theorem trace_inner_jn (V : HSp D) (b : Mx D t t) (x : Mx D V.rank r) (v : Mx D V.rank t) :
    Matrix.trace (HMul.hMul (bl hn 0 0 0 b) (GlobalTheory.StdUnn.inner V (jn hn x v) (jn hn x v)) : Mx D n n) =
      Matrix.trace (mm b (ip V v v)) := by
  rw [trace_bl_last]
  congr 1
  have h : (GlobalTheory.StdUnn.inner V (jn hn x v) (jn hn x v)).submatrix (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr)
      (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr) = ip V v v := by
    ext i j
    simp [GlobalTheory.StdUnn.inner, ip, mm, jn, adj, Matrix.mul_apply]
  rw [h]

def unipGL (y : Mx D r t) : GL (Fin n) (AE D) where
  val := bl hn 1 y 0 1
  inv := bl hn 1 (-y) 0 1
  val_inv := by rw [block_mul₂]; simpa using blockRowSubstitution_one hn
  inv_val := by rw [block_mul₂]; simpa using blockRowSubstitution_one hn

theorem det_unipGL (y : Mx D r t) :
    Matrix.GeneralLinearGroup.det (unipGL hn y : GL (Fin n) (AE D)) = (1 : (AE D)ˣ) :=
  Units.ext (det_bl_unip hn y)

theorem adj_bl_unip_neg (y : Mx D r t) :
    adj (bl hn (1 : Mx D r r) (-y) 0 (1 : Mx D t t)) = bl hn (1 : Mx D r r) 0 (-adj y) (1 : Mx D t t) := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [adj, bl, Matrix.one_apply, apply_ite (cA D)]
  all_goals by_cases h : i = j <;> simp [h, eq_comm]

end Frames

theorem weil_translate_frame {D : D7} {n r t : ℕ} (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (V : HSp D)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ)
    (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)}
    (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕)
    {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (Φ : schwartzA θ V.rank n)
    {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t) (y : Mx D r t)
    (x : Mx D V.rank r) :
    (ω (M.sh y * M.emb (w * nb b) * 1) Φ).1 (jn hn x 0) =
      ∫ v, pch ψ b.1 (ip V v v) * Φ.1 (jn hn x v) * ψ (trA (Matrix.trace (ip V (mm x y) v))) ∂μt := by
  have e1 : ω (M.sh y * M.emb (w * nb b) * 1) Φ = ω (M.sh y) (ω (M.emb w) (ω (M.emb (nb b)) Φ)) := by
    simp only [mul_one, map_mul, Module.End.mul_apply]
  have hdet := det_unipGL hn y
  have hsh : mat (M.sh y) = blk4 (unipGL hn y).1 0 0 (adj ((unipGL hn y)⁻¹).1) := by
    rw [M.sh_mat]
    have : ((unipGL hn y)⁻¹).1 = bl hn 1 (-y) 0 1 := rfl
    rw [this, adj_bl_unip_neg]
    rfl
  have hemb : mat (M.emb (nb b)) = blk4 1 (bl hn 0 0 0 b.1) 0 1 := by
    rw [M.emb_mat (nb b) 1 b.1 0 1 (hnb b), blockRowSubstitution_one, blockMatrix_zero]
  rw [e1, hω.levi (M.sh y) (unipGL hn y) hsh, hdet]
  have hpow : npow (absA D 1) ((V.rank : ℂ) / 2) = 1 := by simp [npow]
  rw [map_one, hpow]
  simp only [Circle.coe_one, one_mul]
  have hj : (HMul.hMul (jn hn x 0) (unipGL hn y).1 : Mx D V.rank n) = jn hn x (mm x y) := jn_mul_unip hn x y
  rw [hj, (hP D n r t hn M V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr μt hμr hμt (ω (M.emb (nb b)) Φ)).2.2 w hw x (mm x y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [hω.unip (M.emb (nb b)) _ hemb, trace_inner_jn]
  rfl

end GlobalTheory.CompanionTheory.CellVal

end
