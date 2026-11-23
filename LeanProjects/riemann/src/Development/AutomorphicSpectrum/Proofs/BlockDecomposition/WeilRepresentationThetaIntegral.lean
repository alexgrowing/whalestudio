import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WzFib

theorem inner_jn {D : D7} {n r t : ℕ} (hn : r + t = n) (V : HSp D) (x : Mx D V.rank r) :
    GlobalTheory.StdUnn.inner V (jn hn x (0 : Mx D V.rank t)) (jn hn x (0 : Mx D V.rank t)) =
      bl hn (GlobalTheory.StdUnn.inner V x x) 0 0 0 := by
  set e : Fin n ≃ Fin r ⊕ Fin t := (finSumFinEquiv.trans (finCongr hn)).symm with he
  have hX : jn hn x (0 : Mx D V.rank t) = (Matrix.fromCols x (0 : Mx D V.rank t)).submatrix id e := rfl
  have hadj : adj (jn hn x (0 : Mx D V.rank t)) =
      (Matrix.fromRows (adj x) (0 : Matrix (Fin t) (Fin V.rank) (AE D))).submatrix e id := by
    ext i k
    rw [hX]
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id]
    rcases e i with a | b
    · simp
    · simp
  have hG : (HMul.hMul (gA V) (jn hn x (0 : Mx D V.rank t)) : Mx D V.rank n) =
      (Matrix.fromCols (HMul.hMul (gA V) x : Mx D V.rank r) (0 : Mx D V.rank t)).submatrix id e := by
    ext i j
    rw [hX]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
    rcases e j with a | b
    · simp [Matrix.mul_apply]
    · simp
  unfold GlobalTheory.StdUnn.inner
  rw [hG, hadj, ← Matrix.submatrix_mul _ _ e id e Function.bijective_id, Matrix.fromRows_mul_fromCols]
  simp [bl, he]

theorem trace_bl {R : Type} [CommRing R] {n r t : ℕ} (hn : r + t = n) (a : Matrix (Fin r) (Fin r) R)
    (b : Matrix (Fin r) (Fin t) R) (c : Matrix (Fin t) (Fin r) R) (d : Matrix (Fin t) (Fin t) R) :
    Matrix.trace (bl hn a b c d) = Matrix.trace a + Matrix.trace d := by
  unfold bl
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  rw [Equiv.sum_comp (finSumFinEquiv.trans (finCongr hn)).symm (fun i => Matrix.fromBlocks a b c d i i),
    Fintype.sum_sum_type]
  simp

theorem trace_nzx {D : D7} {n r t : ℕ} (hn : r + t = n) (V : HSp D) (z : Mx D r r) (x : Mx D V.rank r) :
    Matrix.trace (HMul.hMul (bl hn z 0 (adj (0 : Mx D r t)) 0 : Mx D n n)
        (GlobalTheory.StdUnn.inner V (jn hn x (0 : Mx D V.rank t)) (jn hn x (0 : Mx D V.rank t))) : Mx D n n) =
      Matrix.trace (HMul.hMul z (GlobalTheory.StdUnn.inner V x x) : Mx D r r) := by
  have h0 : adj (0 : Mx D r t) = 0 := by
    ext i j
    simp [adj]
  rw [inner_jn, h0]
  have hm : (HMul.hMul (bl hn z 0 0 0 : Mx D n n) (bl hn (GlobalTheory.StdUnn.inner V x x) 0 0 0) : Mx D n n) =
      bl hn (HMul.hMul z (GlobalTheory.StdUnn.inner V x x) : Mx D r r) 0 0 0 := by
    unfold bl
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  rw [hm, trace_bl]
  simp

theorem conj_char {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (u : AF F) :
    conj (ψ u) = ψ (-u) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 u)]

theorem wz_eq_fib : ∀ {D : D7} {n r t : ℕ} (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω) {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (b₀ : HermE D r) {fib : Measure (Mx D V.rank r)} (hfib : IsFib ψ θ V b₀ μr m.lz fib) (Φ : schwartzA θ V.rank n) (g : G D n), Wz M m ψ b₀ (fun g => (ω g Φ).1 0) g = ∫ x, (ω g Φ).1 (jn hn x 0) ∂fib := by
  intro D n r t hP hn M m V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr hμr μt hμt b₀ fib hfib Φ g
  have hPF := hP D n r t hn M V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr μt hμr hμt
  rw [← (hfib.int _ (hPF (ω g Φ)).2.1).2]
  unfold Wz W
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show (ω (M.w * M.nzx z 0 * g) Φ).1 0 * conj (chz ψ b₀ z) = Jt ψ V μr _ z * ψ (-halfTr _)
  have e1 : ω (M.w * M.nzx z 0 * g) Φ = ω M.w (ω (M.nzx z 0) (ω g Φ)) := by
    simp only [map_mul, Module.End.mul_apply]
  rw [e1, (hPF (ω (M.nzx z 0) (ω g Φ))).1]
  unfold chz
  rw [conj_char hψ]
  congr 1
  unfold Jt
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show (ω (M.nzx z 0) (ω g Φ)).1 (jn hn x 0) = (ω g Φ).1 (jn hn x 0) * ψ (halfTr _)
  rw [hω.unip _ _ (M.nzx_mat z 0), trace_nzx, mul_comm]

end GlobalTheory.CompanionTheory.WzFib

end
