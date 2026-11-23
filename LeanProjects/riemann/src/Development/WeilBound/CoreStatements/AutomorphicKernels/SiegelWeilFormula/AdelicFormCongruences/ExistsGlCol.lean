import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.MemRatVIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.UnipotentLeDiagonalStabiliser

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp PositivityTheory.SiegelWeilFormula.kfour

namespace PositivityTheory.SiegelWeilFormula.Afc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem not_herm_skew {B : Base F E} {m : ℕ} {A : Spc F E m} {r s r' s' : ℕ} (hm : 1 ≤ m)
    (hH : A.IsHerm σ B r s) (hS : A.IsSkew σ B r' s') : False := by
  have h0 : A.J = 0 := by
    ext i j
    have h1 := hH.herm i j
    have h2 := hS.skew i j
    rw [h1] at h2
    exact self_eq_neg.1 h2
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A', hA'⟩ := hH.sig w
  rw [h0, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul] at hA'
  rcases Nat.eq_zero_or_pos r with hr | hr
  · have hs : 0 < s := by omega
    have := congrFun (congrFun hA' (Sum.inr ⟨0, hs⟩)) (Sum.inr ⟨0, hs⟩)
    simp at this
  · have := congrFun (congrFun hA' (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
    simp at this

theorem eps_eq {d : SD σ} (L : LD d) {ε ε' : ℤˣ} (hε : FrameEq σ d.Y d.b ε) (hε' : FrameEq σ L.Y L.b ε') : ε = ε' := by
  have hσ := sigma_sigma_of_good d.ok.good
  have hnL : 1 ≤ L.n := L.ok.hn
  have key : ∀ (s : ℤ), (∀ i j, σ (d.Y.J j i) = (s : E) * d.Y.J i j) → (∀ i j, σ (L.Y.J j i) = (s : E) * L.Y.J i j) →
      ε = ε' := fun s h1 h2 =>
    Units.ext ((eps_of_sign hσ d.ok.hn hε s h1).trans (eps_of_sign hσ hnL hε' s h2).symm)
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩ <;> rcases L.ok.sign with ⟨hA', hY'⟩ | ⟨hA', hY'⟩
  · exact key (-1) (fun i j => by rw [hY]; simp) (fun i j => by rw [hY']; simp)
  · exact (not_herm_skew d.ok.hm hA hA').elim
  · exact (not_herm_skew d.ok.hm hA' hA).elim
  · exact key 1 (fun i j => by rw [hY]; simp) (fun i j => by rw [hY']; simp)

theorem mapc_mul {p q r : Type} [Fintype q] (X : Matrix p q (AE F E)) (Z : Matrix q r (AE F E)) :
    (X * Z).map (cA σ) = X.map (cA σ) * Z.map (cA σ) :=
  Matrix.map_mul (f := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E))

theorem cong_nCond (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {ε : ℤˣ} (P β : Matrix (Fin n) (Fin n) (AE F E))
    (hβ : β ∈ nCond σ n ε) : (P.map (cA σ))ᵀ * β * P ∈ nCond σ n ε := by
  have hβ' : βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ)) := hβ
  have hcc : ∀ z, cA σ (cA σ z) = z := GlobalTheory.EisBL.DoubledUnipotentRadical.cA_cA σ hσ
  have hPP : (P.map (cA σ)).map (cA σ) = P := by ext i j; simp [hcc]
  show ((P.map (cA σ))ᵀ * β * P)ᵀ = -((((ε : ℤ) : AE F E)) • ((P.map (cA σ))ᵀ * β * P).map (cA σ))
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hβ', mapc_mul, mapc_mul,
    Matrix.transpose_map, hPP]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem sub_nCond {N k : ℕ} {ε : ℤˣ} (e : Fin k → Fin N) (β : Matrix (Fin N) (Fin N) (AE F E))
    (hβ : β ∈ nCond σ N ε) : β.submatrix e e ∈ nCond σ k ε := by
  have hβ' : βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ)) := hβ
  show (β.submatrix e e)ᵀ = -((((ε : ℤ) : AE F E)) • (β.submatrix e e).map (cA σ))
  ext i j
  have := congrFun (congrFun hβ' (e i)) (e j)
  simpa [Matrix.transpose_apply, Matrix.submatrix_apply] using this

theorem exists_gl_col {n : ℕ} (v : Fin n → E) (hv : v ≠ 0) (i₀ : Fin n) : ∃ a : GL (Fin n) E, ∀ k, a.1 k i₀ = v k := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  let B : Matrix (Fin n) (Fin n) E := (1 : Matrix (Fin n) (Fin n) E).updateCol j v
  have hB : B.det = v j := by
    have := congrFun (Matrix.cramer_one (α := E) (n := Fin n) ▸ rfl : Matrix.cramer (1 : Matrix (Fin n) (Fin n) E) v = v) j
    rw [Matrix.cramer_apply] at this
    exact this
  let M := B.submatrix id (Equiv.swap i₀ j)
  have hM : M.det ≠ 0 := by
    rw [Matrix.det_permute', hB]
    exact mul_ne_zero (by simp) hj
  refine ⟨((Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hM)).unit, fun k => ?_⟩
  simp [M, B, Matrix.updateCol_self]

end PositivityTheory.SiegelWeilFormula.Afc

end
