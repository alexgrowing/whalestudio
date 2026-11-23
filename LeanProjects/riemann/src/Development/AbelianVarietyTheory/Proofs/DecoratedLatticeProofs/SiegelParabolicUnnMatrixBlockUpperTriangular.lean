import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.LeftInvSect
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model
variable {D : D7} {n : ℕ}

theorem rat_mat {γ : G D n} (h : γ ∈ GF D n) :
    ∃ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) := by
  obtain ⟨x, -, hx⟩ := h
  exact ⟨x.1, (congrArg Units.val hx).symm⟩

theorem det_rat {γ : G D n} (h : γ ∈ GF D n) (a : GL (Fin n) (AE D)) (ha : blkA (mat γ) = a.1) :
    ∃ u : D.host.Eˣ, Matrix.GeneralLinearGroup.det a = Units.map (incA D).toMonoidHom u := by
  haveI : Nontrivial (AF D.host.F) := inferInstanceAs (Nontrivial (Ainf D.host.F × Af D.host.F))
  haveI : Nontrivial (AE D) := inferInstance
  obtain ⟨x, hx⟩ := rat_mat h
  have e : ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = incA D (blkA x).det := by
    rw [RingHom.map_det]
    change a.1.det = _
    rw [← ha, hx]; rfl
  have h0 : (blkA x).det ≠ 0 := fun h0 => Units.ne_zero _ (e.trans (by rw [h0, map_zero]))
  exact ⟨Units.mk0 _ h0, Units.ext e⟩

theorem siegelParabolicUnn_matrix_blockUpperTriangular {p : G D n} (hp : p ∈ P D n) : ∃ b d, mat p = blk4 (blkA (mat p)) b 0 d := by
  refine ⟨((mat p).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    ((mat p).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · exact lower_eq_zero hp i j
  · rfl

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : G D n) = 1 := rfl

theorem levi_mul_inv (a : GL (Fin n) (AE D)) :
    (blk4 a.1 0 0 (adj (a⁻¹).1) : Mx D (n + n) (n + n)) * blk4 (a⁻¹).1 0 0 (adj a.1) = 1 := by
  have h2 : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by rw [← adj_mul]; simp [adj_one]
  simp [submatrix_fromBlocks_mul, h2, block_matrix_one, -Matrix.coe_units_inv]

theorem exists_levi_unip {p : G D n} (hp : p ∈ P D n) (a : GL (Fin n) (AE D)) (ha' : blkA (mat p) = a.1) :
    ∃ (m u : G D n) (b : Mx D n n), p = m * u ∧ mat m = blk4 a.1 0 0 (adj (a⁻¹).1) ∧ mat u = blk4 1 b 0 1 := by
  obtain ⟨m, hm⟩ := exists_levi a
  obtain ⟨m', hm'⟩ := exists_levi a⁻¹
  obtain ⟨b, d, hb⟩ := siegelParabolicUnn_matrix_blockUpperTriangular hp
  rw [ha'] at hb
  rw [inv_inv] at hm'
  have hu : mat (m' * p) = blk4 1 ((a⁻¹).1 * b) 0 (adj a.1 * d) := by
    rw [mat_mul, hm', hb, submatrix_fromBlocks_mul]
    simp [-Matrix.coe_units_inv]
  have hd : (adj a.1 : Mx D n n) * d = 1 := by
    have h : adj (mat (m' * p)) * JR (AF D.host.F) (Jst D n) * mat (m' * p) = JR (AF D.host.F) (Jst D n) := (m' * p).2
    rw [JR_Jst, hu] at h
    generalize (adj a.1 : Mx D n n) * d = d' at h ⊢
    generalize (a⁻¹).1 * b = b' at h
    simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_one, adj_zero, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, mul_neg,
      neg_mul, neg_zero] at h
    exact (blockMatrixTwoByTwoFin_injective h).2.1
  have hmm : m * m' = 1 := mat_inj (by rw [mat_mul, mat_one, hm, hm', levi_mul_inv])
  refine ⟨m, m' * p, (a⁻¹).1 * b, by rw [← mul_assoc, hmm, one_mul], hm, by rw [hu, hd]⟩

theorem exists_blkA {p : G D n} (hp : p ∈ P D n) : ∃ a : GL (Fin n) (AE D), blkA (mat p) = a.1 :=
  ⟨levi (D := D) (n := n) ⟨p, hp⟩, rfl⟩

theorem height_inv (hI : ∀ g : G D n, ∃ p ∈ P D n, ∃ k ∈ K D n, g = p * k) {H : G D n → ℝ≥0} (hH : IsHeight H)
    {γ : G D n} (hp : γ ∈ P D n) (a : GL (Fin n) (AE D)) (ha : blkA (mat γ) = a.1)
    (h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1) (g : G D n) : H (γ * g) = H g := by
  obtain ⟨p, hp', k, hk, rfl⟩ := hI g
  obtain ⟨c, hc⟩ := exists_blkA hp'
  have e : blkA (mat (γ * p)) = (a * c).1 := by rw [blkA_mul hp', ha, hc, Units.val_mul]
  rw [← mul_assoc, hH _ ((P D n).mul_mem hp hp') (a * c) e k hk, hH p hp' c hc k hk, map_mul, map_mul, h1, one_mul]

theorem leftInv_sect : ∀ (D : D7) (n : ℕ), (∀ g : GlobalTheory.StdUnn.G D n, ∃ p ∈ GlobalTheory.StdUnn.P D n, ∃ k ∈ GlobalTheory.StdUnn.K D n, g = p * k) → ∀ (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : GlobalTheory.StdUnn.G D n →* Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n)), IsHeckeChar D χ → GlobalTheory.StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ H : GlobalTheory.StdUnn.G D n → ℝ≥0, GlobalTheory.StdUnn.IsHeight H → ∀ (Φ : GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n) (z : ℂ), GlobalTheory.AutomorphicL2Unitary.LeftInv (GlobalTheory.StdUnn.P D n ⊓ GlobalTheory.StdUnn.GF D n) (GlobalTheory.StdUnn.sect ω H Φ z) := by
  intro D n hI V ψ χ θ μ ω hχ hω H hH Φ z γ hγ g
  obtain ⟨hp, hr⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨a, ha⟩ := exists_blkA hp
  obtain ⟨u, hu⟩ := det_rat hr a ha
  have h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact absE_inclR u
  have h2 : χ (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact hχ.2 u
  have hHe : H (γ * g) = H g := height_inv hI hH hp a ha h1 g
  have hW : (ω (γ * g) Φ).1 0 = (ω g Φ).1 0 := by
    obtain ⟨m, v, b, e, hm, hv⟩ := exists_levi_unip hp a ha
    have e' : ω (γ * g) Φ = ω m (ω v (ω g Φ)) := by
      rw [e, map_mul, map_mul]; rfl
    have z1 : ∀ a : Mx D n n, ((0 : Mx D V.rank n) ⬝ a : Mx D V.rank n) = 0 := fun a => Matrix.zero_mul a
    have z2 : StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by rw [StdUnn.inner, adj_zero, Matrix.zero_mul]
    rw [e', hω.levi m _ hm, h1, h2, z1, hω.unip v b hv, z2]
    simp [halfTr, npow]
  simp only [sect, hHe, hW]

end GlobalTheory.StdUnn.LeftInvSect
