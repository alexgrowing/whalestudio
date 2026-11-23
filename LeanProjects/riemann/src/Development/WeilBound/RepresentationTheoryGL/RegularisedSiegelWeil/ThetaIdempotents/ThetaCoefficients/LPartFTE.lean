import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFTD

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar GlobalTheory.CompanionTheory.ThetaPoisson

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {D : D7} {n r t : ℕ}

theorem mem_gf_of {γ : G D n} (g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (hu : IsUnit g.det)
    (hU : IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (PositivityTheory.GramSchwartzFunctions.EC.Jm D.host.E n) g)
    (h : mat γ = g.map (incA D)) : γ ∈ GF D n := by
  obtain ⟨γ₀, h0, e⟩ := (GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn D n).2.1 g hu hU
  rwa [mat_injective' (e.trans h.symm)] at h0

theorem one_sub_bl' {R : Type} [CommRing R] (hn : r + t = n) :
    1 - bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 0 = bl hn 0 0 0 1 := by
  rw [← blockRowSubstitution_one hn, sub_eq_iff_eq_add, bl_add]; simp

theorem mat_w (hn : r + t = n) (M : Maps D hn) : mat M.w = (wr D.host.E n r).map (incA D) := by
  have hm : (-1 : Matrix (Fin r) (Fin r) D.host.E).map (incA D) = -1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [M.w_mat, wr, eId_eq hn, block_matrix_map, one_sub_bl', block_neg]
  simp [block_map, hm]

theorem mat_emb (hn : r + t = n) (M : Maps D hn) (w : G D t) (hw : IsW w) :
    mat (M.emb w) = (wE (bl hn (0 : Matrix (Fin r) (Fin r) D.host.E) 0 0 1)).map (incA D) := by
  have hm : (-1 : Matrix (Fin t) (Fin t) D.host.E).map (incA D) = -1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [M.emb_mat w 0 1 (-1) 0 hw, wE, one_sub_bl, block_neg, block_matrix_map]
  simp [block_map, hm]

theorem mat_emb' (hn : r + t = n) (M : Maps D hn) (w : G D t) (hw : IsW w) :
    mat (M.emb w) = blk4 (bl hn 1 0 0 0) (bl hn 0 0 0 1) (bl hn 0 0 0 (-1)) (bl hn 1 0 0 0) :=
  M.emb_mat w 0 1 (-1) 0 hw

theorem adj_Pm (hn : r + t = n) : adj ((Pm D.host.E hn).map (incA D)) = (Pm D.host.E hn)ᵀ.map (incA D) := by
  have h1 : (Pm D.host.E hn).map (incA D) = (1 : Mx D n n).submatrix (πe hn) id := by
    rw [Pm, ← Matrix.submatrix_map, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [adj, Matrix.transpose_map, h1, ← Matrix.submatrix_map, Matrix.map_one _ (map_zero _) (map_one _)]

def uP (D : D7) (hn : r + t = n) : GL (Fin n) D.host.E := ⟨(Pm D.host.E hn)ᵀ, Pm D.host.E hn, T_mul_Pm hn, Pm_mul_alt hn⟩

theorem mat_gQ {γ : G D n} (hn : r + t = n) (h : mat γ = (blk4 (Pm D.host.E hn)ᵀ 0 0 (Pm D.host.E hn)ᵀ).map (incA D)) :
    mat γ = blk4 ((uP D hn).1.map (incA D)) 0 0 (adj (((uP D hn)⁻¹).1.map (incA D))) := by
  rw [h, block_matrix_map]
  show blk4 _ _ _ _ = blk4 _ _ _ (adj ((Pm D.host.E hn).map (incA D)))
  rw [adj_Pm]
  simp [uP]

def xz {m : ℕ} (X : Mx D m n) : Mx D m (n + n) :=
  Matrix.of fun i k => Sum.elim (X i) (fun _ => (0 : AE D)) (finSumFinEquiv.symm k)

theorem xPart_xz {m : ℕ} (X : Mx D m n) : xPart (xz X) = X := by
  ext i j
  show Sum.elim (X i) (fun _ => (0 : AE D)) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem yPart_xz {m : ℕ} (X : Mx D m n) : yPart (xz X) = 0 := by
  ext i j
  show Sum.elim (X i) (fun _ => (0 : AE D)) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem heis_xz (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (X : Mx D V.rank n) (F : Mx D V.rank n → ℂ) :
    PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂ ψ V (xz X) F 0 = F X := by
  simp [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂, xPart_xz, yPart_xz, GlobalTheory.StdUnn.inner, halfTr]

theorem trace_inner_jn (V : HSp D) (hn : r + t = n) (x x' : Mx D V.rank r) (v v' : Mx D V.rank t) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (jn hn x v) (jn hn x' v')) = Matrix.trace (ip V x x') + Matrix.trace (ip V v v') := by
  simp only [Matrix.trace, Matrix.diag, GlobalTheory.StdUnn.inner, ip, mm]
  rw [← (ee hn).sum_comp, Fintype.sum_sum_type]
  simp only [Matrix.mul_apply, adj, Matrix.transpose_apply, Matrix.map_apply, jn_ee, Matrix.fromCols_apply_inl,
    Matrix.fromCols_apply_inr]

theorem psi_ip_symm (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (x y : Mx D V.rank t) :
    ψ (trA (Matrix.trace (ip V x y))) = ψ (trA (Matrix.trace (ip V y x))) := by
  have hs := pairing_symm (n := t) (isHermND_gram V) ψ x y
  have e : ∀ a b : Mx D V.rank t, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ a b = ψ (trA (Matrix.trace (ip V a b))) :=
    fun a b => by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
      rfl
  rw [← e, ← e, hs]

theorem levi_zero {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω) (g : G D n) (u : GL (Fin n) D.host.E)
    (hg : mat g = blk4 (u.1.map (incA D)) 0 0 (adj ((u⁻¹).1.map (incA D)))) (F : schwartzA θ V.rank n) :
    (ω g F).1 0 = F.1 0 := by
  obtain ⟨-, hχ, -, -, hω⟩ := hS
  let a' : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) u
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det u) := by
    apply Units.ext
    simp [a', Matrix.GeneralLinearGroup.map]
    exact (RingHom.map_det _ _).symm
  have h1 : absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact absE_inclR _
  have h2 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact hχ.2 _
  have hinv : (a'⁻¹).1 = (u⁻¹).1.map (incA D) := by
    show ((Matrix.GeneralLinearGroup.map (incA D) u)⁻¹).1 = _
    rw [← map_inv]; rfl
  have hg' : mat g = blk4 a'.1 0 0 (adj (a'⁻¹).1) := by
    rw [hinv]; exact hg
  rw [hω.levi g a' hg' F, h1, h2]
  simp [npow]

end PositivityTheory.Rg.Rsw.L.LPartFT
