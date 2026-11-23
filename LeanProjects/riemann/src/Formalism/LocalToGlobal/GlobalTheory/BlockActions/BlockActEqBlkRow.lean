import Formalism.LocalToGlobal.GlobalTheory.BlockActions.MapBrTenL
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfClasses

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix

section Indep

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem blockAct_eq_blkRow (U : ι → Matrix (Fin n) (Fin n) ℂ) : Formalism.GradedWeylDivisibility.blockAct ℂ U = blkRow U := rfl

theorem isUnit_det_of_on (G o : Matrix (Fin n) (Fin n) ℂ) (h : oᴴ * G * o = 1) : IsUnit o.det := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h1
  have h2 : o.det * (oᴴ.det * G.det) = 1 := by rw [← h1]; ring
  exact ⟨Units.mkOfMulEqOne _ _ h2, rfl⟩

theorem unitary_of_two_on (G o1 o2 : Matrix (Fin n) (Fin n) ℂ) (h1 : o1ᴴ * G * o1 = 1) (h2 : o2ᴴ * G * o2 = 1) :
    (o1⁻¹ * o2) * (o1⁻¹ * o2)ᴴ = 1 ∧ ‖(o1⁻¹ * o2).det‖ = 1 ∧ o2 = o1 * (o1⁻¹ * o2) := by
  have hu1 := isUnit_det_of_on _ _ h1
  have hG : G = (o1ᴴ)⁻¹ * o1⁻¹ := Formalism.L2.Col.eq_of_frame _ _ h1
  have hUU : (o1⁻¹ * o2)ᴴ * (o1⁻¹ * o2) = 1 := by
    have e : (o1⁻¹ * o2)ᴴ * (o1⁻¹ * o2) = o2ᴴ * ((o1ᴴ)⁻¹ * o1⁻¹) * o2 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
      simp only [Matrix.mul_assoc]
    rw [e, ← hG, h2]
  refine ⟨mul_eq_one_comm.1 hUU, ?_, ?_⟩
  · have h := congrArg Matrix.det hUU
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    have h' : ‖(o1⁻¹ * o2).det‖ ^ 2 = 1 := by
      have := congrArg (fun z : ℂ => ‖z‖) h
      simp only [norm_mul, norm_star, norm_one] at this
      rw [sq]; exact this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h'
  · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.one_mul]

theorem term_frame_indep (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) ℂ) (k : ι → ℤ)
    (o1 o2 : ι → Matrix (Fin n) (Fin n) ℂ) (h1 : ∀ τ, (o1 τ)ᴴ * G τ * o1 τ = 1) (h2 : ∀ τ, (o2 τ)ᴴ * G τ * o2 τ = 1)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    (∏ τ, ‖(o1 τ).det‖ ^ (2 * k τ)) * (Formalism.L2.Forms.nfAll lam (subP o1 P) (subP o1 P)).re =
      (∏ τ, ‖(o2 τ).det‖ ^ (2 * k τ)) * (Formalism.L2.Forms.nfAll lam (subP o2 P) (subP o2 P)).re := by
  have hU := fun τ => unitary_of_two_on (G τ) (o1 τ) (o2 τ) (h1 τ) (h2 τ)
  have hc : blkRow (fun τ => (o1 τ)⁻¹ * o2 τ) (blkRow o1 P) = blkRow o2 P := by
    rw [blkRow_comp]
    have e : (fun τ => o1 τ * ((o1 τ)⁻¹ * o2 τ)) = o2 := funext fun τ => ((hU τ).2.2).symm
    rw [e]
  have hsub : subP o2 P = blkRow (fun τ => (o1 τ)⁻¹ * o2 τ) (subP o1 P) := hc.symm
  have hdet : ∀ τ, ‖(o2 τ).det‖ = ‖(o1 τ).det‖ := fun τ => by
    have e := congrArg Matrix.det (hU τ).2.2
    rw [Matrix.det_mul] at e
    rw [e, norm_mul, (hU τ).2.1, mul_one]
  have hn : Formalism.L2.Forms.nfAll lam (subP o2 P) (subP o2 P) = Formalism.L2.Forms.nfAll lam (subP o1 P) (subP o1 P) := by
    rw [hsub, ← blockAct_eq_blkRow]
    exact Formalism.L2.Col.nfAll_blockAct lam _ (fun τ => (hU τ).1) _ _
  rw [hn]
  congr 1
  exact Finset.prod_congr rfl (fun τ _ => by rw [hdet τ])

end Indep

section At

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem frame_on_at (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (ι : D.host.E →+* ℂ)
    (o' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) (ho : o'ᴴ * (gramP D).map ι * o' = 1) :
    (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map ι *
        (bZ u Tf.til.z0).map ι * dOT u o')ᴴ * (gramN D D.R.m le_rfl).map ι *
      (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map ι *
        (bZ u Tf.til.z0).map ι * dOT u o') = 1 := by
  have hga : (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map ι)ᴴ *
      (gramN D D.R.m le_rfl).map ι * ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map ι =
      (gramN D D.R.m le_rfl).map ι := by
    have h := ((Tf.til.ga c)⁻¹).2
    rw [InvMemClass.coe_inv] at h
    have h' : (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map
        (sigD D : D.host.E →+* D.host.E))ᵀ * gramN D D.R.m le_rfl *
        ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) = gramN D D.R.m le_rfl := h
    have h2 := congrArg (fun X => X.map ι) h'
    simp only [Matrix.map_mul] at h2
    rw [map_cT_at] at h2
    exact h2
  have hbZ : ((bZ u Tf.til.z0).map ι)ᴴ * (gramN D D.R.m le_rfl).map ι * (bZ u Tf.til.z0).map ι =
      Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks ((gramP D).map ι) 0 0
        (Matrix.of fun _ _ => ((D.mem u).A.T : ℂ)⁻¹)) := by
    have h := gram_bZ (u := u) Tf.til.z0 Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    have h2 := congrArg (fun X => X.map ι) h
    simp only [Matrix.map_mul] at h2
    rw [map_cT_at] at h2
    rw [h2, Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    congr 2
    ext i j
    simp [map_inv₀, map_natCast]
  have e : ∀ (X Y Z G : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ),
      (X * Y * Z)ᴴ * G * (X * Y * Z) = Zᴴ * (Yᴴ * (Xᴴ * G * X) * Y) * Z := by
    intro X Y Z G
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hga, hbZ, dOT_on _ _ ho]

end At

end Formalism.L2.GlobalTheoryTheory.Br
