import Formalism.LocalToGlobal.GlobalTheory.GL4.PMsShort

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Matrix

section CSMat

variable {ι : Type} [Fintype ι]

theorem cs_dot (u v : ι → ℂ) : ‖star u ⬝ᵥ v‖ ^ 2 ≤ ‖star u ⬝ᵥ u‖ * ‖star v ⬝ᵥ v‖ := by
  have hgen : ∀ a b : ι → ℂ, star a ⬝ᵥ b =
      inner ℂ (WithLp.toLp 2 a : EuclideanSpace ℂ ι) (WithLp.toLp 2 b : EuclideanSpace ℂ ι) := by
    intro a b
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [hgen u v, hgen u u, hgen v v, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  set x : EuclideanSpace ℂ ι := WithLp.toLp 2 u
  set y : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have h := norm_inner_le_norm (𝕜 := ℂ) x y
  simp only [norm_pow, RCLike.norm_ofReal, abs_norm, Complex.norm_real, norm_norm]
  calc _ ≤ (‖x‖ * ‖y‖) ^ 2 := by gcongr
    _ = _ := by ring

theorem cs_factor (Q : Matrix ι ι ℂ) (s : ℂ) (hs : ‖s‖ = 1) (a b : ι → ℂ) :
    ‖star a ⬝ᵥ (s • (Qᴴ * Q)) *ᵥ b‖ ^ 2 ≤
      ‖star a ⬝ᵥ (s • (Qᴴ * Q)) *ᵥ a‖ * ‖star b ⬝ᵥ (s • (Qᴴ * Q)) *ᵥ b‖ := by
  have key : ∀ x y : ι → ℂ,
      star x ⬝ᵥ (s • (Qᴴ * Q)) *ᵥ y = s * (star (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y)) := by
    intro x y
    rw [smul_mulVec, dotProduct_smul, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec,
      smul_eq_mul]
  simp only [key, norm_mul, hs, one_mul]
  exact cs_dot _ _

end CSMat

theorem cT_eq_conjTranspose {m p : Type} (M : Matrix m p ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT, conjTranspose_apply]

theorem factor_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (p q : ℕ) (h : Formalism.UG.HasSignature G p q)
    (hpq : q = 0 ∨ p = 0) :
    ∃ (e : Fin n ≃ Fin p ⊕ Fin q) (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (s : ℂ),
      ‖s‖ = 1 ∧ G.reindex e e = s • (Qᴴ * Q) := by
  obtain ⟨e, P, hP⟩ := h
  rw [cT_eq_conjTranspose] at hP
  have h1 : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
      ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ = 1 := by
    rw [← conjTranspose_mul, h1, conjTranspose_one]
  have hM : G.reindex e e = ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ *
      Formalism.UG.Jpq p q * ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
    rw [← hP]
    calc G.reindex e e = (((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ *
          (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ) * G.reindex e e *
          ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
            ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) := by
          rw [h2, h1, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rcases hpq with rfl | rfl
  · refine ⟨e, ((P⁻¹ : GL (Fin p ⊕ Fin 0) ℂ) : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ), 1, by simp, ?_⟩
    have hJ : Formalism.UG.Jpq p 0 = 1 := by
      ext (i | i) (j | j)
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
      · exact i.elim0
      · exact i.elim0
    rw [hM, hJ, Matrix.mul_one, one_smul]
  · refine ⟨e, ((P⁻¹ : GL (Fin 0 ⊕ Fin q) ℂ) : Matrix (Fin 0 ⊕ Fin q) (Fin 0 ⊕ Fin q) ℂ), -1, by simp, ?_⟩
    have hJ : Formalism.UG.Jpq 0 q = -1 := by
      ext (i | i) (j | j)
      · exact i.elim0
      · exact i.elim0
      · exact j.elim0
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
    rw [hM, hJ, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, neg_one_smul]

section CSSpace

open Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_expand (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * (S.gram i j * S.frame.repr y j) := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, HSpace.gram, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem phi_hT (S : HSpace E) (φ : E →+* ℂ) (hstar : ∀ a, φ (star a) = star (φ a)) (x y : S.V) :
    φ (S.hT x y) = star (fun i => φ (S.frame.repr x i)) ⬝ᵥ (S.gram.map φ) *ᵥ (fun j => φ (S.frame.repr y j)) := by
  rw [hT_expand]
  simp only [dotProduct, mulVec, Matrix.map_apply, Pi.star_apply, map_sum, map_mul, hstar,
    Finset.mul_sum]

theorem dot_reindex {m ι : Type} [Fintype m] [Fintype ι] (e : m ≃ ι) (G : Matrix m m ℂ) (a b : m → ℂ) :
    star (a ∘ e.symm) ⬝ᵥ (G.reindex e e) *ᵥ (b ∘ e.symm) = star a ⬝ᵥ G *ᵥ b := by
  rw [reindex_apply, submatrix_mulVec_equiv]
  have hb : (b ∘ e.symm) ∘ e.symm.symm = b := by
    funext x
    simp
  rw [hb]
  simp only [dotProduct, Function.comp_apply, Pi.star_apply]
  exact Equiv.sum_comp e.symm (fun i => star (a i) * (G *ᵥ b) i)

theorem csAt_of_definite (S : HSpace E) (hstar : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hdef : S.IsDefinite) : CSAt S := by
  intro φ x y
  obtain ⟨e, Q, s, hs, hG⟩ := factor_of_sig (S.gram.map φ) (S.sig φ).1 (S.sig φ).2 (hsig φ)
    (by rcases hdef φ with h | h <;> simp [h])
  simp only [phi_hT S φ (hstar φ)]
  rw [← dot_reindex e, ← dot_reindex e, ← dot_reindex e, hG]
  exact cs_factor Q s hs _ _

theorem csAt_of_isomEmb (S S' : HSpace E) (ι : S.V →ₗ[E] S'.V) (hι : HSpace.IsIsomEmb S S' ι) (h : CSAt S') :
    CSAt S := by
  intro φ x y
  rw [← hι x y, ← hι x x, ← hι y y]
  exact h φ (ι x) (ι y)

end CSSpace

section CSRecord

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem host_star (D : D7) (φ : D.host.E →+* ℂ) (a : D.host.E) : φ (star a) = star (φ a) := by
  exact @NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ _ D.host.isCMField_hostE _ φ a

theorem csAt_X (D : D7) (i : ℕ) (hi : i ≤ D.R.m) : CSAt (D.sp.X i) :=
  csAt_of_definite (D.sp.X i) (host_star D) (D.sp.X_sig i) (D.sp.X_def i hi)

theorem csAt_X' (D : D7) : CSAt D.sp.X' :=
  csAt_of_isomEmb D.sp.X' (D.sp.X D.R.m) D.sp.iX' D.sp.iX'_isom (csAt_X D D.R.m le_rfl)

def FrameCoordAt (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (S : HSpace D.host.E) (q n : ℕ) : Prop :=
  ShortFrame S q (msRho D u C₀ n) ∧ CoordCount S q (msRho D u C₀ n) (coordinateLogBound D u C₀ n)

theorem msCount_of_frames (D : D7) (C₀ : ℝ) (hC : 3 ≤ C₀)
    (h : ∀ u : D.what₂.Word,
      (∀ i ≤ D.R.m, FrameCoordAt D u C₀ (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (D.R.N i)) ∧
      FrameCoordAt D u C₀ D.sp.X' 1 (D.R.N D.R.m - 1)) : MsCount D C₀ :=
  msCount_of_short D C₀ hC fun u =>
    ⟨fun i hi => ⟨((h u).1 i hi).1, csAt_X D i hi, ((h u).1 i hi).2⟩, ⟨(h u).2.1, csAt_X' D, (h u).2.2⟩⟩

theorem Link1F_of_frames
    (h : ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), (∀ (x : ℝ) (i : Fm.Ix x), Formalism.L2.Herm.FullTied (Fm.D x i)) →
      Transference → ∃ C₀ : ℝ, 3 ≤ C₀ ∧ Formalism.MainNotions.flipTwoThree.fam0 Fm fun D => ∀ u : D.what₂.Word,
        (∀ i ≤ D.R.m, FrameCoordAt D u C₀ (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (D.R.N i)) ∧
        FrameCoordAt D u C₀ D.sp.X' 1 (D.R.N D.R.m - 1)) : Link1F :=
  Link1F_of_count fun eps Fm hH hT => by
    obtain ⟨C₀, hC, x0, h0⟩ := h eps Fm hH hT
    exact ⟨C₀, by linarith, x0, fun x hx hx1 i => msCount_of_frames _ C₀ hC (h0 x hx hx1 i)⟩

end CSRecord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
