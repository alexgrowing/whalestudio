import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

namespace Formalism.BasicNotions

open NumberField

section gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem HSpace.pos_of_isomEmb (A B : HSpace E) (ι : A.V →ₗ[E] B.V) (hι : HSpace.IsIsomEmb A B ι)
    (hA : A.SigOK) (hB : B.SigOK) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hdef : A.sig τ = (A.rank, 0) ∨ A.sig τ = (0, A.rank)) (hlt : (B.sig τ).2 < A.rank) :
    A.sig τ = (A.rank, 0) := by
  rcases hdef with h | h
  · exact h
  · exfalso
    have hw : (Matrix.of fun i j => B.hT (ι (A.frame i)) (ι (A.frame j))) = A.gram := by
      ext i j; exact hι _ _
    have hsA := hA τ
    rw [h, ← hw] at hsA
    have key := (sig_family B τ hτ _ hsA (hB τ)).2
    have hs := sig_sum B hB τ
    simp only at key
    omega

theorem HSpace.frame_of_pos (S : HSpace E) (σ : E →+* ℂ)
    (hσ : ∀ a, σ (star a) = (starRingEnd ℂ) (σ a)) (h : Formalism.UG.HasSignature (S.gram.map σ) S.rank 0) :
    ∃ Y : Matrix (Fin S.rank) (Fin S.rank) ℂ, IsUnit Y.det ∧
      ∀ y : S.V, ∑ i, ‖(Y.mulVec fun j => σ (S.frame.repr y j)) i‖ ^ 2 = (σ (S.hT y y)).re := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq S.rank 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  set Pm : Matrix (Fin S.rank ⊕ Fin 0) (Fin S.rank ⊕ Fin 0) ℂ := P.val with hPm
  set Qm : Matrix (Fin S.rank ⊕ Fin 0) (Fin S.rank ⊕ Fin 0) ℂ := (P⁻¹).val with hQm
  have hPQ : Pm * Qm = 1 := by rw [hPm, hQm, ← Units.val_mul, mul_inv_cancel]; rfl
  have hcT : Formalism.UG.cT (starRingEnd ℂ) Pm = Pm.conjTranspose := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  set G : Matrix (Fin S.rank) (Fin S.rank) ℂ := S.gram.map σ with hG
  have hGr : G.reindex e e = Qm.conjTranspose * Qm := by
    have h1 : Qm.conjTranspose * (Pm.conjTranspose * G.reindex e e * Pm) * Qm = Qm.conjTranspose * Qm := by
      rw [hP, Matrix.mul_one]
    have h2 : Qm.conjTranspose * Pm.conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
    rw [← h1]
    calc G.reindex e e = (Qm.conjTranspose * Pm.conjTranspose) * G.reindex e e * (Pm * Qm) := by
          rw [h2, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  let Y : Matrix (Fin S.rank) (Fin S.rank) ℂ := Qm.submatrix e e
  have hGY : G = Y.conjTranspose * Y := by
    have : G = (G.reindex e e).submatrix e e := by ext i j; simp
    rw [this, hGr]
    ext i j
    simp only [Y, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact (Equiv.sum_comp e _).symm
  refine ⟨Y, ?_, fun y => ?_⟩
  · have : Y.det = Qm.det := Matrix.det_submatrix_equiv_self e Qm
    rw [this]
    exact (Matrix.isUnit_iff_isUnit_det _).mp ⟨P⁻¹, rfl⟩
  · set z : Fin S.rank → ℂ := fun j => σ (S.frame.repr y j) with hz
    have h1 : ∑ i, ‖(Y.mulVec z) i‖ ^ 2 = (star (Y.mulVec z) ⬝ᵥ Y.mulVec z).re := by
      simp [dotProduct, Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
    have h2 : star (Y.mulVec z) ⬝ᵥ Y.mulVec z = star z ⬝ᵥ G.mulVec z := by
      rw [hGY, Matrix.star_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star z)]
    have h3 : σ (S.hT y y) = star z ⬝ᵥ G.mulVec z := by
      have := LinearMap.sum_repr_mul_repr_mulₛₗ S.frame S.frame (B := S.hT) y y
      rw [← this, Finsupp.sum_fintype _ _ (by intro i; simp)]
      simp only [dotProduct, Matrix.mulVec, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_fintype _ _ (by intro j; simp), map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [smul_eq_mul, map_mul, RingHom.id_apply, hG, hz, Matrix.map_apply, HSpace.gram, Pi.star_apply]
      rw [starRingEnd_apply, hσ]
      simp only [starRingEnd_apply]
      ring
    rw [h1, h2, h3]

theorem HSpace.form_pos (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = (starRingEnd ℂ) (τ a)) (h : S.sig τ = (S.rank, 0)) (x : S.V) (hx : x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ τ (S.hT x x) = (c : ℂ) := by
  have hsig := hS τ
  rw [h] at hsig
  obtain ⟨Y, hY, hsum⟩ := S.frame_of_pos τ hτ hsig
  have hz : (fun j => τ (S.frame.repr x j)) ≠ 0 := by
    intro h0
    apply hx
    apply S.frame.repr.injective
    ext j
    have := congrFun h0 j
    simpa using this
  have hYz : Y.mulVec (fun j => τ (S.frame.repr x j)) ≠ 0 := by
    intro h0
    apply hz
    have hinj : Function.Injective Y.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det Y).mpr hY)
    exact hinj (by rw [h0, Matrix.mulVec_zero])
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hYz
  have hpos : 0 < (τ (S.hT x x)).re := by
    rw [← hsum x]
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, ?_⟩
    have : 0 < ‖(Y.mulVec fun j => τ (S.frame.repr x j)) i‖ := norm_pos_iff.mpr hi
    positivity
  have hre : τ (S.hT x x) = starRingEnd ℂ (τ (S.hT x x)) := by
    rw [← hτ]
    congr 1
    exact ((S.herm.eq x x)).symm
  refine ⟨(τ (S.hT x x)).re, hpos, ?_⟩
  apply Complex.ext
  · simp
  · have := congrArg Complex.im hre
    simp only [Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

end gen

section spaces

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E]

theorem Spaces.X'_posDef (S : Spaces R F E) (hYm : ∀ τ : E →+* ℂ, (S.Y R.m).sig τ = sigYD R R.m) :
    S.X'.IsPosDef := by
  intro τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := S.cm.cmUnram.2.1 τ
  refine HSpace.pos_of_isomEmb S.X' (S.Y R.m) S.eYm.toLinearMap S.eYm_isom S.X'_sig (S.Y_sig R.m) τ hτ
    ((factXmDef R F S).1 τ) ?_
  rw [hYm τ, S.X'_rank]
  simp only [sigYD, Nat.sub_self, Nat.zero_div]
  unfold Ranks.rankX' Ranks.r
  have := R.k_ge
  omega

theorem Spaces.X_posDef (S : Spaces R F E)
    (hY : ∀ j, j ≤ R.m → ∀ τ : E →+* ℂ, (S.Y j).sig τ = sigYD R j) (j : ℕ) (hj : j ≤ R.m) :
    (S.X j).IsPosDef := by
  intro τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := S.cm.cmUnram.2.1 τ
  rcases Nat.lt_or_ge j R.m with hjm | hjm
  · refine HSpace.pos_of_isomEmb (S.X j) (S.Y j) (S.iXY j) (S.iXY_isom j hjm) (S.X_sig j) (S.Y_sig j) τ hτ
      (S.X_def j hj τ) ?_
    rw [hY j hj τ, S.X_rank j hj]
    simp only [sigYD, Ranks.N]
    have h1 := R.m_add_three_le_k
    have h2 : (R.m - j) / 2 < R.k := by omega
    exact lt_of_lt_of_le h2 (Nat.le_add_right _ _)
  · have hjm' : j = R.m := le_antisymm hj hjm
    subst hjm'
    have hX' := Spaces.X'_posDef S (hY R.m le_rfl) τ
    rw [S.X'_rank] at hX'
    rw [S.X_rank R.m le_rfl]
    exact ((factXmDef R F S).2.2 τ).2 hX'

theorem Spaces.X_form_pos (S : Spaces R F E)
    (hY : ∀ j, j ≤ R.m → ∀ τ : E →+* ℂ, (S.Y j).sig τ = sigYD R j) (j : ℕ) (hj : j ≤ R.m)
    (τ : E →+* ℂ) (x : (S.X j).V) (hx : x ≠ 0) : ∃ c : ℝ, 0 < c ∧ τ ((S.X j).hT x x) = (c : ℂ) :=
  HSpace.form_pos (S.X j) (S.X_sig j) τ (S.cm.cmUnram.2.1 τ) (S.X_posDef hY j hj τ) x hx

end spaces

namespace D7

variable (D : D7)

theorem X_posDef (j : ℕ) (hj : j ≤ D.R.m) : letI := D.host.cmStar; (D.sp.X j).IsPosDef :=
  letI := D.host.cmStar; D.sp.X_posDef D.Y_sigval j hj

theorem X'_posDef : letI := D.host.cmStar; D.sp.X'.IsPosDef :=
  letI := D.host.cmStar; D.sp.X'_posDef (D.Y_sigval D.R.m le_rfl)

theorem X_form_pos (j : ℕ) (hj : j ≤ D.R.m) (τ : D.host.E →+* ℂ) :
    letI := D.host.cmStar; ∀ x : (D.sp.X j).V, x ≠ 0 → ∃ c : ℝ, 0 < c ∧ τ ((D.sp.X j).hT x x) = (c : ℂ) :=
  letI := D.host.cmStar; fun x hx => D.sp.X_form_pos D.Y_sigval j hj τ x hx

end D7

end Formalism.BasicNotions

end
