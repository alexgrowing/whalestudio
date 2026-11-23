import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.SelfDualLatticesOneOrbit

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Build

variable (p f : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF p f) O] {N r K : ℕ}

def phiS (N r K : ℕ) (s : ℤ) : WF p f →+* MvPolynomial (Fin N × Fin (r + K)) O := C.comp (psiO p f O s)

def FrobCong : Prop :=
  ∀ (s s' : ℤ), s ≤ s' → ∀ β : WF p f, ∃ τ : WF p f,
    (sigPow p f s β) ^ (p ^ (s' - s).toNat) - sigPow p f s' β = (p : WF p f) * τ

variable {p f O}

lemma phiS_cong (hF : FrobCong p f) (s s' : ℤ) (hs : s ≤ s') (β : WF p f) :
    ((p : ℕ) : MvPolynomial (Fin N × Fin (r + K)) O) ∣
      (phiS p f O N r K s β) ^ (p ^ (s' - s).toNat) - phiS p f O N r K s' β := by
  obtain ⟨τ, hτ⟩ := hF s s' hs β
  refine ⟨C (algebraMap (WF p f) O τ), ?_⟩
  have := congrArg (fun x => (C (algebraMap (WF p f) O x) : MvPolynomial (Fin N × Fin (r + K)) O)) hτ
  simpa [phiS, psiO] using this

lemma map_inv_one (φ : WF p f →+* MvPolynomial (Fin N × Fin (r + K)) O)
    (M M' : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f)) (h : M * M' = 1) : M.map φ * M'.map φ = 1 := by
  rw [← Matrix.map_mul, h]; exact Matrix.map_one _ (map_zero _) (map_one _)

lemma Lam_inv_one (φ : WF p f →+* MvPolynomial (Fin N × Fin (r + K)) O)
    (M M' : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f)) (h : M * M' = 1) :
    abelian₂ (M.map φ) * abelian₂ (M'.map φ) = 1 := by
  rw [← Lam_mul, map_inv_one φ M M' h, Lam_one]

def mkTS (hF : FrobCong p f) (S : UniformizedDVR p O) (hsq : S.SqP) (c : ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ)
    (pos : Fin N → ℤ) (ζ y : Fin N → Fin (r + K) → MvPolynomial (Fin N × Fin (r + K)) O)
    (M M' : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f)) (h1 : M * M' = 1) (h2 : M' * M = 1)
    (hw : ∀ (j : ℕ) (h : j < N), ((colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c ∧ 1 ≤ c) ∨
        (colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c ∧ ¬ 1 ≤ c)) →
      Matrix.vecMul (ζ ⟨j, h⟩) (M.map (phiS p f O N r K (pos ⟨j, h⟩))) = y ⟨j, h⟩)
    (hc : ∀ (j : ℕ) (h : j < N), ((colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c ∧ ¬ 1 ≤ c) ∨
        (colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c ∧ 1 ≤ c)) →
      Matrix.mulVec (M'.map (phiS p f O N r K (pos ⟨j, h⟩))) (ζ ⟨j, h⟩) = y ⟨j, h⟩) :
    TS p (C S.w : MvPolynomial (Fin N × Fin (r + K)) O) c mu pos ζ y where
  T := fun s Kv => Matrix.vecMul Kv (abelian₂ (M.map (phiS p f O N r K s)))
  step := by
    intro j h Kv
    unfold colStep
    split_ifs with a1 a2 a3 a4
    · rw [Lam_wedge, hw j h (Or.inl ⟨a1, a2⟩)]
    · rw [Lam_contr _ _ (map_inv_one _ M M' h1), hc j h (Or.inl ⟨a1, a2⟩)]
    · rw [Lam_contr _ _ (map_inv_one _ M M' h1), hc j h (Or.inr ⟨a3, a4⟩)]
    · rw [Lam_wedge, hw j h (Or.inr ⟨a3, a4⟩)]
    · rfl
  base := by
    intro s J hJ
    classical
    simp only [Matrix.vecMul, dotProduct]
    refine Finset.sum_eq_zero fun I _ => ?_
    unfold extOne
    by_cases hI : I = ∅
    · subst hI; rw [Lam_empty _ J hJ]; simp
    · rw [if_neg hI]; simp
  pw := by
    intro s s' Kv o hs hd J
    have hW : (C S.w : MvPolynomial (Fin N × Fin (r + K)) O) ≠ 0 := by
      rw [Ne, C_eq_zero]; exact S.w_irr.ne_zero
    have hsq' : (C S.w : MvPolynomial (Fin N × Fin (r + K)) O) ^ 2 = ((p : ℕ) : MvPolynomial (Fin N × Fin (r + K)) O) := by
      rw [← C_pow, hsq, map_natCast]
    have := step1 p (Fact.out : p.Prime) (C S.w) hW hsq' (s' - s).toNat
      (abelian₂ (M.map (phiS p f O N r K s))) (abelian₂ (M'.map (phiS p f O N r K s)))
      (abelian₂ (M.map (phiS p f O N r K s'))) (abelian₂ (M'.map (phiS p f O N r K s')))
      (Lam_inv_one _ M M' h1) (Lam_inv_one _ M' M h2)
      (fun I J => by
        rw [← Lam_map, ← Lam_map]
        exact phiS_cong hF s s' hs _) Kv o hd J
    exact ⟨this.1, fun h => ⟨(this.2 h).1, fun hlt => (this.2 h).2 (by omega)⟩⟩
  inv := by
    intro s Kv o hd J
    have : Kv = Matrix.vecMul (Matrix.vecMul Kv (abelian₂ (M.map (phiS p f O N r K s))))
        (abelian₂ (M'.map (phiS p f O N r K s))) := by
      rw [Matrix.vecMul_vecMul, Lam_inv_one _ M M' h1, Matrix.vecMul_one]
    rw [this]
    simp only [Matrix.vecMul, dotProduct]
    exact Finset.dvd_sum fun I _ => Dvd.dvd.mul_right (hd I) _

end Build

section Final

variable (p f : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF p f) O] {N r K : ℕ}

def zetaL (w : O) (LL : LiftLetters (Fin N)) (g g' : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f)) (i : Fin N) :
    Fin (r + K) → MvPolynomial (Fin N × Fin (r + K)) O :=
  if LL.vec i then Matrix.vecMul (yO w LL i) ((g'⁻¹ * g).map (phiS p f O N r K (LL.pos i)))
  else Matrix.mulVec ((g⁻¹ * g').map (phiS p f O N r K (LL.pos i))) (yO w LL i)

lemma lift_substitution_letter (w : O) (LL : LiftLetters (Fin N)) (g g' : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f))
    (hg : IsGLW g) (hg' : IsGLW g') (i : Fin N) (b : Fin (r + K)) :
    liftSubst p f O w r LL g' (letG p f (O := O) LL g i b) =
      MvPolynomial.map (algebraMap O (KK O)) (zetaL p f w LL g g' i b) := by
  unfold letG zetaL
  by_cases hv : LL.vec i = true
  · rw [if_pos hv, if_pos hv, map_sum]
    simp only [map_mul, liftSubst_X_vec p f O w LL r g' hg' i _ hv, algHom_C, Matrix.vecMul, dotProduct, map_sum,
      Matrix.map_apply, phiS, RingHom.comp_apply, map_C, yO, map_X]
    have e : ∀ c : Fin (r + K), ∑ a, sigMat p f O g'⁻¹ (LL.pos i) c a * sigMat p f O g (LL.pos i) a b =
        algebraMap O (KK O) (psiO p f O (LL.pos i) ((g'⁻¹ * g) c b)) := by
      intro c; rw [← Matrix.mul_apply, ← sigMat_mul, sigMat_apply]
    simp only [← e, Finset.sum_mul, map_sum, Finset.mul_sum, C_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by
      rw [MvPolynomial.algebraMap_eq]; ring
  · have hv' : LL.vec i = false := by simpa using hv
    rw [if_neg hv, if_neg hv, map_sum, sigMat_inv p f O g hg]
    simp only [map_mul, liftSubst_X_cov p f O w LL r g' i _ hv', algHom_C, Matrix.mulVec, dotProduct, map_sum,
      Matrix.map_apply, phiS, RingHom.comp_apply, map_C, yO, map_X]
    have e : ∀ c : Fin (r + K), ∑ a, sigMat p f O g⁻¹ (LL.pos i) b a * sigMat p f O g' (LL.pos i) a c =
        algebraMap O (KK O) (psiO p f O (LL.pos i) ((g⁻¹ * g') b c)) := by
      intro c; rw [← Matrix.mul_apply, ← sigMat_mul, sigMat_apply]
    simp only [← e, Finset.sum_mul, map_sum, Finset.mul_sum, C_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by
      rw [MvPolynomial.algebraMap_eq]; ring

lemma lift_substitution_column_kernel (w : O) (LL : LiftLetters (Fin N)) (g g' : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f))
    (hg : IsGLW g) (hg' : IsGLW g') (z : ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ)
    (J : Finset (Fin (r + K))) :
    liftSubst p f O w r LL g' (KKc p f (O := O) LL g z mu c J) =
      MvPolynomial.map (algebraMap O (KK O)) (ZZ p (zetaL p f w LL g g') LL.pos mu c N z J) := by
  rw [KKc_eq]
  have h1 := ZZ_map (liftSubst p f O w r LL g').toRingHom p (letG p f (O := O) LL g) LL.pos mu c N le_rfl z J
  have h2 := ZZ_map (MvPolynomial.map (algebraMap O (KK O))) p (zetaL p f w LL g g') LL.pos mu c N le_rfl z J
  rw [h2]
  refine h1.trans ?_
  congr 1
  funext i b
  exact lift_substitution_letter p f w LL g g' hg hg' i b

theorem lifted_column_order (hF : FrobCong p f) (S : UniformizedDVR p O) (hsq : S.SqP) (LL : LiftLetters (Fin N))
    (g g' : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f)) (hg : IsGLW g) (hg' : IsGLW g') (z : ℤ)
    (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (H : ColOK LL mu c) (hmono : Monotone LL.pos)
    (hz : ∀ i, LL.pos i ≤ z)
    (hposc : ∀ i j : Fin N, i < j → IsUsed mu c i → IsCostly mu c j → LL.pos i < LL.pos j)
    (J : Finset (Fin (r + K))) :
    InWjRg p f O S.w r LL g' (KKc p f (O := O) LL g z mu c J) (oc (fun i => p ^ (z - LL.pos i).toNat) mu c) := by
  have a1 : (g⁻¹ * g') * (g'⁻¹ * g) = 1 := by
    rw [mul_assoc, ← mul_assoc g', Matrix.mul_nonsing_inv g' hg', one_mul, Matrix.nonsing_inv_mul g hg]
  have a2 : (g'⁻¹ * g) * (g⁻¹ * g') = 1 := by
    rw [mul_assoc, ← mul_assoc g, Matrix.mul_nonsing_inv g hg, one_mul, Matrix.nonsing_inv_mul g' hg']
  have vecZ : ∀ i, LL.vec i = true → Matrix.vecMul (zetaL p f S.w LL g g' i)
      ((g⁻¹ * g').map (phiS p f O N r K (LL.pos i))) = yO S.w LL i := by
    intro i hv
    unfold zetaL; rw [if_pos hv, Matrix.vecMul_vecMul, map_inv_one _ _ _ a2, Matrix.vecMul_one]
  have covZ : ∀ i, LL.vec i = false → Matrix.mulVec ((g'⁻¹ * g).map (phiS p f O N r K (LL.pos i)))
      (zetaL p f S.w LL g g' i) = yO S.w LL i := by
    intro i hv
    unfold zetaL; rw [if_neg (by simp [hv]), Matrix.mulVec_mulVec, map_inv_one _ _ _ a2, Matrix.one_mulVec]
  have hts : Nonempty (TS p (C S.w : MvPolynomial (Fin N × Fin (r + K)) O) c mu LL.pos (zetaL p f S.w LL g g')
      (yO S.w LL)) := by
    by_cases hc : 1 ≤ c
    · refine ⟨mkTS hF S hsq c mu LL.pos _ _ (g⁻¹ * g') (g'⁻¹ * g) a1 a2 (fun j h hw => ?_) (fun j h hw => ?_)⟩
      · rcases hw with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact vecZ _ (H.rise j h h1).1
        · exact absurd hc h2
      · rcases hw with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact absurd hc h2
        · exact covZ _ (H.fall j h h1).1
    · refine ⟨mkTS hF S hsq c mu LL.pos _ _ (g'⁻¹ * g).transpose (g⁻¹ * g').transpose
        (by rw [← Matrix.transpose_mul, a1, Matrix.transpose_one])
        (by rw [← Matrix.transpose_mul, a2, Matrix.transpose_one]) (fun j h hw => ?_) (fun j h hw => ?_)⟩
      · rcases hw with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact absurd h2 hc
        · rw [Matrix.transpose_map, Matrix.vecMul_transpose]; exact covZ _ (H.fall j h h1).1
      · rcases hw with ⟨h1, _⟩ | ⟨_, h2⟩
        · rw [Matrix.transpose_map, Matrix.mulVec_transpose]; exact vecZ _ (H.rise j h h1).1
        · exact absurd h2 hc
  obtain ⟨ts⟩ := hts
  have hmain := fun J => (Ord_main p (Fact.out : p.Prime).ne_zero S.w LL mu c H hmono hposc _ ts N le_rfl z
    (fun i _ _ => hz i) J).1
  obtain ⟨q, hq⟩ := ts.inv z _ _ hmain J
  rw [oS_top] at hq
  unfold InWjRg
  rw [lift_substitution_column_kernel p f S.w LL g g' hg hg', hq]
  intro m
  exact ⟨q.coeff m, by rw [coeff_map, ← C_pow, coeff_C_mul]⟩

end Final

end Formalism.MainNotions.LemmaBAlt
