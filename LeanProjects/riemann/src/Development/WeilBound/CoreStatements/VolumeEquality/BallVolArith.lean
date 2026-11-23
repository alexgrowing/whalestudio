import Development.WeilBound.CoreStatements.VolumeEquality.BallVolDefs
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.LevelIndexEq

noncomputable section

namespace SheetDecomposition

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar.Cusp.Dict GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem sig_of_sgI {j j' : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin (j + j')) (Fin (j + j')) E)
    (A : Matrix (Fin (j + j')) (Sg j j') ℂ) (h : Aᴴ * (G.map τ)ᵀ * A = sgI j j') :
    ∃ Q : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, Q.det ≠ 0 ∧
      ReciprocityTheory.ChartRestriction.G.FD.gram τ G Q = Matrix.diagonal fun a : Fin (j + j') => ((sgn j (a : ℕ) : ℝ) : ℂ) := by
  let Q : Matrix (Fin (j + j')) (Fin (j + j')) ℂ := A.submatrix id finSumFinEquiv.symm
  have e : Qᴴ * (G.map τ)ᵀ * Q = Matrix.diagonal fun a : Fin (j + j') => ((sgn j (a : ℕ) : ℝ) : ℂ) := by
    have : Qᴴ * (G.map τ)ᵀ * Q = (Aᴴ * (G.map τ)ᵀ * A).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      ext a b
      simp [Q, Matrix.mul_apply]
    rw [this, h]
    ext a b
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
    rw [Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.diagonal_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq]
    rcases a with a | a <;> rcases b with b | b <;> simp [sgI, sgn, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨Q, fun h0 => ?_, ?_⟩
  · have := congrArg det e
    rw [det_mul, h0, mul_zero, det_diagonal] at this
    refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) this.symm
    simp only [sgn]
    split_ifs <;> simp
  · rw [← diagonal_transpose, ← e]
    ext a b
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul, Matrix.conjTranspose_apply, Complex.star_def]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isotropic_of_sig {r p : ℕ} (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (Ψ : Set (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ∨ ComplexEmbedding.conjugate τ ∈ Ψ)
    (hs : ∀ τ ∈ Ψ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      ReciprocityTheory.ChartRestriction.G.FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ))
    (hr : 3 ≤ r) (h0 : 0 < p) (h1 : p < r) : ∃ e : Fin r → E, e ≠ 0 ∧ herm G e e = 0 := by
  classical
  let i0 : Fin r := ⟨0, by omega⟩
  let i1 : Fin r := ⟨r - 1, by omega⟩
  let m : Fin r := ⟨1, by omega⟩
  have hm0 : i0 ≠ m := by simp [i0, m, Fin.ext_iff]
  have hm1 : i1 ≠ m := by simp [i1, m, Fin.ext_iff]; omega
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]; omega
  let ε : Fin r → ℤ := fun a => if (a : ℕ) < p then 1 else -1
  have hε : ∀ a, ε a * ε a = 1 := fun a => by simp only [ε]; split_ifs <;> norm_num
  have hεs : ∀ a : Fin r, ((sgn p (a : ℕ) : ℝ) : ℂ) = (ε a : ℂ) := fun a => by
    simp only [ε, sgn]; split_ifs <;> simp
  let π : ℤ := ∏ a ∈ Finset.univ.erase m, ε a
  have hπ : π * π = 1 := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun a _ => hε a
  let d : Fin r → E := fun a => if a = m then G.det * π else ε a
  have hdet : (diagonal d).det = G.det := by
    rw [det_diagonal, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m), Finset.prod_congr rfl
      (g := fun a => (ε a : E)) fun a ha => if_neg (Finset.ne_of_mem_erase ha)]
    simp only [d, if_true]
    rw [← Int.cast_prod, mul_assoc, ← Int.cast_mul, hπ, Int.cast_one, mul_one]
  have hcd : ∀ a, cc (d a) = d a := fun a => by
    have := GlobalTheory.Published.cc_det_of_herm hG
    simp only [d]
    split_ifs
    · simp only [cc, map_mul, map_intCast] at this ⊢; rw [this]
    · simp [cc]
  obtain ⟨P, hP, e⟩ := GlobalTheory.Published.Landherr.of_signature GlobalTheory.QNorm.landherr_and_landherrSt.1 (G' := diagonal d) hG
    (fun a b => by
      by_cases h : a = b
      · subst h; simp [hcd]
      · simp [h, Ne.symm h, cc])
    hd (by rw [hdet]; exact hd) Ψ hΨ
    (fun τ hτ => ⟨p, hs τ hτ, by
      obtain ⟨Q, hQ, e⟩ := hs τ hτ
      have h2 := congrArg det e
      rw [GlobalTheory.Published.gram_eq, det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
        ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_diagonal,
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)] at h2
      simp only [hεs] at h2
      rw [← Int.cast_prod] at h2
      refine ⟨diagonal fun a => if a = m then Q.det else 1, ?_, ?_⟩
      · rw [det_diagonal]
        exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> simp [hQ]
      · rw [GlobalTheory.Published.gram_eq, diagonal_transpose, diagonal_map (map_zero _), diagonal_map (map_zero _),
          diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext a
        rw [hεs]
        by_cases h : a = m
        · subst h
          have hπ' : (π : ℂ) * π = 1 := by exact_mod_cast hπ
          simp only [d, if_true, map_mul, map_intCast]
          linear_combination (π : ℂ) * h2 + (ε m : ℂ) * hπ'
        · simp [d, h]⟩)
    ⟨1, by rw [hdet, div_self hd]; simp [cc]⟩
  refine ⟨P *ᵥ (Pi.single i0 1 + Pi.single i1 1), fun h => ?_, ?_⟩
  · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) i0
    simp [Pi.single_eq_of_ne h01] at this
  · rw [herm_mulVec', show Pᵀ * G * P.map (ccH E) = diagonal d from e.symm]
    have e0 : d i0 = 1 := by simp [d, hm0, ε, i0, h0]
    have e1 : d i1 = -1 := by
      have : ¬ (r - 1 < p) := by omega
      simp [d, hm1, ε, i1, this]
    simp [herm, cc, diagonal_apply, Pi.single_apply, apply_ite (IsCMField.complexConj E), add_mul, mul_add,
      Finset.sum_add_distrib, h01, h01.symm, e0, e1]

theorem arithIdx : ArithIdx := by
  intro E _ _ _ _ Ψ j j' s G G' L L' ξ 𝔞 hΨ hj hj' hr hG hG' hd hd' hs hs' hL hL' hξ hc hS hS' h𝔞 hN
  have t : ∀ u ∈ Set.range s, ∃ Q : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, Q.det ≠ 0 ∧
      ReciprocityTheory.ChartRestriction.G.FD.gram u G Q = Matrix.diagonal fun a : Fin (j + j') => ((sgn j (a : ℕ) : ℝ) : ℂ) := by
    rintro _ ⟨τ, rfl⟩
    exact (hs τ).elim fun A => sig_of_sgI _ _ A
  have t' : ∀ u ∈ Set.range s, ∃ Q : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, Q.det ≠ 0 ∧
      ReciprocityTheory.ChartRestriction.G.FD.gram u G' Q = Matrix.diagonal fun a : Fin (j + j') => ((sgn j (a : ℕ) : ℝ) : ℂ) := by
    rintro _ ⟨τ, rfl⟩
    exact (hs' τ).elim fun A => sig_of_sgI _ _ A
  obtain ⟨P, hP, hPG⟩ := (GlobalTheory.selfDual_lattices_one_genus hG hG' hd hd' hL hL' (Or.inr ⟨ξ, hξ, hc, hS, hS'⟩)).2.2
    GlobalTheory.QNorm.landherr_and_landherrSt.1 GlobalTheory.T.hasse_norm_theorem_quadratic_extension (Set.range s) hΨ fun u hu => ⟨j, t u hu, t' u hu⟩
  let a : GL (Fin (j + j')) E := Matrix.GeneralLinearGroup.mkOfDetNeZero P hP
  have ha : (a : Matrix (Fin (j + j')) (Fin (j + j')) E)ᵀ * G *
      (a : Matrix (Fin (j + j')) (Fin (j + j')) E).map (ccH E) = G' := hPG.symm
  obtain ⟨aL', haL', hmap, -, t2⟩ := dualTransport E _ G G' a L' ha hL'
  have hg := localToAdelic E _ G L aL' hL haL'
    ((GlobalTheory.selfDual_lattices_one_genus hG hG hd hd haL' hL (Or.inr ⟨ξ, hξ, hc, t2 ξ hS', hS⟩)).2.1 rfl)
  have hI : IsIsotropicHermitianSetting (IsCMField.complexConj E) G := by
    refine ⟨Algebra.IsQuadraticExtension.finrank_eq_two _ _, IsCMField.complexConj_ne_one E, ?_, isUnit_iff_ne_zero.2 hd,
      isotropic_of_sig G hG hd _ hΨ t hr hj (by omega)⟩
    ext i k
    exact (hG i k).symm
  have e : conjBy a (levelGrp (ccH E) G' L' 𝔞) = levelGrp (ccH E) G aL' 𝔞 :=
    (levelFacts _ E _ (IsCMField.complexConj E) G' L' 𝔞 hL' (isUnit_iff_ne_zero.2 hd')).2 G a aL' ha hmap
  refine ⟨a, ha, ?_, ?_⟩
  · rw [e]
    exact inf_le_left
  · rw [e]
    exact levelIndexEq _ E _ _ G L aL' 𝔞 hI hL haL' h𝔞 hN hg

end SheetDecomposition
