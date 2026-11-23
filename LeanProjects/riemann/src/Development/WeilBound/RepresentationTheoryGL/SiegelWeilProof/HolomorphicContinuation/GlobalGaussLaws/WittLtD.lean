import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittLtC

open Matrix NumberField GlobalTheory.Inertia
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hyp_map (τ : E →+* ℂ) : (hyp : Matrix (Fin 2) (Fin 2) E).map τ = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hyp]

theorem index_hyp (τ : E →+* ℂ) :
    posIndex ((hyp : Matrix (Fin 2) (Fin 2) E).map τ) = 1 ∧ negIndex ((hyp : Matrix (Fin 2) (Fin 2) E).map τ) = 1 := by
  rw [hyp_map]
  have hP : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    norm_num
  have hD : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ)ᵀ * !![0, 1; 1, 0] *
      (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) = diagonal ![2, -2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] <;> norm_num
  refine ⟨?_, ?_⟩
  · rw [posIndex_eq_card_of_congr_diagonal hP hD, Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext k
    fin_cases k <;> simp
  · rw [negIndex_eq_card_of_congr_diagonal hP hD, Finset.card_eq_one]
    refine ⟨1, ?_⟩
    ext k
    fin_cases k <;> simp

theorem hf_blocks {m : ℕ} (G2 : Matrix (Fin m) (Fin m) E) (u u' : Fin 2 ⊕ Fin m → E) :
    hf (fromBlocks hyp 0 0 G2) u u' = hf hyp (u ∘ Sum.inl) (u' ∘ Sum.inl) + hf G2 (u ∘ Sum.inr) (u' ∘ Sum.inr) := by
  simp only [hf]
  rw [fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, Function.comp_def]

private theorem posIndex_negIndex_eq_one_add_of_hyperbolic_split {n : Type} [Fintype n] [DecidableEq n] {m : ℕ} {G : Matrix n n E}
    {G2 : Matrix (Fin m) (Fin m) E} {P : Matrix n n E} (e : Fin 2 ⊕ Fin m ≃ n) (hP : P.det ≠ 0)
    (hPG : Pᵀ * G * P.map FD.cc = (fromBlocks hyp 0 0 G2).submatrix e.symm e.symm)
    (hG2 : ∀ a b, FD.cc (G2 a b) = G2 b a) (τ : E →+* ℂ) :
    posIndex (G.map τ) = 1 + posIndex (G2.map τ) ∧ negIndex (G.map τ) = 1 + negIndex (G2.map τ) := by
  have hQ : (P.map τ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ).2 hP
  have hmap : (P.map τ)ᵀ * G.map τ * (P.map τ).map (starRingEnd ℂ) =
      ((fromBlocks hyp 0 0 G2).submatrix e.symm e.symm).map τ := by
    rw [← hPG, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    congr 1
    ext i j
    simp [emb_cc]
  have hH1 : ((hyp : Matrix (Fin 2) (Fin 2) E).map τ).IsHermitian := by
    rw [hyp_map]
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  have hH2 : (G2.map τ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.map_apply]
    rw [← starRingEnd_apply, ← emb_cc, hG2]
  have hblk : ((fromBlocks hyp 0 0 G2).submatrix e.symm e.symm).map τ =
      (fromBlocks ((hyp : Matrix (Fin 2) (Fin 2) E).map τ) 0 0 (G2.map τ)).submatrix e.symm e.symm := by
    rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
    simp
  obtain ⟨h1, h2⟩ := index_hyp (E := E) τ
  constructor
  · rw [← posIndex_congr (G.map τ) hQ, hmap, hblk, posIndex_submatrix_equiv,
      posIndex_fromBlocks hH1 hH2, h1]
  · rw [← negIndex_congr (G.map τ) hQ, hmap, hblk, negIndex_submatrix_equiv,
      negIndex_fromBlocks hH1 hH2, h2]

set_option maxHeartbeats 1600000 in

theorem main_iso : ∀ (k : ℕ) {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n E),
    (∀ a b, FD.cc (G a b) = G b a) → G.det ≠ 0 → 2 * k < Fintype.card n →
    (∀ τ : E →+* ℂ, k ≤ posIndex (G.map τ) ∧ k ≤ negIndex (G.map τ)) →
    ∃ W : Submodule E (n → E), Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, hf G x y = 0 := fun
  | 0 => by
    intro G _ _ _ _
    refine ⟨⊥, by simp, ?_⟩
    intro x hx y hy
    rw [Submodule.mem_bot] at hx
    subst hx
    simp [hf]
  | k + 1 => by
    rename_i n _ _
    intro G hG hdet hcard hidx
    have h3 : 3 ≤ Fintype.card n := by omega
    obtain ⟨z, hz, hzz⟩ := iso_gen G hG hdet h3 (fun τ =>
      ⟨le_trans (Nat.le_add_left 1 k) (hidx τ).1, le_trans (Nat.le_add_left 1 k) (hidx τ).2⟩)
    obtain ⟨m, e, G2, P, hP, hPG, hG2, hdet2⟩ := split hG hdet hz hzz
    have hm := Fintype.card_congr e
    simp at hm
    obtain ⟨W2, hW2r, hW2⟩ := main_iso k G2 hG2 hdet2 (by simp; omega) (fun τ => by
      obtain ⟨h1, h2⟩ := posIndex_negIndex_eq_one_add_of_hyperbolic_split e hP hPG hG2 τ
      obtain ⟨h4, h5⟩ := hidx τ
      exact ⟨by omega, by omega⟩)
    let ψ : E × W2 →ₗ[E] (Fin 2 ⊕ Fin m → E) :=
      { toFun := fun p => Sum.elim ![p.1, 0] (p.2 : Fin m → E)
        map_add' := by
          intro p q
          ext (i | i)
          · fin_cases i <;> simp
          · simp
        map_smul' := by
          intro c p
          ext (i | i)
          · fin_cases i <;> simp
          · simp }
    let L : (Fin 2 ⊕ Fin m → E) →ₗ[E] (n → E) := P.mulVecLin ∘ₗ LinearMap.funLeft E E e.symm
    have hLapp : ∀ u, L u = P *ᵥ (u ∘ e.symm) := fun u => rfl
    have hψ : Function.Injective ψ := by
      intro p q hpq
      have h1 := congrFun hpq (Sum.inl 0)
      have h2 : ∀ i, (p.2 : Fin m → E) i = (q.2 : Fin m → E) i := fun i => congrFun hpq (Sum.inr i)
      simp [ψ] at h1
      exact Prod.ext h1 (Subtype.ext (funext h2))
    have hL : Function.Injective L := by
      have hu : Function.Injective P.mulVec :=
        Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det P).2 (isUnit_iff_ne_zero.2 hP))
      exact hu.comp (LinearMap.funLeft_injective_of_surjective E E _ e.symm.surjective)
    have hinj : Function.Injective (L ∘ₗ ψ) := by
      rw [LinearMap.coe_comp]
      exact hL.comp hψ
    have key : ∀ u u' : Fin 2 ⊕ Fin m → E, hf G (L u) (L u') = hf (fromBlocks hyp 0 0 G2) u u' := by
      intro u u'
      have := hf_congr G P (u ∘ e.symm) (u' ∘ e.symm)
      rw [hPG, hf_submatrix] at this
      rw [hLapp, hLapp]
      simpa [Function.comp_def] using this.symm
    refine ⟨LinearMap.range (L ∘ₗ ψ), ?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_self, hW2r]
      ring
    · intro x hx y hy
      obtain ⟨p, rfl⟩ := LinearMap.mem_range.1 hx
      obtain ⟨q, rfl⟩ := LinearMap.mem_range.1 hy
      show hf G (L (ψ p)) (L (ψ q)) = 0
      rw [key, hf_blocks]
      have e1 : ∀ r : E × W2, (ψ r ∘ Sum.inl) = ![r.1, 0] := by
        intro r
        funext i
        simp [ψ]
      have e2 : ∀ r : E × W2, (ψ r ∘ Sum.inr) = (r.2 : Fin m → E) := by
        intro r
        funext i
        simp [ψ]
      rw [e1, e2, e1, e2, hW2 _ p.2.2 _ q.2.2]
      simp [hf, hyp, dotProduct, mulVec, Fin.sum_univ_two]

end PositivityTheory.Rg.Sw.Glob.WLt

end
