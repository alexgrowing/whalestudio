import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.FormCOfRel

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem mem_relC_iff (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (t t' : O)
    (Y : Ix r → O) :
    Y ∈ relC O cj (Z.map O.subtype) t t' ↔ ∃ c₁ c₂ : Fin (r + 1) → O,
      (fun j => Y (Sum.inl j)) = Z.mulVec c₂ - (t * c₁ (Fin.last r)) • Pi.single (Fin.last r) 1 ∧
      (fun j => Y (Sum.inr j)) =
        (cjT O cj hO Z).mulVec c₁ - (t' * c₂ (Fin.last r)) • Pi.single (Fin.last r) 1 := by
  have kl : ∀ (c : Ix r → E) (j : Fin (r + 1)), ∑ i, c i * gramC cj (Z.map O.subtype) t t' i (Sum.inl j) =
      (∑ b, (Z j b : E) * c (Sum.inr b)) - (if j = Fin.last r then (t : E) * c (Sum.inl (Fin.last r)) else 0) :=
    fun c j => sum_gram_inl cj _ _ _ c j
  have kr : ∀ (c : Ix r → E) (j : Fin (r + 1)), ∑ i, c i * gramC cj (Z.map O.subtype) t t' i (Sum.inr j) =
      (∑ a, cj (Z a j : E) * c (Sum.inl a)) -
        (if j = Fin.last r then (t' : E) * c (Sum.inr (Fin.last r)) else 0) :=
    fun c j => sum_gram_inr cj _ _ _ c j
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun a => c (Sum.inl a), fun b => c (Sum.inr b), ?_, ?_⟩
    · funext j
      apply Subtype.ext
      rw [hc (Sum.inl j), kl (fun i => (c i : E)) j]
      by_cases hj : j = Fin.last r
      · subst hj; simp [Matrix.mulVec, dotProduct]
      · simp [hj, Matrix.mulVec, dotProduct]
    · funext j
      apply Subtype.ext
      rw [hc (Sum.inr j), kr (fun i => (c i : E)) j]
      by_cases hj : j = Fin.last r
      · subst hj; simp [Matrix.mulVec, dotProduct, cjT]
      · simp [hj, Matrix.mulVec, dotProduct, cjT]
  · rintro ⟨c₁, c₂, h₁, h₂⟩
    refine ⟨Sum.elim c₁ c₂, ?_⟩
    rintro (j | j)
    · rw [kl, show (Y (Sum.inl j) : E) = ((fun j => Y (Sum.inl j)) j : E) from rfl, h₁]
      by_cases hj : j = Fin.last r
      · subst hj; simp [Matrix.mulVec, dotProduct]
      · simp [hj, Matrix.mulVec, dotProduct]
    · rw [kr, show (Y (Sum.inr j) : E) = ((fun j => Y (Sum.inr j)) j : E) from rfl, h₂]
      by_cases hj : j = Fin.last r
      · subst hj; simp [Matrix.mulVec, dotProduct, cjT]
      · simp [hj, Matrix.mulVec, dotProduct, cjT]

theorem mem_headCols_iff {R : Type} [CommRing R] (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (k : Fin (r + 1) → R) :
    k ∈ headCols Z ↔ ∃ w : Fin (r + 1) → R, w (Fin.last r) = 0 ∧ k = Z.mulVec w := by
  unfold headCols
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨Fin.snoc c 0, by simp, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨fun a => w a.castSucc, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hw, mul_comm]

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
