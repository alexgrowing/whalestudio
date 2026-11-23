import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Restrict
import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothCore
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset Matrix

namespace PositivityTheory.RgHe3

namespace BlockRestriction

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.UnitaryDecomposition PositivityTheory.RgHe

variable {n : ℕ}

def psi (e : Fin n ⊕ Unit ≃ Fin (n + 1)) :
    Matrix (Fin n) (Fin n) ℂ × Matrix Unit Unit ℂ →+* Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ where
  toFun p := Matrix.reindex e e (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' a b := by
    simp [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  map_zero' := by simp
  map_add' a b := by
    ext i j
    rcases h1 : e.symm i with i' | i' <;> rcases h2 : e.symm j with j' | j' <;> simp [h1, h2]

theorem continuous_psi (e : Fin n ⊕ Unit ≃ Fin (n + 1)) : Continuous (psi e) := by
  show Continuous fun p : Matrix (Fin n) (Fin n) ℂ × Matrix Unit Unit ℂ =>
    (Matrix.fromBlocks p.1 0 0 p.2).submatrix e.symm e.symm
  exact (continuous_fst.matrix_fromBlocks continuous_const continuous_const
    continuous_snd).matrix_submatrix _ _

set_option backward.isDefEq.respectTransparency false in
theorem emb_exp (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (Y : Matrix (Fin n) (Fin n) ℂ) :
    emb e (NormedSpace.exp Y) = NormedSpace.exp (blk0 e Y) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedRing (Matrix Unit Unit ℂ) := Matrix.linftyOpNormedRing
  letI : NormedRing (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix Unit Unit ℂ) := Matrix.linftyOpNormedAlgebra
  have h := NormedSpace.map_exp (psi e) (by exact continuous_psi e) (Y, 0)
  have h3 : psi e (NormedSpace.exp (Y, 0)) = emb e (NormedSpace.exp Y) := by
    show Matrix.reindex e e (Matrix.fromBlocks (NormedSpace.exp (Y, (0 : Matrix Unit Unit ℂ))).1 0 0
      (NormedSpace.exp (Y, (0 : Matrix Unit Unit ℂ))).2) = _
    rw [Prod.fst_exp, Prod.snd_exp, NormedSpace.exp_zero]
    rfl
  rw [← h3, h]
  rfl

theorem block_embed_smul (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (c : ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    blk0 e (c • Y) = c • blk0 e Y := by
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [blk0]

theorem block_embed_add (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (Y Z : Matrix (Fin n) (Fin n) ℂ) :
    blk0 e (Y + Z) = blk0 e Y + blk0 e Z := by
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [blk0]

theorem block_embed_single (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (a b : Fin n) :
    blk0 e (Matrix.single a b 1) = Matrix.single (e (Sum.inl a)) (e (Sum.inl b)) 1 := by
  ext i j
  obtain ⟨x, rfl⟩ := e.surjective i
  obtain ⟨y, rfl⟩ := e.surjective j
  rcases x with x | x <;> rcases y with y | y <;> simp [blk0, Matrix.single_apply]

theorem embed_eq_block_embed_add (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (h : Matrix (Fin n) (Fin n) ℂ) :
    emb e h = blk0 e h + emb e 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [blk0, emb]

theorem emb_exp_smul (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    emb e (NormedSpace.exp ((t : ℂ) • X)) = NormedSpace.exp ((t : ℂ) • blk0 e X) := by
  rw [emb_exp, block_embed_smul]

theorem jm_eq {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (hF : Fits ε ε' e) :
    Jm ε = emb e (Jm ε') := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  have h1 : ε (e (Sum.inr ())) = true := hF.1
  rcases a with a | a <;> rcases b with b | b <;> simp [emb, Jm, Matrix.diagonal_apply, hF.2, h1]

theorem block_embed_conjTranspose (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (X : Matrix (Fin n) (Fin n) ℂ) : (blk0 e X)ᴴ = blk0 e Xᴴ := by
  simp [blk0, Matrix.fromBlocks_conjTranspose]

theorem block_embed_mul_embed (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    blk0 e X * emb e Y = blk0 e (X * Y) := by
  simp [blk0, emb, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem embed_mul_block_embed (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    emb e Y * blk0 e X = blk0 e (Y * X) := by
  simp [blk0, emb, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem emb_mem {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (hF : Fits ε ε' e)
    {h : Matrix (Fin n) (Fin n) ℂ} (hh : h ∈ UJset ε') : emb e h ∈ UJset ε := by
  have h1 : ∀ A B : Matrix (Fin n) (Fin n) ℂ, emb e (A * B) = emb e A * emb e B := by
    intro A B
    simp only [emb, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  have h2 : (emb e h)ᴴ = emb e hᴴ := by
    simp [emb, Matrix.fromBlocks_conjTranspose]
  show (emb e h)ᴴ * Jm ε * emb e h = Jm ε
  have hh' : hᴴ * Jm ε' * h = Jm ε' := hh
  rw [h2, jm_eq hF, ← h1, ← h1, hh']

theorem continuous_emb' (e : Fin n ⊕ Unit ≃ Fin (n + 1)) : Continuous fun h : Matrix (Fin n) (Fin n) ℂ => emb e h := by
  show Continuous fun h : Matrix (Fin n) (Fin n) ℂ => (Matrix.fromBlocks h 0 0 1).submatrix e.symm e.symm
  exact (continuous_id.matrix_fromBlocks continuous_const continuous_const
    continuous_const).matrix_submatrix _ _

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def blk0L (e : Fin n ⊕ Unit ≃ Fin (n + 1)) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ where
  toFun := blk0 e
  map_add' := block_embed_add e
  map_smul' r Y := by
    rw [RingHom.id_apply, ← Complex.coe_smul, block_embed_smul, Complex.coe_smul]

open scoped ContDiff in
theorem contDiff_emb (e : Fin n ⊕ Unit ≃ Fin (n + 1)) :
    ContDiff ℝ ∞ (fun h : Matrix (Fin n) (Fin n) ℂ => emb e h) := by
  have h1 : ContDiff ℝ ∞ (fun h : Matrix (Fin n) (Fin n) ℂ => blk0L e h) :=
    (LinearMap.toContinuousLinearMap (blk0L e)).contDiff
  have h2 := h1.add (contDiff_const (c := emb e (0 : Matrix (Fin n) (Fin n) ℂ)))
  have e1 : (fun h : Matrix (Fin n) (Fin n) ℂ => emb e h) = fun h => blk0L e h + emb e 0 :=
    funext fun h => embed_eq_block_embed_add e h
  rw [e1]
  exact h2

theorem smooth_res {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (hF : Fits ε ε' e)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)} {v : H} (hv : IsSmoothVecU ε π v) :
    IsSmoothVecU ε' (res e π) v := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, h1, hFs, hFe⟩ := hv (emb e g₀) (emb_mem hF hg₀)
  refine ⟨(fun h => emb e h) ⁻¹' U, fun h => F (emb e h), hU.preimage (continuous_emb' e), h1,
    hFs.comp (contDiff_emb e).contDiffOn (fun h hh => hh), fun g hg hJ => ?_⟩
  exact hFe _ hg (emb_mem hF hJ)

end Smooth

theorem dS_res {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : Fin n ⊕ Unit ≃ Fin (n + 1))
    (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) :
    dS (res e π) X v = dS π (blk0 e X) v := by
  simp only [dS, res, emb_exp_smul]

end BlockRestriction

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.UnitaryDecomposition PositivityTheory.RgHe BlockRestriction

theorem restriction_holds : Restrict := by
  intro n ε ε' e H _ _ _ π hF hπ
  have hmul : ∀ A B : Matrix (Fin n) (Fin n) ℂ, emb e (A * B) = emb e A * emb e B := by
    intro A B
    simp only [emb, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  have hone : emb e 1 = 1 := by
    simp [emb, Matrix.fromBlocks_one]
  have hU : ∀ g, g ∈ UJset ε' → emb e g ∈ UJset ε := fun g hg => emb_mem hF hg
  have hres : IsURepOn (UJset ε') (res e π) := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · show π (emb e 1) = 1
      rw [hone]
      exact hπ.1.1
    · intro a ha b hb
      show π (emb e (a * b)) = π (emb e a) ∘SL π (emb e b)
      rw [hmul]
      exact hπ.1.2 _ (hU a ha) _ (hU b hb)
    · intro g hg v
      exact hπ.2.1 _ (hU g hg) v
    · intro v
      exact (hπ.2.2 v).comp (continuous_emb' e).continuousOn (fun g hg => hU g hg)
  refine ⟨hres, ?_⟩
  have hmem : ∀ x : smD ε π, (x : H) ∈ smD ε' (res e π) := fun x =>
    (mem_smD_iff _ _ _).2 (smooth_res hF ((mem_smD_iff _ _ _).1 x.2))
  refine ⟨(smD ε π).subtype.codRestrict (smD ε' (res e π)) hmem, fun x => rfl, ?_⟩
  intro a b x
  have hsub : ∀ Y Z : Matrix (Fin n) (Fin n) ℂ, blk0 e (Y - Z) = blk0 e Y - blk0 e Z := by
    intro Y Z
    rw [eq_sub_iff_add_eq, ← block_embed_add, sub_add_cancel]
  have hJ : ∀ Y : Matrix (Fin n) (Fin n) ℂ,
      Jm ε * (blk0 e Y)ᴴ * Jm ε = blk0 e (Jm ε' * Yᴴ * Jm ε') := by
    intro Y
    rw [jm_eq hF, block_embed_conjTranspose, embed_mul_block_embed, block_embed_mul_embed]
  have hc1 : ∀ Y, blk0 e (S7.cpart1 ε' Y) = S7.cpart1 ε (blk0 e Y) := by
    intro Y
    simp only [S7.cpart1]
    rw [hJ, ← hsub, block_embed_smul]
  have hc2 : ∀ Y, blk0 e (S7.cpart2 ε' Y) = S7.cpart2 ε (blk0 e Y) := by
    intro Y
    simp only [S7.cpart2]
    rw [hJ, ← block_embed_add, block_embed_smul]
  apply Subtype.ext
  show ((smE ε π (e (Sum.inl a)) (e (Sum.inl b))) x : H) =
    ((smE ε' (res e π) a b) ⟨x, hmem x⟩ : H)
  rw [smE_apply hπ, smE_apply hres, dS_res, dS_res, hc1, hc2, block_embed_single]

end PositivityTheory.RgHe3
