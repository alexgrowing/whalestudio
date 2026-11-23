import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MonomialOfClean
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwoBlockParahoricLowerBlockDetTameCharacter
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem diagT_mem_parahoric (c : A ⊕ D → kˣ) (hc : ∀ i, valuation k (c i : k) = 1) :
    diagT k (A ⊕ D) c ∈ parahoric k A D := by
  rw [mem_parahoric]
  refine ⟨(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [val_diagT, diagonal_apply]
    split_ifs
    · exact (Valuation.mem_integer_iff _ _).2 (hc i).le
    · exact zero_mem _
  · rw [← map_inv, val_diagT, diagonal_apply]
    split_ifs
    · refine (Valuation.mem_integer_iff _ _).2 ?_
      simp [map_inv₀, hc i]
    · exact zero_mem _
  · rw [val_diagT, diagonal_apply_ne _ (by simp)]
    simp

theorem det_lower_diagT (c : A ⊕ D → kˣ) :
    ((diagT k (A ⊕ D) c : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det =
      ((∏ i, c (.inr i) : kˣ) : k) := by
  have : ((diagT k (A ⊕ D) c : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂ =
      diagonal fun i => (c (.inr i) : k) := by
    ext i j
    simp [toBlocks₂₂, val_diagT, diagonal_apply]
  rw [this, det_diagonal, Units.coe_prod]

theorem prod_mulSingle_inr (p : A ⊕ D) (u : kˣ) :
    (∏ i : D, (Pi.mulSingle p u : A ⊕ D → kˣ) (.inr i)) = if p.isRight then u else 1 := by
  rcases p with a | d
  · simp [Pi.mulSingle_apply]
  · simp [Pi.mulSingle_apply]

end GlobalTheory.ParHeckeSupp

namespace GlobalTheory.ParHeckeSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem eq_zero_of_mixed (ξ : kˣ →* ℂˣ) (hξ : ¬ IsUnram ξ) (φ : GL (A ⊕ D) k → ℂ) (hφ : IsBiType ξ φ)
    (m : GL (A ⊕ D) k) (τ : Equiv.Perm (A ⊕ D)) (hm : ∀ x y, y ≠ τ x → (m : Matrix (A ⊕ D) (A ⊕ D) k) x y = 0)
    (p : A ⊕ D) (hp : (τ p).isRight ≠ p.isRight) : φ m = 0 := by
  obtain ⟨u, hu1, hu⟩ : ∃ u : kˣ, valuation k (u : k) = 1 ∧ ξ u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hξ h
  have hv : ∀ q : A ⊕ D, ∀ i, valuation k ((Pi.mulSingle q u : A ⊕ D → kˣ) i : k) = 1 := fun q i => by
    rw [Pi.mulSingle_apply]
    split_ifs <;> simp [hu1]
  have hcomm : diagT k (A ⊕ D) (Pi.mulSingle p u) * m = m * diagT k (A ⊕ D) (Pi.mulSingle (τ p) u) := by
    ext x y
    simp only [Units.val_mul, val_diagT, diagonal_mul, mul_diagonal]
    by_cases hy : y = τ x
    · subst hy
      simp [Pi.mulSingle_apply, mul_comm]
    · simp [hm x y hy]
  have h1 := (hφ _ (diagT_mem_parahoric _ (hv p)) _ (det_lower_diagT _).symm m).1
  have h2 := (hφ _ (diagT_mem_parahoric _ (hv (τ p))) _ (det_lower_diagT _).symm m).2
  rw [hcomm, h2, prod_mulSingle_inr, prod_mulSingle_inr] at h1
  have hu' : (ξ u : ℂ) ≠ 1 := fun h => hu (Units.ext (by simpa using h))
  by_contra h0
  have h3 := mul_right_cancel₀ h0 h1
  cases h₁ : (τ p).isRight <;> cases h₂ : p.isRight <;> simp only [h₁, h₂] at h3 hp
  · exact hp rfl
  · exact hu' (by simpa using h3.symm)
  · exact hu' (by simpa using h3)
  · exact hp rfl

theorem exists_emb₂ (m : GL (A ⊕ D) k) (τ : Equiv.Perm (A ⊕ D))
    (hm : ∀ x y, y ≠ τ x → (m : Matrix (A ⊕ D) (A ⊕ D) k) x y = 0) (hτ : ∀ p, (τ p).isRight = p.isRight) :
    ∃ x y, m = emb₂ k (Equiv.refl (A ⊕ D)) (x, y) := by
  have h12 : (m : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₁₂ = 0 := by
    ext a d
    refine hm _ _ fun h => ?_
    have := hτ (.inl a)
    rw [← h] at this
    simp at this
  have h21 : (m : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₁ = 0 := by
    ext d a
    refine hm _ _ fun h => ?_
    have := hτ (.inr d)
    rw [← h] at this
    simp at this
  have hdet : (m : Matrix (A ⊕ D) (A ⊕ D) k).det =
      (m : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₁₁.det * (m : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det := by
    conv_lhs => rw [← fromBlocks_toBlocks (m : Matrix (A ⊕ D) (A ⊕ D) k), h12]
    exact det_fromBlocks_zero₁₂ _ _ _
  have hm0 : (m : Matrix (A ⊕ D) (A ⊕ D) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero
  rw [hdet] at hm0
  refine ⟨nonsingInvUnit _ (isUnit_iff_ne_zero.2 (left_ne_zero_of_mul hm0)),
    nonsingInvUnit _ (isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hm0)), Units.ext ?_⟩
  rw [val_emb₂]
  simp only [reindex_refl_refl]
  conv_lhs => rw [← fromBlocks_toBlocks (m : Matrix (A ⊕ D) (A ⊕ D) k), h12, h21]
  rfl

end GlobalTheory.ParHeckeSupp

namespace GlobalTheory.ParHeckeSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def numE : A ⊕ D ≃ Fin (Fintype.card A + Fintype.card D) :=
  (Equiv.sumCongr (Fintype.equivFin A) (Fintype.equivFin D)).trans finSumFinEquiv

theorem numE_lt (a : A) (d : D) : numE (A := A) (D := D) (.inl a) < numE (.inr d) := by
  simp only [numE, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_iff_val_lt_val, Fin.coe_castAdd,
    Fin.coe_natAdd]
  omega

variable (k A D) in

def toAD : GL (Fin (Fintype.card A + Fintype.card D)) k →* GL (A ⊕ D) k :=
  Units.map (reindexAlgEquiv k k (numE (A := A) (D := D)).symm).toMonoidHom

theorem toAD_val (g : GL (Fin (Fintype.card A + Fintype.card D)) k) (x y : A ⊕ D) :
    (toAD k A D g : Matrix (A ⊕ D) (A ⊕ D) k) x y = (g : Matrix _ _ k) (numE x) (numE y) := by
  simp [toAD, reindexAlgEquiv_apply, reindex_apply]

theorem toAD_surj (g : GL (A ⊕ D) k) : ∃ g₀, toAD k A D g₀ = g :=
  ⟨Units.map (reindexAlgEquiv k k (numE (A := A) (D := D))).toMonoidHom g,
    Units.ext (Matrix.ext fun x y => by rw [toAD_val]; simp [reindexAlgEquiv_apply, reindex_apply])⟩

theorem toAD_incl_mem (u : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.unipLevel k (Fintype.card A + Fintype.card D)) :
    toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u) ∈ parahoric k A D := by
  rw [mem_parahoric]
  refine ⟨⟨Units.map (reindexAlgEquiv 𝒪[k] 𝒪[k] (numE (A := A) (D := D)).symm).toMonoidHom u.1, ?_⟩,
    fun i j => ?_⟩
  · ext x y
    rw [toAD_val, GlobalTheory.TypeDim.incl_val]
    simp [reindexAlgEquiv_apply, reindex_apply]
    rfl
  · rw [toAD_val, GlobalTheory.TypeDim.incl_val]
    have h := ((mem_unipB _).1 (Subgroup.mem_comap.1 u.2)).1 _ _ (numE_lt j i)
    rw [GlobalTheory.TypeDim.red_val] at h
    exact (GlobalTheory.ParahoricLowerBlock.residue_eq_zero_iff_val _).1 h

theorem support_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ →
    ∀ φ : GL (A ⊕ D) k → ℂ, IsBiType ξ φ → ∀ g, φ g ≠ 0 → ∃ x y, ∃ j ∈ parahoric k A D,
      ∃ j' ∈ parahoric k A D, g = j * emb₂ k (Equiv.refl (A ⊕ D)) (x, y) * j' := by
  intro k _ _ _ _ A D _ _ _ _ ξ hξt hξ φ hφ g hg
  obtain ⟨g₀, rfl⟩ := toAD_surj g
  obtain ⟨u, u', w, c, e⟩ := GlobalTheory.TypeDim.IwahoriBruhat.iwahori_bruhat k _ g₀
  have hj := toAD_incl_mem (A := A) (D := D) u
  have hj' := toAD_incl_mem (A := A) (D := D) u'
  have hgm : toAD k A D g₀ = toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u) *
      toAD k A D (GlobalTheory.Parabolic.permGL k w * diagT k _ c) * toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u') := by
    rw [e]
    simp only [map_mul]
  generalize toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u) = j at hj hgm
  generalize toAD k A D (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses.incl k _ u') = j' at hj' hgm
  let τ : Equiv.Perm (A ⊕ D) := numE.trans (w.symm.trans numE.symm)
  have hm : ∀ x y, y ≠ τ x →
      (toAD k A D (GlobalTheory.Parabolic.permGL k w * diagT k _ c) : Matrix (A ⊕ D) (A ⊕ D) k) x y = 0 := by
    intro x y h
    rw [toAD_val, Units.val_mul, val_diagT, mul_diagonal, GlobalTheory.Parabolic.permGL_apply, if_neg, zero_mul]
    intro h'
    apply h
    simp [τ, h']
  generalize toAD k A D (GlobalTheory.Parabolic.permGL k w * diagT k _ c) = m at hm hgm
  have hφm : φ m ≠ 0 := by
    intro h0
    apply hg
    obtain ⟨hd, -⟩ := GlobalTheory.ParahoricLowerBlock.lower_block_tame k A D ξ hξt j hj
    obtain ⟨hd', -⟩ := GlobalTheory.ParahoricLowerBlock.lower_block_tame k A D ξ hξt j' hj'
    rw [hgm, (hφ j' hj' (Units.mk0 _ hd') rfl _).2, (hφ j hj (Units.mk0 _ hd) rfl _).1, h0]
    simp
  have hτ : ∀ p, (τ p).isRight = p.isRight := by
    by_contra h
    push_neg at h
    obtain ⟨p, hp⟩ := h
    exact hφm (eq_zero_of_mixed ξ hξ φ hφ m τ hm p hp)
  obtain ⟨x, y, hxy⟩ := exists_emb₂ m τ hm hτ
  exact ⟨x, y, j, hj, j', hj', by rw [hgm, hxy]⟩

end GlobalTheory.ParHeckeSupp
