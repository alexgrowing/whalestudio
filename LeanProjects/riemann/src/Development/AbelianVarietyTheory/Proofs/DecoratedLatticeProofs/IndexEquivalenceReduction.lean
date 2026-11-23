import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IterPrincipalSpec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

namespace GlobalTheory.FunObj.TieLev

theorem mem_iter_gen {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {R t : Type} [Fintype R] [DecidableEq R] [Fintype t] [DecidableEq t]
    (P : TypeDatum k R) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : GL (Ix R t j) k) :
    g ∈ (P.iter t μ hμ j).J ↔ g ∈ KO k (Ix R t j) ∧
      (∀ a b : Ix R t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧
      ∃ x ∈ P.J, x.val = g.val.submatrix Sum.inl Sum.inl := by
  induction j with
  | zero =>
    refine ⟨fun h => ⟨TypeDatum.le_KO _ h, fun a b hab => ?_, _, h, rfl⟩, fun ⟨_, _, x, hx, e⟩ => ?_⟩
    · have := Ix.blk_le a
      omega
    · change (reGL (ixZero R t)).symm g ∈ P.J
      rwa [show (reGL (ixZero R t)).symm g = x from Units.ext (by rw [reGL_symm_val, e]; rfl)]
  | succ j ih =>
    have e : g ∈ (P.iter t μ hμ (j + 1)).J ↔
        (reGL (ixSucc R t j)).symm g ∈ (P.iter t μ hμ j).stepJ t := Iff.rfl
    rw [e, TypeDatum.mem_stepJ_iff]
    constructor
    · rintro ⟨h0, ⟨u, hu, eu⟩, hC⟩
      obtain ⟨-, h1, x, hx, ex⟩ := (ih u).1 hu
      refine ⟨(reGL_symm_mem_KO _ _).1 h0, fun a b hab => ?_, x, hx, ?_⟩
      · obtain ⟨a, rfl⟩ := (ixSucc R t j).surjective a
        obtain ⟨b, rfl⟩ := (ixSucc R t j).surjective b
        rcases a with a | a <;> rcases b with b | b
        · rw [blk_ixSucc_inl, blk_ixSucc_inl] at hab
          have := h1 a b hab
          rw [eu] at this
          exact this
        · rw [blk_ixSucc_inl, blk_ixSucc_inr] at hab
          have := Ix.blk_le a
          omega
        · exact hC a b
        · exact absurd hab (lt_irrefl _)
      · rw [ex, eu]; rfl
    · rintro ⟨h0, h1, x, hx, ex⟩
      have h0' := (reGL_symm_mem_KO (ixSucc R t j) g).2 h0
      have hC : MaxM ((reGL (ixSucc R t j)).symm g).val.toBlocks₂₁ := fun a b =>
        h1 (ixSucc R t j (.inr a)) (ixSucc R t j (.inl b)) (by
          rw [blk_ixSucc_inl, blk_ixSucc_inr]; exact Nat.lt_succ_of_le (Ix.blk_le b))
      obtain ⟨u, hu, eu⟩ := (exists_diag_blocks h0' hC).1
      refine ⟨h0', ⟨u, (ih u).2 ⟨hu, fun a b hab => ?_, x, hx, ?_⟩, eu⟩, hC⟩
      · rw [eu]
        exact h1 (ixSucc R t j (.inl a)) (ixSucc R t j (.inl b)) (by rwa [blk_ixSucc_inl, blk_ixSucc_inl])
      · rw [ex, eu]; rfl

end GlobalTheory.FunObj.TieLev

namespace GlobalTheory.FunObj.TieLev

section Num
variable {R : Type} {r t j a : ℕ}

def IsIxR (e₀ : R ≃ Fin r) (ea : Ix R (Fin t) j ≃ Fin a) : Prop :=
  a = r + j * t ∧ (∀ i, (ea (.inl i)).val = (e₀ i).val) ∧ ∀ c s, (ea (.inr (c, s))).val = r + (s.val + t * c.val)

theorem isIxR_of_isIx {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a}
    (h : GlobalTheory.FunObj.Comparison₂.IsIx ((Equiv.sumCongr e₀.symm (Equiv.refl (Fin j × Fin t))).trans ea)) : IsIxR e₀ ea :=
  ⟨h.1, fun i => by simpa using h.2.1 (e₀ i), fun c s => by simpa using h.2.2 c s⟩

theorem IsIxR.blkOf {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a} (h : IsIxR e₀ ea) (i : Ix R (Fin t) j) :
    Formalism.L2.DIV.blkOf r t (ea i) = i.blk := by
  rcases i with i | ⟨c, s⟩
  · rw [Formalism.L2.DIV.blkOf, if_pos (by rw [h.2.1]; exact (e₀ i).2)]; rfl
  · rw [Formalism.L2.DIV.blkOf, h.2.2, if_neg (by omega), Nat.add_sub_cancel_left, Nat.add_mul_div_left _ _ s.pos,
      Nat.div_eq_of_lt s.2, zero_add]; rfl

variable {b : ℕ} {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a} {eb : Ix R (Fin t) (j + 1) ≃ Fin b}

theorem val_succ_inl (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (i : Ix R (Fin t) j) :
    (eb (ixSucc _ _ j (.inl i))).val = (ea i).val := by
  rcases i with i | ⟨c, s⟩
  · exact (hb.2.1 i).trans (ha.2.1 i).symm
  · exact (hb.2.2 c.castSucc s).trans (ha.2.2 c s).symm

theorem topL_a {κ : Type} [Zero κ] (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (y : Matrix (Fin b) (Fin a) κ)
    (i l : Ix R (Fin t) j) : topL a y (ea i) (ea l) = y (eb (ixSucc _ _ j (.inl i))) (ea l) := by
  have h : (ea i).val < b ∧ (ea l).val < a := ⟨val_succ_inl ha hb i ▸ (eb _).2, (ea l).2⟩
  rw [topL, dif_pos h]
  exact congrArg₂ y (Fin.ext (val_succ_inl ha hb i).symm) rfl

end Num

end GlobalTheory.FunObj.TieLev

namespace GlobalTheory.FunObj.TieLev

section Red
variable {S κ K : Type} [CommRing S] [CommRing κ] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {φ : S →+* κ} {ψ : S →+* K}
variable {R : Type} {r t j a b : ℕ} {e₀ : R ≃ Fin r} {ea : Ix R (Fin t) j ≃ Fin a} {eb : Ix R (Fin t) (j + 1) ≃ Fin b}

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem lowZero_a (h : GlobalTheory.FunObj.Comparison₂.IsRed φ ψ) (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (N : Matrix (Fin b) (Fin a) S) :
    LowZero a (N.map φ) ↔ MaxM (((N.map ψ).submatrix eb ea).submatrix (ixSucc _ _ j) id).toRows₂ := by
  refine ⟨fun H i l => (h.ker _).1 (H _ _ ?_ (ea l).2), fun H i l hi _ => ?_⟩
  · have := hb.2.2 (Fin.last j) i
    rw [Fin.val_last, mul_comm] at this
    exact ha.1.le.trans (le_of_le_of_eq (by omega) this.symm)
  obtain ⟨i, rfl⟩ := eb.surjective i
  obtain ⟨l, rfl⟩ := ea.surjective l
  obtain ⟨i | i, rfl⟩ := (ixSucc _ _ j).surjective i
  · exact absurd (val_succ_inl ha hb i ▸ hi) (ea i).2.not_ge
  · exact (h.ker _).2 (H i l)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem diagonalBlock_det_blockTriangular (ha : IsIxR e₀ ea) {g : GL (Fin a) κ} (hg : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) (c : Fin j) :
    (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c.val + 1) g : κ) = (Ix.diagonalBlockOfMatrix (g.val.submatrix ea ea) c).det := by
  have hb : Function.Bijective fun s : Fin t =>
      (⟨ea (.inr (c, s)), ha.blkOf _⟩ : {i : Fin a // Formalism.L2.DIV.blkOf r t i = c.val + 1}) := by
    refine ⟨fun s s' h => by simpa using congrArg Subtype.val h, fun ⟨i, hi⟩ => ?_⟩
    obtain ⟨i | ⟨c', s⟩, rfl⟩ := ea.surjective i
    · exact absurd ((ha.blkOf _).symm.trans hi) (Nat.succ_ne_zero _).symm
    · obtain rfl : c' = c := Fin.ext (Nat.succ_injective ((ha.blkOf _).symm.trans hi))
      exact ⟨s, rfl⟩
  rw [Formalism.L2.DIV.diag_block_det_val _ hg, ← det_submatrix_equiv_self (Equiv.ofBijective _ hb)]
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem firstBlock_topBlockMatrix_reduction_eq (ha : IsIxR e₀ ea) (hb : IsIxR e₀ eb) (hr : r ≤ a) (N : Matrix (Fin b) (Fin a) S) {g : GL (Fin a) κ}
    (hg : g.val = topL a (N.map φ)) (hbt : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) :
    (Formalism.L2.DIV.upperLeftBlock hr g).val.submatrix e₀ e₀ =
      ((N.submatrix (fun i => eb (ixSucc _ _ j (.inl i))) ea).submatrix Sum.inl Sum.inl).map φ := by
  ext i l
  rw [submatrix_apply, Formalism.L2.DIV.upper_block_val_submatrix hr (Formalism.L2.DIV.blockTri_blkOf_le r t hbt), submatrix_apply, hg,
    show Fin.castLE hr (e₀ i) = ea (.inl i) from Fin.ext (ha.2.1 i).symm,
    show Fin.castLE hr (e₀ l) = ea (.inl l) from Fin.ext (ha.2.1 l).symm, topL_a ha hb]
  rfl

end Red

end GlobalTheory.FunObj.TieLev

namespace GlobalTheory.FunObj.TieLev

theorem iterPhi_read : ∀ (S κ k : Type) [CommRing S] [CommRing κ] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : S →+* κ) (ψ : S →+* k), GlobalTheory.FunObj.Comparison₂.IsRed φ ψ → ∀ (R : Type) [Fintype R] [DecidableEq R] (r t j a b : ℕ) (e₀ : R ≃ Fin r) (ea : Ix R (Fin t) j ≃ Fin a) (eb : Ix R (Fin t) (j + 1) ≃ Fin b), GlobalTheory.FunObj.Comparison₂.IsIx ((Equiv.sumCongr e₀.symm (Equiv.refl (Fin j × Fin t))).trans ea) → GlobalTheory.FunObj.Comparison₂.IsIx ((Equiv.sumCongr e₀.symm (Equiv.refl (Fin (j + 1) × Fin t))).trans eb) → ∀ (hr : r ≤ a) (P : TypeDatum k R) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ c, IsTame (μ c)) (χ : ℕ → κˣ →* ℂˣ), (∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat φ ψ (χ (c + 1)) (μ (c + 1))) → ∀ Rd : P.J → GL (Fin r) κ → Prop, (∀ (x : P.J) (g : GL (Fin r) κ) (M : Matrix R R S), g.val.submatrix e₀ e₀ = M.map φ → (Rd x g ↔ MaxM ((x : GL R k).val - M.map ψ))) → ∀ N : Matrix (Fin b) (Fin a) S, (P.iterPhi (Fin t) μ hμ j ((N.map ψ).submatrix eb ea) ≠ 0 → LowZero a (N.map φ) ∧ ∃ g : GL (Fin a) κ, g.val = topL a (N.map φ) ∧ g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧ ∃ x, Rd x (Formalism.L2.DIV.upperLeftBlock hr g)) ∧ (LowZero a (N.map φ) → ∀ g : GL (Fin a) κ, g.val = topL a (N.map φ) → g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) → ∀ x, Rd x (Formalism.L2.DIV.upperLeftBlock hr g) → P.iterPhi (Fin t) μ hμ j ((N.map ψ).submatrix eb ea) = (P.lam x : ℂ) * (∏ c ∈ Finset.range j, (χ (c + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c + 1) g) : ℂ)) * (χ (j + 1) (Matrix.GeneralLinearGroup.det g) : ℂ)⁻¹) := by
  intro S κ k _ _ _ _ _ _ φ ψ h R _ _ r t j a b e₀ ea eb hA hB hr P μ hμ χ hχ Rd hRd N
  have ha := isIxR_of_isIx hA
  have hb := isIxR_of_isIx hB
  set M := N.submatrix (fun i => eb (ixSucc _ _ j (.inl i))) ea with hM
  have hy : (topL a (N.map φ)).submatrix ea ea = M.map φ := Matrix.ext (topL_a ha hb (N.map φ))
  have e1 : ∀ g : GL (Fin a) κ, g.val = topL a (N.map φ) → (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ↔
      ∀ i l : Ix R (Fin t) j, l.blk < i.blk → valuation k (ψ (M i l)) < 1) := fun g hg => by
    rw [Formalism.L2.DIV.mem_blockTri, hg, ea.surjective.forall₂]
    refine forall₂_congr fun i l => ?_
    rw [ha.blkOf, ha.blkOf, ← h.ker]
    exact imp_congr_right fun _ => iff_of_eq (congrArg (· = 0) (congrFun (congrFun hy i) l))
  have e3 : (topL a (N.map φ)).det = (M.map φ).det := by rw [← hy, det_submatrix_equiv_self]
  have hsub : ∀ g' : GL (Ix R (Fin t) j) k, g'.val = M.map ψ →
      g'.val.submatrix Sum.inl Sum.inl = (M.submatrix Sum.inl Sum.inl).map ψ := fun g' e => by rw [e]; rfl
  refine ⟨fun h0 => ?_, fun hlow g hg hbt x hx => ?_⟩
  · rw [TypeDatum.iterPhi, TypeDatum.Phi_ne_zero_iff] at h0
    obtain ⟨⟨g', hg', e'⟩, hlow⟩ := h0
    have e'' : g'.val = M.map ψ := e'
    obtain ⟨k1, k2, x, hx, ex⟩ := (mem_iter_gen P μ hμ j g').1 hg'
    obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 (e3 ▸ (h.isUnit_det_iff M).2 ⟨g', k1, e''⟩)
    have hbt : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := (e1 g hg).2 fun i l hil => by
      have := k2 i l hil
      rwa [e''] at this
    refine ⟨(lowZero_a h ha hb N).2 hlow, g, hg, hbt, ⟨x, hx⟩, (hRd ⟨x, hx⟩ _ _ (firstBlock_topBlockMatrix_reduction_eq ha hb hr N hg hbt)).2 ?_⟩
    change MaxM (x.val - _)
    rw [ex, hsub g' e'', sub_self]
    exact maxM_zero
  · have hmx := (hRd x _ _ (firstBlock_topBlockMatrix_reduction_eq ha hb hr N hg hbt)).1 hx
    obtain ⟨g', k1, e''⟩ := (h.isUnit_det_iff M).1 (e3 ▸ hg ▸ (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
    have hx' : MaxM (g'.val.submatrix Sum.inl Sum.inl - (x : GL R k).val) := fun i l => by
      rw [hsub g' e'', Matrix.sub_apply, ← neg_sub, Valuation.map_neg]
      exact hmx i l
    obtain ⟨x', hx'J, ex'⟩ := P.exists_of_congr x.2 hx'
    have hJ : g' ∈ (P.iter (Fin t) μ hμ j).J := (mem_iter_gen P μ hμ j g').2
      ⟨k1, fun i l hil => by rw [e'']; exact (e1 g hg).1 hbt i l hil, x', hx'J, ex'⟩
    obtain ⟨g₀, D, e0, hD, el⟩ := GlobalTheory.SymBridge.iter_lam_closed k R (Fin t) P μ hμ j ⟨g', hJ⟩
    have hl : P.lam g₀ = P.lam x := by
      have h5 : MaxM ((g₀ : GL R k).val - (x : GL R k).val) := by
        rw [e0]; exact hx'
      have := P.lam_eq_one (x⁻¹ * g₀) (inv_mul_mem_KOne (P.le_KO x.2) h5)
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    have hblk : ∀ c : Fin j, μ (c.val + 1) (Matrix.GeneralLinearGroup.det (D c)) =
        χ (c.val + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c.val + 1) g) := fun c =>
      ((hχ c c.2.le).det (Ix.diagonalBlockOfMatrix M c) (by rw [diagonalBlock_det_blockTriangular ha hbt c, hg, hy]; rfl)
        (by rw [Matrix.GeneralLinearGroup.val_det_apply, (hD c).2, e'']; rfl)).symm
    have hdet : μ (j + 1) (Matrix.GeneralLinearGroup.det g') = χ (j + 1) (Matrix.GeneralLinearGroup.det g) :=
      ((hχ j le_rfl).det M (by rw [← hy, det_submatrix_equiv_self, ← hg]; rfl)
        (by rw [Matrix.GeneralLinearGroup.val_det_apply, e''])).symm
    rw [TypeDatum.iterPhi, TypeDatum.Phi_of_mem (x := ((N.map ψ).submatrix eb ea).submatrix (ixSucc _ _ j) id) _ _
      ⟨g', hJ⟩ e'' ((lowZero_a h ha hb N).1 hlow), el, hl, hdet, Units.val_mul, Units.coe_prod,
      Units.val_inv_eq_inv_val, Finset.prod_range]
    simp only [hblk]

end GlobalTheory.FunObj.TieLev
