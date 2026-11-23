import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul
open MeasureTheory Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.OrbDesc.StabIndex

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}

def bdiag (e : ι ≃ Fin a ⊕ Fin b) (A : Matrix ι ι K) : Matrix ι ι K :=
  Matrix.of fun i j => if side e i = side e j then A i j else 0

theorem bdiag_mul (e : ι ≃ Fin a ⊕ Fin b) {A B : Matrix ι ι K}
    (hA : A.BlockTriangular (side e)) (hB : B.BlockTriangular (side e)) :
    bdiag e (A * B) = bdiag e A * bdiag e B := by
  ext i j
  simp only [bdiag, Matrix.of_apply, Matrix.mul_apply]
  split_ifs with hij
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hik : side e i = side e k
    · rw [if_pos hik, if_pos (hik.symm.trans hij)]
    · rw [if_neg hik, zero_mul]
      rcases lt_or_gt_of_ne (Ne.symm hik) with h | h
      · rw [hA h, zero_mul]
      · rw [hB (hij ▸ h), mul_zero]
  · symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : side e i = side e k
    · rw [if_neg (fun h => hij (hik.trans h)), mul_zero]
    · rw [if_neg hik, zero_mul]

theorem bdiag_one (e : ι ≃ Fin a ⊕ Fin b) : bdiag e (1 : Matrix ι ι K) = 1 := by
  ext i j
  simp only [bdiag, Matrix.of_apply, Matrix.one_apply]
  split_ifs with h1 h2 <;> simp_all

theorem bdiag_of_levi (e : ι ≃ Fin a ⊕ Fin b) {g : GL ι K} (hg : g ∈ blockLevi e) :
    bdiag e (g : Matrix ι ι K) = g := by
  ext i j
  simp only [bdiag, Matrix.of_apply]
  split_ifs with h
  · rfl
  · have h1 : (g : Matrix ι ι K).BlockTriangular (side e) := hg.1
    have h2 : (g : Matrix ι ι K).BlockTriangular (fun i => OrderDual.toDual (side e i)) := hg.2
    rcases lt_or_gt_of_ne (Ne.symm h) with h' | h'
    · exact (h1 h').symm
    · exact (h2 (show OrderDual.toDual (side e j) < OrderDual.toDual (side e i) from h')).symm

theorem uMat_blockTriangular (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) :
    (uMat e X).BlockTriangular (side e) := by
  intro i j hij
  simp only [uMat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  simp only [side] at hij
  rcases hi : e i with x | x <;> rcases hj : e j with y | y <;> simp_all
  all_goals exact absurd hij (by decide)

theorem bdiag_uMat (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) :
    bdiag e (uMat e X) = 1 := by
  ext i j
  simp only [bdiag, uMat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.of_apply,
    Matrix.one_apply]
  split_ifs with hs hij hij
  · subst hij
    generalize e i = u
    rcases u with x | x <;> simp
  · have h' : e i ≠ e j := e.injective.ne hij
    simp only [side] at hs
    revert hs h'
    generalize e i = u
    generalize e j = v
    rcases u with x | x <;> rcases v with y | y <;> simp_all
  · exact absurd (by rw [hij]) hs
  · rfl

section Top

variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {a b : ℕ}

def bdiagHom (e : ι ≃ Fin a ⊕ Fin b) : blockPar (K := K) e →* GL ι K where
  toFun p := ⟨bdiag e (p : GL ι K), bdiag e (((p : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K),
    by rw [← bdiag_mul e p.2 ((blockPar e).inv_mem p.2)]; simp [bdiag_one],
    by rw [← bdiag_mul e ((blockPar e).inv_mem p.2) p.2]; simp [bdiag_one]⟩
  map_one' := Units.ext (by simp [bdiag_one])
  map_mul' p q := Units.ext (by
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact bdiag_mul e p.2 q.2)

theorem continuous_bdiag (e : ι ≃ Fin a ⊕ Fin b) : Continuous (bdiag (K := K) e) :=
  continuous_matrix fun i j => by
    by_cases h : side e i = side e j
    · simp only [bdiag, Matrix.of_apply, if_pos h]
      exact continuous_id.matrix_elem i j
    · simp only [bdiag, Matrix.of_apply, if_neg h]
      exact continuous_const

theorem continuous_bdiagHom (e : ι ≃ Fin a ⊕ Fin b) : Continuous (bdiagHom (K := K) e) := by
  refine Units.continuous_iff.2 ⟨(continuous_bdiag e).comp (Units.continuous_val.comp continuous_subtype_val), ?_⟩
  show Continuous fun p : blockPar (K := K) e => bdiag e (((p : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K)
  exact (continuous_bdiag e).comp (Units.continuous_val.comp (continuous_inv.comp continuous_subtype_val))

theorem isClosed_blockPar (e : ι ≃ Fin a ⊕ Fin b) (h0 : IsClosed ({0} : Set K)) :
    IsClosed (blockPar (K := K) e : Set (GL ι K)) := by
  have : (blockPar (K := K) e : Set (GL ι K)) = ⋂ i, ⋂ j, ⋂ (_ : side e j < side e i),
      {g : GL ι K | (g : Matrix ι ι K) i j ∈ ({0} : Set K)} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_singleton_iff]
    rfl
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    h0.preimage (Units.continuous_val.matrix_elem i j)

end Top

theorem relIndex_ne_zero_of_subset_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] {W S : Subgroup G} (hW : IsOpen (W : Set G)) {Q : Set G} (hQ : IsCompact Q)
    (hS : (S : Set G) ⊆ Q) : W.relIndex S ≠ 0 := by
  set C := S.topologicalClosure
  have hCQ : (C : Set G) ⊆ Q := by
    rw [Subgroup.topologicalClosure_coe]; exact closure_minimal hS hQ.isClosed
  have hC : IsCompact (C : Set G) := hQ.of_isClosed_subset S.isClosed_topologicalClosure hCQ
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hWo : IsOpen ((W.subgroupOf C : Subgroup C) : Set C) := by
    rw [Subgroup.coe_subgroupOf]; exact hW.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hWo
  have h1 : W.relIndex C ≠ 0 := Subgroup.index_ne_zero_of_finite
  intro h
  exact h1 (Subgroup.relIndex_eq_zero_of_le_right S.le_topologicalClosure h)

theorem relIndex_twCent_inf_ne_zero : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b) (γ : GL ι K),
  GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ≤ GlobalTheory.OrbDesc.blockLevi e →
  ∀ K' : Subgroup (GL ι K), IsOpen (K' : Set (GL ι K)) → IsCompact (K' : Set (GL ι K)) →
  ∀ x ∈ GlobalTheory.OrbDesc.blockPar e,
    (GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ⊓ (GlobalTheory.OrbDesc.blockPar e ⊓ K').map (MulAut.conj x).toMonoidHom).relIndex
      (GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ⊓
        ((GlobalTheory.OrbDesc.blockPar e ⊓ K') ⊔ GlobalTheory.OrbDesc.blockUni e).map (MulAut.conj x).toMonoidHom) ≠ 0 := by
  intro K _ _ _ _ ι _ _ a b e γ hT K' hK'o hK'c x hx
  set T := GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ
  set P := blockPar (K := K) e
  set cx := (MulAut.conj x).toMonoidHom
  set W := K'.map cx
  set S := T ⊓ ((P ⊓ K') ⊔ blockUni e).map cx
  set A := T ⊓ (P ⊓ K').map cx
  have hTP : T ≤ P := hT.trans inf_le_left
  have hWmem : ∀ g, g ∈ W ↔ x⁻¹ * g * x ∈ K' := fun g => by
    simp only [W, cx]; rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hWo : IsOpen (W : Set (GL ι K)) := by
    have : (W : Set (GL ι K)) = (fun g => x⁻¹ * g * x) ⁻¹' (K' : Set (GL ι K)) := Set.ext hWmem
    rw [this]; exact hK'o.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hSWA : W ⊓ S ≤ A := by
    rintro g ⟨hgW, hgT, -⟩
    refine ⟨hgT, Subgroup.mem_map_equiv.2 ?_⟩
    rw [MulAut.conj_symm_apply]
    exact ⟨P.mul_mem (P.mul_mem (P.inv_mem hx) (hTP hgT)) hx, (hWmem g).1 hgW⟩
  have key : W.relIndex S ≠ 0 := by
    by_cases h0 : IsClosed ({0} : Set K)
    · haveI : T1Space K := IsTopologicalAddGroup.t1Space K h0
      haveI : T2Space (GL ι K) := Units.isEmbedding_embedProduct.t2Space
      have hPc : IsClosed (P : Set (GL ι K)) := isClosed_blockPar e h0
      set π := bdiagHom (K := K) e
      have hWc : IsCompact (W : Set (GL ι K)) := by
        have : (W : Set (GL ι K)) = (fun g => x * g * x⁻¹) '' (K' : Set (GL ι K)) := rfl
        rw [this]; exact hK'c.image ((continuous_const.mul continuous_id).mul continuous_const)
      have hQ : IsCompact (π '' {p : P | (p : GL ι K) ∈ W}) :=
        (hPc.isClosedEmbedding_subtypeVal.isCompact_preimage hWc).image (continuous_bdiagHom e)
      refine relIndex_ne_zero_of_subset_compact hWo hQ ?_
      rintro s ⟨hsT, hsmap⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hsmap
      set L' := (P ⊓ K').subgroupOf P
      have hZ : (P ⊓ K') ⊔ blockUni e ≤ ((L'.map π).comap π).map P.subtype := by
        refine sup_le ?_ ?_
        · intro g hg
          exact ⟨⟨g, hg.1⟩, ⟨⟨g, hg.1⟩, hg, rfl⟩, rfl⟩
        · rintro g ⟨X, rfl⟩
          have hgP : uHom e X ∈ P := uMat_blockTriangular e X.toAdd
          refine ⟨⟨_, hgP⟩, ?_, rfl⟩
          show π ⟨_, hgP⟩ ∈ L'.map π
          have : π ⟨_, hgP⟩ = 1 := Units.ext (bdiag_uMat e X.toAdd)
          rw [this]; exact (L'.map π).one_mem
      obtain ⟨p, hp, hpy⟩ := hZ hy
      obtain ⟨l, hl, hlp⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hp)
      set px : P := ⟨x, hx⟩
      refine ⟨px * l * px⁻¹, ?_, ?_⟩
      · show x * (l : GL ι K) * x⁻¹ ∈ W
        rw [hWmem]
        simpa [mul_assoc] using (Subgroup.mem_subgroupOf.1 hl).2
      · have hs : cx y ∈ P := hTP hsT
        have e1 : px * p * px⁻¹ = ⟨cx y, hs⟩ :=
          Subtype.ext (by simp [cx, px, ← hpy, MulAut.conj_apply])
        rw [map_mul, map_mul, hlp, ← map_mul, ← map_mul, e1]
        exact Units.ext (bdiag_of_levi e (hT hsT))
    · have hI : (⊥ : Ideal K).closure = ⊤ := by
        rcases Ideal.eq_bot_or_top (⊥ : Ideal K).closure with h | h
        · exfalso
          apply h0
          have h' := congrArg (fun I : Ideal K => (I : Set K)) h
          have : closure ({0} : Set K) = {0} := by
            simpa only [Ideal.coe_closure, Submodule.bot_coe] using h'
          exact closure_eq_iff_isClosed.mp this
        · exact h
      have hsp0 : ∀ y : K, (0 : K) ⤳ y := fun y => by
        rw [specializes_iff_mem_closure]
        have : y ∈ (⊥ : Ideal K).closure := hI ▸ Submodule.mem_top
        have h2 : y ∈ (((⊥ : Ideal K).closure : Ideal K) : Set K) := this
        simpa only [Ideal.coe_closure, Submodule.bot_coe] using h2
      have hsp : ∀ c y : K, c ⤳ y := fun c y => by
        have := (hsp0 (y - c)).map (continuous_add_right c)
        simpa using this
      have hspM : ∀ A B : Matrix ι ι K, A ⤳ B := fun A B =>
        specializes_pi.2 fun i => specializes_pi.2 fun j => hsp _ _
      have hspG : ∀ g h : GL ι K, g ⤳ h := fun g h => by
        rw [← Units.isEmbedding_embedProduct.isInducing.specializes_iff]
        simp only [Units.embedProduct_apply]
        exact specializes_prod.2 ⟨hspM _ _, (hspM _ _).map MulOpposite.continuous_op⟩
      have hall : ∀ g, g ∈ W := fun g => (hspG g 1).mem_open hWo W.one_mem
      rw [Subgroup.relIndex_eq_one.mpr (fun g _ => hall g)]
      exact one_ne_zero
  intro h
  apply key
  rw [← Subgroup.inf_relIndex_right]
  exact Subgroup.relIndex_eq_zero_of_le_left hSWA h

end GlobalTheory.OrbDesc.StabIndex
