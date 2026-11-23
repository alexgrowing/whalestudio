import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeStabilizerIffScaledFrameConj
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EmbK

open GlobalTheory.CompanionTheory.JacobiMaps

section Entries

variable {R : Type} [CommRing R] {n r t : ℕ}

theorem block_matrix_apply_inl_inl (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = a i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem block_matrix_apply_inl_inr (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = b i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]

theorem block_matrix_apply_inr_inl (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = c i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]

theorem block_matrix_apply_inr_inr (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = d i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

theorem entry (hn : r + t = n) (a b c d : Matrix (Fin t) (Fin t) R) (i j : Fin (n + n)) :
    blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d) i j = (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) i j ∨
    ∃ i' j', blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d) i j = blk4 a b c d i' j' ∧
      (1 : Matrix (Fin (t + t)) (Fin (t + t)) R) i' j' = (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) i j := by
  have h1 : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) =
      blk4 (bl hn 1 0 0 1) (bl hn 0 0 0 0) (bl hn 0 0 0 0) (bl hn 1 0 0 1) := by
    have z : bl hn (0 : Matrix (Fin r) (Fin r) R) 0 0 (0 : Matrix (Fin t) (Fin t) R) = 0 := blockMatrix_zero hn
    rw [blockRowSubstitution_one, z, GlobalTheory.StdUnn.Model.block_matrix_one]
  have h2 : (1 : Matrix (Fin (t + t)) (Fin (t + t)) R) = blk4 1 0 0 1 := GlobalTheory.StdUnn.Model.block_matrix_one.symm
  rw [h1, h2]
  have bll : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = a i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]
  have blr : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = b i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]
  have brl : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = c i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]
  have brr : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = d i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i <;>
    obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j <;>
    rcases i with i | i <;> rcases j with j | j <;>
    simp only [block_matrix_apply_inl_inl, block_matrix_apply_inl_inr, block_matrix_apply_inr_inl, block_matrix_apply_inr_inr, bll, blr, brl, brr, true_or] <;>
    first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, (block_matrix_apply_inl_inl a b c d i j).symm, block_matrix_apply_inl_inl _ _ _ _ i j⟩
    | exact Or.inr ⟨_, _, (block_matrix_apply_inl_inr a b c d i j).symm, block_matrix_apply_inl_inr _ _ _ _ i j⟩
    | exact Or.inr ⟨_, _, (block_matrix_apply_inr_inl a b c d i j).symm, block_matrix_apply_inr_inl _ _ _ _ i j⟩
    | exact Or.inr ⟨_, _, (block_matrix_apply_inr_inr a b c d i j).symm, block_matrix_apply_inr_inr _ _ _ _ i j⟩

theorem map_one_apply {T : Type} [CommRing T] {N : ℕ} (f : R →+* T) (i j : Fin N) :
    f ((1 : Matrix (Fin N) (Fin N) R) i j) = (1 : Matrix (Fin N) (Fin N) T) i j := by
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

end Entries

variable {D : D7} {n r t : ℕ} {hn : r + t = n}

theorem emb_entries_one (M : Maps D hn) {T : Type} [CommRing T] (f : AE D →+* T) {u : G D t}
    (hu : ∀ i j, f (mat u i j) = (1 : Matrix (Fin (t + t)) (Fin (t + t)) T) i j) (i j : Fin (n + n)) :
    f (mat (M.emb u) i j) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) T) i j := by
  rw [M.emb_mat u _ _ _ _ (block_matrix_of_blocks (mat u)).symm]
  rcases entry hn (b11 (mat u)) (b12 (mat u)) (b21 (mat u)) (b22 (mat u)) i j with h | ⟨i', j', h, h'⟩
  · rw [h, map_one_apply]
  · rw [h, block_matrix_of_blocks, hu i' j', ← map_one_apply f i' j', h', map_one_apply]

theorem emb_entries_mem (M : Maps D hn) {T : Type} [CommRing T] (f : AE D →+* T) (P : Subring T) {u : G D t}
    (hu : ∀ i j, f (mat u i j) ∈ P) (i j : Fin (n + n)) : f (mat (M.emb u) i j) ∈ P := by
  rw [M.emb_mat u _ _ _ _ (block_matrix_of_blocks (mat u)).symm]
  rcases entry hn (b11 (mat u)) (b12 (mat u)) (b21 (mat u)) (b22 (mat u)) i j with h | ⟨i', j', h, -⟩
  · rw [h, map_one_apply]
    by_cases e : i = j
    · subst e; simpa using P.one_mem
    · simpa [Matrix.one_apply_ne e] using P.zero_mem
  · rw [h, block_matrix_of_blocks]
    exact hu i' j'

theorem stab_entries {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {m : GL (Fin N) (Fv F v ⊗[F] E)}
    (h : m ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v)) (i j : Fin N) :
    m.1 i j ∈ intLoc F E v ∧ (m⁻¹).1 i j ∈ intLoc F E v := by
  have hs : (Pi.single j 1 : Fin N → Fv F v ⊗[F] E) ∈ latLoc F (stdLattice E N) v := by
    refine mem_latLoc_stdLattice.2 fun k => ?_
    by_cases e : k = j
    · subst e; simpa using (intLoc F E v).one_mem
    · simpa [Pi.single_eq_of_ne e] using (intLoc F E v).zero_mem
  constructor
  · have h1 := mem_latLoc_stdLattice.1 ((h _).1 hs) i
    simpa using h1
  · have e : m.1 *ᵥ ((m⁻¹).1 *ᵥ (Pi.single j 1 : Fin N → Fv F v ⊗[F] E)) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have h2 : (m⁻¹).1 *ᵥ (Pi.single j 1 : Fin N → Fv F v ⊗[F] E) ∈ latLoc F (stdLattice E N) v :=
      (h _).2 (by rw [e]; exact hs)
    have h1 := mem_latLoc_stdLattice.1 h2 i
    simpa using h1

theorem emb_mem_KOff : ∀ {D : D7} {n r t : ℕ} {hn : r + t = n} (M : Maps D hn) (S : Finset (Pl D)) (u : G D t),
    u ∈ KOff D t S → M.emb u ∈ KOff D n S := by
  intro D n r t hn M S u hu
  obtain ⟨hf, h1, h2⟩ := mem_levelOff.1 hu
  refine mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · have hw := mem_finPts_iff_forall.1 hf w
    have ent : ∀ i j, compInf D.host.F D.host.E w (mat u i j) = (1 : Matrix (Fin (t + t)) (Fin (t + t)) _) i j := fun i j => by
      have e := congrArg (fun g => (matHom _ D.sp.cm.sig (Jst D t) g).1 i j) hw
      simp only [map_one, Units.val_one] at e
      exact e
    apply matHom_injective
    apply Units.ext
    ext i j
    rw [matHom_projArch, map_one]
    exact emb_entries_one M _ ent i j
  · have ent : ∀ i j, cv D v (mat u i j) = (1 : Matrix (Fin (t + t)) (Fin (t + t)) _) i j := fun i j => by
      have e := congrArg (fun g => (matHom _ D.sp.cm.sig (Jst D t) g).1 i j) (h1 v hv)
      simp only [map_one, Units.val_one] at e
      exact e
    apply matHom_injective
    apply Units.ext
    ext i j
    rw [matHom_proj, map_one]
    exact emb_entries_one M _ ent i j
  · have key : ∀ x : G D t, proj D.sp.cm.sig (Jst D t) v x ∈ stabLoc D.sp.cm.sig (Jst D t) (stdLattice D.host.E (t + t)) v →
        ∀ i j, (matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v (M.emb x))).1 i j ∈ intLoc D.host.F D.host.E v := by
      intro x hx i j
      exact emb_entries_mem M (cv D v) _ (fun i j => (stab_entries hx i j).1) i j
    refine GlobalTheory.StdUnn.StabFin.mem_stab_std (key u (h2 v hv)) fun i j => ?_
    rw [← map_inv, ← map_inv, ← map_inv]
    exact key u⁻¹ (by rw [map_inv]; exact inv_mem (h2 v hv)) i j

end GlobalTheory.CompanionTheory.EmbK
