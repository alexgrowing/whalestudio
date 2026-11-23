import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.LowerRows

theorem block_mulVec_lower_rows {A : Type} [CommRing A] {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) A)
    (w : Fin (n + n) → A) (i : Fin n) :
    (blk4 a b c d *ᵥ w) (finSumFinEquiv (Sum.inr i)) =
      (c *ᵥ (fun j => w (finSumFinEquiv (Sum.inl j))) +
        d *ᵥ (fun j => w (finSumFinEquiv (Sum.inr j)))) i := by
  unfold blk4
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm, Matrix.fromBlocks_mulVec,
    Sum.elim_inr]
  rfl

def glue {A : Type} {n : ℕ} (y y' : Fin n → A) : Fin (n + n) → A :=
  fun i => Sum.elim y y' (finSumFinEquiv.symm i)

theorem glue_inl {A : Type} {n : ℕ} (y y' : Fin n → A) (j : Fin n) :
    glue y y' (finSumFinEquiv (Sum.inl j)) = y j := by
  simp only [glue, Equiv.symm_apply_apply, Sum.elim_inl]

theorem glue_inr {A : Type} {n : ℕ} (y y' : Fin n → A) (j : Fin n) :
    glue y y' (finSumFinEquiv (Sum.inr j)) = y' j := by
  simp only [glue, Equiv.symm_apply_apply, Sum.elim_inr]

theorem glue_mem {A : Type} {n : ℕ} {S : Set A} {y y' : Fin n → A} (hy : ∀ i, y i ∈ S)
    (hy' : ∀ i, y' i ∈ S) (i : Fin (n + n)) : glue y y' i ∈ S := by
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j
  · rw [glue_inl]; exact hy j
  · rw [glue_inr]; exact hy' j

theorem lower_image {A : Type} [CommRing A] (S : Subring A) {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) A)
    (g h : Matrix (Fin (n + n)) (Fin (n + n)) A) (hgh : g * h = 1) (hg : g = blk4 a b c d)
    (hs : ∀ y, (∀ i, y i ∈ S) ↔ ∀ i, (g *ᵥ y) i ∈ S) (x : Fin n → A) :
    (∃ y, (∀ i, y i ∈ S) ∧ ∃ y', (∀ i, y' i ∈ S) ∧ x = c *ᵥ y + d *ᵥ y') ↔ ∀ i, x i ∈ S := by
  constructor
  · rintro ⟨y, hy, y', hy', rfl⟩ i
    have h1 := (hs (glue y y')).1 (glue_mem (S := (S : Set A)) hy hy') (finSumFinEquiv (Sum.inr i))
    rw [hg, block_mulVec_lower_rows] at h1
    simpa only [glue_inl, glue_inr] using h1
  · intro hx
    set w : Fin (n + n) → A := h *ᵥ glue 0 x with hw
    have hgw : g *ᵥ w = glue 0 x := by
      rw [hw, Matrix.mulVec_mulVec, hgh, Matrix.one_mulVec]
    have hwS : ∀ i, w i ∈ S := (hs w).2 fun i => by
      rw [hgw]
      exact glue_mem (S := (S : Set A)) (fun _ => S.zero_mem) hx i
    refine ⟨fun j => w (finSumFinEquiv (Sum.inl j)), fun _ => hwS _,
      fun j => w (finSumFinEquiv (Sum.inr j)), fun _ => hwS _, funext fun i => ?_⟩
    rw [← block_mulVec_lower_rows a b c d w i, ← hg, hgw, glue_inr]

theorem lower_image_lat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (a b c d : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (g : GL (Fin (n + n)) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (hg : g.1 = blk4 a b c d)
    (hs : ∀ y, y ∈ latLoc F (stdLattice E (n + n)) v ↔ g.1 *ᵥ y ∈ latLoc F (stdLattice E (n + n)) v) :
    {x | ∃ y ∈ latLoc F (stdLattice E n) v, ∃ y' ∈ latLoc F (stdLattice E n) v, x = c.mulVec y + d.mulVec y'} =
      (latLoc F (stdLattice E n) v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) := by
  have hgh : g.1 * (g⁻¹).1 = 1 := by simp
  ext x
  have key := lower_image (intLoc F E v) a b c d g.1 (g⁻¹).1 hgh hg
    (fun y => by
      have := hs y
      rwa [mem_latLoc_stdLattice, mem_latLoc_stdLattice] at this) x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_latLoc_stdLattice]
  exact key

theorem blockMatrix_map {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (a b c d : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    (blk4 a b c d).map (compFin F E v) =
      blk4 (PositivityTheory.SiegelWeilFormula.Gen.matV v a) (PositivityTheory.SiegelWeilFormula.Gen.matV v b)
        (PositivityTheory.SiegelWeilFormula.Gen.matV v c) (PositivityTheory.SiegelWeilFormula.Gen.matV v d) := by
  unfold blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  rfl

theorem lowerRows_onto : ∀ (D : D7) (n : ℕ) (k : G D n) (k₁ k₂ k₃ k₄ : Mx D n n), k ∈ K D n → mat k = blk4 k₁ k₂ k₃ k₄ → ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), {x | ∃ y ∈ (latLoc D.host.F (stdLattice D.host.E n) v), ∃ y' ∈ (latLoc D.host.F (stdLattice D.host.E n) v), x = (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃).mulVec y + (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄).mulVec y'} = ((latLoc D.host.F (stdLattice D.host.E n) v) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
  intro D n k k₁ k₂ k₃ k₄ hk hm v
  have hlev : k ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) :=
    (Subgroup.mem_inf.1 hk).1
  have hst := mem_stabLoc.1 (mem_levelOpen.1 hlev v)
  refine lower_image_lat v (PositivityTheory.SiegelWeilFormula.Gen.matV v k₁) (PositivityTheory.SiegelWeilFormula.Gen.matV v k₂)
    (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃) (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄) _ ?_ hst
  rw [matHom_proj, ← blockMatrix_map, ← hm]
  rfl

end GlobalTheory.CompanionTheory.MM.LowerRows
