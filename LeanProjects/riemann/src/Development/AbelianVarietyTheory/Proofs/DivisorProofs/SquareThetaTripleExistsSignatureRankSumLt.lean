import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem hasSignature_of_hasSig_conj {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (M.map (starRingEnd ℂ)) r s) : Formalism.UG.HasSignature M r s := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr hn.symm).trans finSumFinEquiv.symm
  let P : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := A.submatrix e.symm id
  have h2 := congrArg (fun X => X.map (starRingEnd ℂ)) hA
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.fromBlocks_map] at h2
  have hc : (starRingEnd ℂ) ∘ (starRingEnd ℂ) = id := funext fun z => Complex.conj_conj z
  have hc' : (starRingEnd ℂ) ∘ (star : ℂ → ℂ) = id := funext fun z => Complex.conj_conj z
  simp only [hc, hc', Matrix.map_id] at h2
  have key : (A.map (starRingEnd ℂ))ᵀ * M * A = Formalism.UG.Jpq r s := by
    rw [Formalism.UG.Jpq, h2]
    congr 1
    · ext a b; simp [Matrix.one_apply]
    · ext a b; simp
    · ext a b; simp
    · ext a b; simp [Matrix.one_apply]
  have key2 : Formalism.UG.cT (starRingEnd ℂ) P * Matrix.reindex e e M * P = Formalism.UG.Jpq r s := by
    rw [← key, Formalism.UG.cT, Matrix.reindex_apply]
    have hm : (A.submatrix e.symm id).map (starRingEnd ℂ) = (A.map (starRingEnd ℂ)).submatrix e.symm id := rfl
    simp only [P, hm, Matrix.transpose_submatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hinv : (Formalism.UG.Jpq r s * (Formalism.UG.cT (starRingEnd ℂ) P * Matrix.reindex e e M)) * P = 1 := by
    rw [Matrix.mul_assoc, key2, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
    simp
  exact ⟨e, ⟨P, _, mul_eq_one_comm.mp hinv, hinv⟩, key2⟩

theorem squareTriple_sig_rank : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  intro D T L sc G W t i j hT M hM
  obtain ⟨e, Bs, Γ, X, om, om', h, hTr, -⟩ := hT.of_forall hM
  refine ⟨Γ.p, ?_, ?_⟩
  · obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    obtain ⟨τ, hτ, -⟩ := h.cart w
    refine ⟨τ, hasSignature_of_hasSig_conj ?_⟩
    have hs := hTr.geo.hV.sig w
    rw [h.JW, one_smul] at hs
    have hmap : (G.V (.grid (↑i + 1) (↑j + 1))).gram.map (Bs.emb w).1 = (gramAt D _ τ).map (starRingEnd ℂ) := by
      ext a b; simp [gramAt, hτ]
    rw [hmap] at hs
    exact hs
  · have hc := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    have hb := hTr.geo.eBig
    have hl := hTr.geo.lt
    dsimp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV₁] at hc hb hl
    show (G.V (.grid (↑i) (↑j + 1))).rank + (G.V (.grid (↑i + 1) ↑j)).rank < _
    omega

end GlobalTheory.FunObj

end
