import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexUniformisationHarrisTaylorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOfPeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyModuliMapOfMarkedPeriodIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtCorrespondOfCartesianStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem Model.fineAt_univ : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N) h hL, 0 < N → N.Coprime p →
    b.IsType σ ρ → FineAt (M.univ.fam h hL) σ ρ N (D.Cls N) := by
  intro p _ D R _ b N σ ρ M h hL hN hNp hty
  have tr : ∀ (o : Obj b N (spMap σ)) (y : Sp ℂ ⟶ M.X) (m : ObjMap o M.univ y), y ≫ M.s = spMap σ →
      ∀ h' hL' (D' : PLat D.O D.inv) t Q,
        (∀ e', UnifAt (o.fam h' hL') σ ρ N D' t Q (𝟙 _) e' → ∃ e, UnifAt (M.univ.fam h hL) σ ρ N D' t Q y e) ∧
        (∀ e, UnifAt (M.univ.fam h hL) σ ρ N D' t Q y e → ∃ e', UnifAt (o.fam h' hL') σ ρ N D' t Q (𝟙 _) e') := by
    intro o y m hy h' hL' D' t Q
    have key := GlobalTheory.T.uniformisationAt_correspond_of_cartesian D.O D.inv D.g ρ R R σ σ D.La (M.univ.fam h hL) (o.fam h' hL') N y m.φ m.cart m.act
      ((GlobalTheory.T.harrisTaylorObjectPullback_comp_diagonalBundle p D R b N M.X (Sp ℂ) (Sp ℂ) M.s (spMap σ) (spMap σ) M.univ o o y (𝟙 _)).2 m) m.eta D' t Q (𝟙 _)
      (Category.id_comp _) (by erw [Category.id_comp]; exact hy)
    erw [Category.id_comp] at key
    exact ⟨fun e' he' => (key.1 e' he').imp fun e he => he.1, fun e he => (key.2 e he).imp fun e' he' => he'.1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨o, ⟨m⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback p D R b N M.X (Sp ℂ) M.s (spMap σ) y hy M.univ
    obtain ⟨h', hL'⟩ := GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle p D R b N (Sp ℂ) (spMap σ) o
    obtain ⟨D', t, Q, e, hC, hU⟩ := GlobalTheory.T.exists_complexUniformisation_harrisTaylor p D R b N σ ρ o h' hL' hN hNp hty
    obtain ⟨e2, he2⟩ := (tr o y m hy h' hL' D' t Q).1 e hU
    exact ⟨D', t, Q, e2, hC, he2⟩
  · intro D' t Q hC hQ
    obtain ⟨o, h', hL', e, hU⟩ := GlobalTheory.T.exists_harrisTaylor_object_of_period p D R b N σ ρ D' t Q hN hNp hty hC hQ
    obtain ⟨f, ⟨hf, ⟨m⟩⟩, -⟩ := M.rep (Sp ℂ) (spMap σ) o
    obtain ⟨e2, he2⟩ := (tr o f m hf h' hL' D' t Q).1 e hU
    exact ⟨f, e2, he2⟩
  · intro D' D'' t t' Q Q' y y' e e' hU hU' w u hw hQ
    have hy : y ≫ M.s = spMap σ := hU.1
    have hy' : y' ≫ M.s = spMap σ := hU'.1
    obtain ⟨o1, ⟨m1⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback p D R b N M.X (Sp ℂ) M.s (spMap σ) y hy M.univ
    obtain ⟨o2, ⟨m2⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback p D R b N M.X (Sp ℂ) M.s (spMap σ) y' hy' M.univ
    obtain ⟨h1, hL1⟩ := GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle p D R b N (Sp ℂ) (spMap σ) o1
    obtain ⟨h2, hL2⟩ := GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle p D R b N (Sp ℂ) (spMap σ) o2
    obtain ⟨e1, he1⟩ := (tr o1 y m1 hy h1 hL1 D' t Q).2 e hU
    obtain ⟨e2, he2⟩ := (tr o2 y' m2 hy' h2 hL2 D'' t' Q').2 e' hU'
    obtain ⟨m12⟩ := GlobalTheory.T.nonempty_moduliMap_of_marked_period_isometry p D R b N σ ρ o1 o2 h1 hL1 h2 hL2 D' D'' t t' Q Q' e1 e2 w u hN he1 he2 hw hQ
    have hc := (GlobalTheory.T.harrisTaylorObjectPullback_comp_diagonalBundle p D R b N M.X (Sp ℂ) (Sp ℂ) M.s (spMap σ) (spMap σ) M.univ o2 o1 y' (𝟙 _)).1
      ⟨m12⟩ ⟨m2⟩
    obtain ⟨f, -, huniq⟩ := M.rep (Sp ℂ) (spMap σ) o1
    have e1' := huniq y ⟨hy, ⟨m1⟩⟩
    have e2' := huniq (𝟙 _ ≫ y') ⟨by erw [Category.id_comp]; exact hy', hc⟩
    erw [Category.id_comp] at e2'
    rw [e1', e2']

end GlobalTheory.UPel.HT
