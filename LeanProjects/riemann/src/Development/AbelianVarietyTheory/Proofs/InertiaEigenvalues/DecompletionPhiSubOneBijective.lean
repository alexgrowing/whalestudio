import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleEmbeddingFrobeniusGaloisCompatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedSubringTensorWittSaturatedCompleteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEllStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingImageSaturatedAdicClosedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixesEpsilonRootsResGammaTrivialStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittCompletePiAdicModEllStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingImageAddEllPiAdicClosedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittApproxFrobeniusPerfectionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixFrobeniusSubOneBijectiveModSubringStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecWOfMatrixStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

set_option maxHeartbeats 2000000 in

theorem decompletion_matrix (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL)
    (E : EtSit P AI K s LL h W) (H : Set (GQ l))
    (hH : ∀ g, g ∈ H ↔ ∃ hg : g ∈ GK K, W.resΓ ⟨g, hg⟩ = 1)
    (d : ℕ) (Pm : Matrix (Fin d) (Fin d) W.EE) :
    (∀ y : Fin d → RW LL, (∀ i, y i ∈ fixSub AI LL H) → ∃ z : Fin d → RW LL,
      (∀ i, z i ∈ fixSub AI LL H) ∧
        ∀ i, ∃ e, y i - (∑ k, E.tie.ioE (Pm i k) * φRW LL (z k) - z i) = E.tie.ioE e) ∧
    (∀ z : Fin d → RW LL, (∀ i, z i ∈ fixSub AI LL H) →
      (∀ i, ∃ e, ∑ k, E.tie.ioE (Pm i k) * φRW LL (z k) - z i = E.tie.ioE e) →
        ∀ i, ∃ e, z i = E.tie.ioE e) := by
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.T.etaleEmbedding_frobenius_galois_compat l P AI K s LL h W E
  obtain ⟨f1, f2, f3⟩ := GlobalTheory.T.galoisFixedSubringTensorWitt_saturated_complete l P AI LL H
  obtain ⟨p1, p2, -, -⟩ := GlobalTheory.T.frobenius_constants_piAdic_filtration_modEll l P AI LL s
  obtain ⟨s1, s2⟩ := GlobalTheory.T.etaleRing_image_saturated_adicClosed l P AI K s LL h W E
  have hE : ∀ e, E.tie.ioE e ∈ fixSub AI LL H := fun e => mem_fixSub.2 fun g hg => by
    obtain ⟨hg, hg1⟩ := (hH g).1 hg
    exact c2 ⟨g, hg⟩ hg1 e
  have hsub : ∀ y ∈ fixSub AI LL H, y ∈ fixSub AI LL (Hinf K : Set (GQ l)) := fun y hy =>
    mem_fixSub.2 fun g hg => mem_fixSub.1 hy g
      ((hH g).2 ((GlobalTheory.T.cyclotomicTower_fixes_epsilonRoots_resGamma_trivial l P AI K).2 s LL h W g hg))
  have hπ : piR AI LL s ∈ fixSub AI LL H := by rw [← c3]; exact hE _
  have q1 := GlobalTheory.T.galoisFixedTensorWitt_complete_piAdic_modEll l P AI LL s H hπ
  have q2 := GlobalTheory.T.etaleRing_image_add_ell_pi_adic_closed l P AI K s LL h W E
  have q3 := fun y hy => GlobalTheory.T.galoisFixedTensorWitt_approx_frobeniusPerfection l P AI K s LL h W E y (hsub y hy)
  have q4 := GlobalTheory.T.matrix_frobenius_sub_one_bijective_mod_subring (RW LL) W.EE (RA LL) (E.tie.ioE : W.EE →+* RW LL) (inclR LL : RA LL →+* RW LL)
    (φRW LL : RW LL →+* RW LL) (fixSub AI LL H) l (piR AI LL s)
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s) rfl
  simp only [RingHom.coe_coe] at q4
  have q5 := q4 hE f2 (fun e => ⟨W.φE e, (c1 e).symm⟩) p1 p2 c4 f1 s1
  have q6 := q5 q1 q2 q3
  exact q6 f3 s2 d Pm

theorem decompletion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; DecW S E := by
  intro D HW F l _ K s LL h S E
  refine GlobalTheory.T.decW_of_matrix_criterion S E fun d Pm => ?_
  have hm := decompletion_matrix l (D.loc l) (D.locA l) K s LL h ((HW l).W K s LL h)
    ((F l).E K s LL h) {g | ∃ hg : g ∈ GK K, ((HW l).W K s LL h).resΓ ⟨g, hg⟩ = 1}
    (fun _ => Iff.rfl) d Pm
  have hf : ∀ x : RW LL, x ∈ fixSub (D.locA l) LL
      {g | ∃ hg : g ∈ GK K, ((HW l).W K s LL h).resΓ ⟨g, hg⟩ = 1} ↔
      ∀ g ∈ Hker S, S.gR g x = x := fun x =>
    mem_fixSub.trans ⟨fun hx g hg => hx g.1 ⟨g.2, hg⟩, fun hx g ⟨hg, hg1⟩ => hx ⟨g, hg⟩ hg1⟩
  refine ⟨fun y hy => ?_, fun z hz => hm.2 z fun i => (hf _).2 (hz i)⟩
  obtain ⟨z, hz, hz'⟩ := hm.1 y fun i => (hf _).2 (hy i)
  exact ⟨z, fun i => (hf _).1 (hz i), hz'⟩

end GlobalTheory.Decompl
