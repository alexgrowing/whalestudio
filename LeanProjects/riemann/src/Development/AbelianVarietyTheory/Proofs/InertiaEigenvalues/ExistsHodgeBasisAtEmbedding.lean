import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSTmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtFixing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorDeRhamCoordMulGaloisActionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiKernelKillingElementStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardEqOfLinIndepSpanningDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeBasisOfAdaptedInvariantFamilyStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.HodgeAt

set_option maxHeartbeats 1000000 in

theorem exists_hodge_at_embedding : ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → Formalism.MainNotions.N.IsDR (P.PD K) R → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (σ : GQ l), (∀ x : ↥K.1, σ ((τ x : ↥L.1) : Om l) = (x : Om l)) → ∃ (K' : FinExt l) (H : Hodge C ξ (fun g => (r g).val.map fun x => σ (x : Om l)) K'), K.1 ≤ K'.1 ∧ ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = multV (P.PD K) R τ n := by
  intro l _ K L P AI T C hC ξ hξ a r R hR hDR τ σ hσ
  haveI := K.2
  haveI := L.2
  haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K L (Fin a → ↥L.1) R).1
  obtain ⟨m, d, k, hA⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (GlobalTheory.DRFil.isField_dR T) R
    (GlobalTheory.DRFil.filSpans T K L R hDR) τ
  obtain ⟨K', hKK', hK'⟩ := exists_ext_fixing l K L σ
  obtain ⟨e, he1, he0⟩ := GlobalTheory.T.exists_bdR_element_normalized_killing_phi_kernel l P σ L a
  have hid := phiS_idem l P K L τ σ hσ
  set w : Fin m → Fin a → P.R.BdR := fun i => PhiS P σ L a (d i) with hw
  have hfil : ∀ i j, w i j ∈ (P.PD K).Fil (k i) := fun i j =>
    phiS_mem_Fil l P AI T K L σ (k i) _ (GlobalTheory.DRFil.ext_mem_FilV (P.PD K) _ (hA.mem i).2)
  have hind : ∀ β : Fin m → P.R.BdR, ∑ i, β i • w i = 0 → β = 0 := by
    intro β hβ
    have h0 : ∑ i, GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) (e * ((1 : ↥L.1) ⊗ₜ β i)) (d i) = 0 := by
      simp only [GlobalTheory.DRFil.sm_mul, GlobalTheory.DRFil.sm_one_tmul, ← map_sum]
      apply he0
      rw [PhiS_sum]
      simp only [PhiS_mulR]
      rw [← hβ]
      funext j
      simp [hw]
    funext i
    have := congrArg (phiS P σ L) (hA.indep _ h0 i)
    simpa [map_mul, hid, he1, phiS_tmul] using this
  have hspan : ∀ j, ∃ u : Fin m → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1 := by
    intro j
    obtain ⟨rr, hrr, hy⟩ := hA.span 0 (Pi.single j 1 ⊗ₜ (1 : P.R.BdR))
      (GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) _ (P.PD K).one_mem)
    refine ⟨fun i => phiS P σ L (rr i), fun i => by simpa using phiS_mem_Fil l P AI T K L σ _ _ (hrr i), ?_⟩
    have h2 := congrArg (PhiS P σ L a) hy
    rw [PhiS_sm] at h2
    simp only [hid, one_mul, PhiS_sum, PhiS_sm] at h2
    have h3 : ∑ i, (fun i => phiS P σ L (rr i)) i • w i = ∑ x, fun i => phiS P σ L (rr x) * PhiS P σ L a (d x) i := rfl
    rw [h3, ← h2, PhiS_tmul]
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_eq_of_ne hij]
  have hinv : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i,
      ((fun g => (r g).val.map fun x => σ (x : Om l)) g).map (algebraMap (Om l) P.R.BdR) *ᵥ
        (fun j => P.actQdR (g : GQ l) (w i j)) = w i := by
    intro g hg i
    have h1 := GlobalTheory.T.tensorDeRhamCoordMul_galois_action l P K L σ a r R hR g (fun y => hK' g hg y) (d i)
    rw [(GlobalTheory.DRFil.mem_DdR (P.PD K) R _).1 (hA.mem i).1.1 g] at h1
    rw [Matrix.map_map]
    exact h1.symm
  have hma := GlobalTheory.T.card_eq_of_linIndep_spanning_deRham l P AI T a m w hind (fun j => (hspan j).imp fun u hu => hu.2)
  subst hma
  obtain ⟨H, hH⟩ := GlobalTheory.T.hodge_basis_of_adapted_invariant_family l P AI T C hC ξ hξ K K' m _ w k hfil hspan hinv
  exact ⟨K', H, hKK', fun n => by rw [hH n, hA.multV_eq]⟩

end GlobalTheory.HodgeAt
