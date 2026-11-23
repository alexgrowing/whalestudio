import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingCoreCrystallineDeRhamInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisDeRhamLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodMatrixAtLogZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedModificationAtEStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTeichmullerPowSemistablePeriodsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EcoefQNormLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogUniformizerTiltBdRPlusCocycleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableInvariantBdRPlusBasisApproxStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableExpCocycleCoboundaryModFilStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsOverAcrisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer

theorem sst_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsSst P (qRep ρ) → ∃ (N c₁ c₂ c₃ k₀ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)) (X X' : Matrix (Fin d) (Fin d) (bk.S)) (Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l)) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (Per.Acris l)), F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).val.map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * κ g)) ∧ (∀ g : ↥(GK K), bk.FixFlat g → κ g = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m := by
  intro l _ K bk P AI T C hC d ρ hsst
  have hdr := GlobalTheory.sst_isDR l P AI T K _ (qRep ρ) hsst
  obtain ⟨H, -⟩ := GlobalTheory.T.exists_hodge_basis_deRham_lattice l K P AI T C hC (bk.ev bk.E) bk.span_ev d ρ hdr
  obtain ⟨b, c, hb, hfix, hlog⟩ := GlobalTheory.T.exists_log_teichmuller_pow_semistablePeriods l K bk P AI T C hC trivial
  obtain ⟨U, U', c₁, c₃, k, F, F', Mn, hUU', hFF', hφ, hMn, hgal⟩ := GlobalTheory.T.semistable_periodMatrix_at_log_zero l K bk P AI T C hC d ρ b c hb hsst
  obtain ⟨-, hInvdR⟩ := GlobalTheory.MemLoc.fits_inv l P AI T C hC
  obtain ⟨lam, hlamg, hlamA⟩ := GlobalTheory.T.exists_log_uniformizerTilt_bdRPlus_cocycle l K bk P AI T C hC b c hb hfix hlog
  obtain ⟨Λ₀, hΛ₀g, hΛ₀A⟩ := GlobalTheory.T.semistable_invariant_bdRPlus_basis_approx l K bk P AI T C hC d (fun g => (ρ g).val) U k Mn c hMn hgal lam hlamg hlamA
  obtain ⟨e, m, hm, hdf⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero d) l (Fact.out : l.Prime).ne_one
  have hk₀ : ∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l (e + k * d) k i‖ ≤ 1 := fun i hi => GlobalTheory.SstPer.ecoefQ_norm_le k hm hdf hi
  obtain ⟨N₀, hZ⟩ := GlobalTheory.T.semistable_periods_over_Acris l K bk P AI T C hC d (fun g => (ρ g).val) U U' hUU' c₁ F hφ k (e + k * d) Mn c hk₀ hgal
  have hUUι : U.map C.ι * U'.map C.ι = 1 := by
    rw [← Matrix.map_mul, hUU', Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨N, c₂, X, X', hN, hXX', hX, hX'⟩ := GlobalTheory.T.exists_twisted_modification_at_E l K bk C hInvdR d (fun g => (ρ g).val) H (U.map C.ι) (U'.map C.ι) Λ₀ hUUι hΛ₀g hΛ₀A N₀
  obtain ⟨Z, Z', hZZ', hZφ, hZg, hZX, hZX'⟩ := hZ N hN X X' hX hX'
  refine ⟨N, c₁, c₂, c₃, e + k * d, F, F', X, X', Z, Z', fun g => GlobalTheory.SstPer.kap C bk (e + k * d) k Mn (c g), hFF', hXX', hZZ', hZφ, hZg, ?_, hZX, hZX', GlobalTheory.T.semistable_exp_cocycle_coboundary_mod_fil l K bk P AI T C hC d k (e + k * d) Mn c hk₀ hMn hlog⟩
  intro g hg
  simp only
  rw [hfix g hg]
  exact GlobalTheory.SstPer.kap_zero C bk _ k Mn

end GlobalTheory.SstPer

end
