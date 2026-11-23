import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantUnitMatrixBcrisFrame
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.fixW_holds :
    FixW := by
  intro l _ K bk P AI T n hn s
  set x := f0 bk s with hx
  have hact := ActLaws.act_laws l
  have hσB : ∀ (g : GQ l) (y : Per.Acris l), Per.σB g (iB l y) = iB l (sigA g y) :=
    hact.2.2.2.2.2.2.2.2.2.2.2.1
  have hφB : ∀ y : Per.Acris l, Per.φB l (iB l y) = iB l (phiA l y) :=
    hact.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, hσι⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  have hfix : ∀ g : ↥(GK K), sigA (g : GQ l) x = x := by
    intro g
    have hxe : x = iA l (WittVector.frobenius (bk.ev (PowerSeries.C (PowerSeries.constantCoeff s)))) := by
      simp only [hx, f0, fA, RingHom.comp_apply, bk.ev_frob]
    rw [hxe, hσι, ← GlobalTheory.RingBasics.φA_apply, ← ActLaws.φA_σA, bk.ev_C, bk.gal_w g]
  have hinj : Function.Injective (iB l) := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l
  set b := T.eB.symm (iB l x) with hb
  have hbfix : ∀ g : ↥(GK K), (P.PD K).actB g b = b := by
    intro g
    apply T.eB.injective
    rw [P.PD_actB, T.actB, hb, RingEquiv.apply_symm_apply, hσB, hfix]
  obtain ⟨c, hc⟩ := (P.PD K).invB b hbfix
  have hc' : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, c.2.2⟩ = b := hc
  have hit : ∀ (m : ℕ) (y : ↥(MaximalUnramifiedExtension l)), (fun z => P.φB z)^[m] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B y) =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((frobUr l ^ m) y) := by
    intro m y
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, phiB_algebraMap, pow_succ', AlgHom.mul_apply]
  have hbn : (fun z => P.φB z)^[n] b = b := by
    rw [← hc', hit, hn ⟨c, c.2.2⟩ c.2.1]
  have htr : ∀ (m : ℕ) (y : P.R.B), T.eB ((fun z => P.φB z)^[m] y) = (Per.φB l)^[m] (T.eB y) := by
    intro m y
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T.frob, ih]
  have hin : ∀ (m : ℕ) (y : Per.Acris l), (Per.φB l)^[m] (iB l y) = iB l ((phiA l)^[m] y) := by
    intro m y
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hφB]
  apply hinj
  have h1 := htr n b
  rw [hbn, hb, RingEquiv.apply_symm_apply, hin] at h1
  rw [RingHom.coe_pow]
  exact h1.symm
