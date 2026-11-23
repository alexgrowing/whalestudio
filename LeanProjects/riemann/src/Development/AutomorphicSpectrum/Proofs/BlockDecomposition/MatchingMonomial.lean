import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPull
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugation
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.RationalHermitianCountable.CountableRatHerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPlacesOfHasRealPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PosDefFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatAtIsCO
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyMapLatLocEqLatO
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyMulClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarLatticeUnipotentIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAddHaarTens
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.CompanionTheory.SwUnf GlobalTheory.CompanionTheory.HermPoisson GlobalTheory.CompanionTheory.SiegelUnip
variable {D : D7} {n : ℕ}

theorem integral_pull (D : D7) (n : ℕ) (lam : Measure (hermA D n)) (hl : lam.IsAddHaarMeasure)
    (a : GL (Fin n) (AE D)) (F : hermA D n → ℂ) :
    ∫ b, F b ∂lam = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ b, F (pull a b) ∂lam := by
  have key := GlobalTheory.CompanionTheory.CgMod.integral_cg D n lam hl a (fun c => F (pull a c))
  have e : ∀ c : hermA D n, pull a (cg a c) = c := fun c => Subtype.ext (by
    show (a⁻¹).1 * (a.1 * c.1 * adj a.1) * adj (a⁻¹).1 = c.1
    have h1 : (a⁻¹).1 * a.1 = 1 := by simp
    calc (a⁻¹).1 * (a.1 * c.1 * adj a.1) * adj (a⁻¹).1
        = ((a⁻¹).1 * a.1) * c.1 * (adj a.1 * adj (a⁻¹).1) := by simp only [Matrix.mul_assoc]
      _ = c.1 := by rw [h1, adj_mul_adj_inv, Matrix.one_mul, Matrix.mul_one])
  simp only [e] at key
  exact key

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem matchMono : PositivityTheory.PfSWUS.MatchMono := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hCD w hw β hβ a k hk φ hφ
  obtain ⟨hpl, hne⟩ := GlobalTheory.CompanionTheory.MM.isPlaces_of_hasRealPar D ψ θ l hS.hψ hS.hθ hS.hl
  obtain ⟨ε, fr, hfr, hfr1⟩ := GlobalTheory.CompanionTheory.CartFrames.exists_frames D V θ s hS.hθ hS.hs
  obtain ⟨hfock, hsch⟩ := mono_mem D n V θ l s φ hS.hθ hpl.ne hS.hs hφ
  obtain ⟨lamG, hlamG⟩ := GlobalTheory.CompanionTheory.LocHaar.exists_addHaar_tens D n
  obtain ⟨𝓕, hμ⟩ := hS.hμ
  obtain ⟨e, c, g, d, bs, gv, hpure, hφe⟩ := hφ
  obtain ⟨P, hP⟩ := GlobalTheory.CompanionTheory.PfSWUS.MonoSplit.main D n V l s fr e c hne hfr1
  have hcm := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  have hT : ∀ x y, D.sp.cm.sig (β.1 y x) = β.1 x y := fun x y => by
    have := congrFun (congrFun β.2 x) y
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  obtain ⟨hnb, hlam⟩ := hCD
  haveI : lam.IsAddHaarMeasure := hlam.1
  refine ⟨d, bs, θ, l, ε, fr, gAt θ a, P, lamG, latAt a.1, latAt (adj (a⁻¹).1),
    fun X => φ (HMul.hMul (tupOf X) a.1), fun Y => g fun i j => ∑ k, Y k i * finPart D (a.1 k j),
    fun v Y => gv v (fun j i => ∑ k, Y k i * PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 k j),
    μ.map tupInv, lam.map hermTo, ψ, ?_, npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n), ⟨(n : ℝ) / 2, ?_⟩, ?_⟩
  · refine
      { cm := hcm, herm := hJ, lt := hR.1, hT := hT, det := hβ, chr := hS.hψ, places := hpl, frames := hfr, haar := hlamG,
        co := fun v => ⟨GlobalTheory.CompanionTheory.MM.latAt_isCO D n a v, ?_⟩, std := ?_, pure := GlobalTheory.CompanionTheory.PureTwist.isPureFin_twist D n V.rank d bs g gv a hpure, prod := ?_,
        sdW := sdW_map V hS.hψ hμ, sdH := sdHerm_map hS.hψ hlam }
    · exact GlobalTheory.CompanionTheory.MM.latAt_isCO D n (astar a) v
    · filter_upwards [GlobalTheory.CompanionTheory.MM.LatStd.latAt_eq_latO D n a d bs, GlobalTheory.CompanionTheory.MM.LatStd.latAt_eq_latO D n (astar a) d bs] with v h1 h2
      exact ⟨h1, h2⟩
    · intro X
      have hcomp : ∀ τ, compAt θ τ (HMul.hMul (tupOf X) a.1 : Mx D V.rank n) =
          Matrix.of (fun i j => θ τ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X j i)) * (gAt θ a τ).1 := by
        intro τ
        ext i j
        simp only [compAt, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
        rfl
      have hfin : (fun i j => finPart D ((HMul.hMul (tupOf X) a.1 : Mx D V.rank n) i j)) =
          fun i j => ∑ k, HeckeCharacterZeroLocus.SiegelWeilU.projFin X k i * finPart D (a.1 k j) := by
        funext i j
        simp only [Matrix.mul_apply, map_sum, map_mul]
        rfl
      show φ (HMul.hMul (tupOf X) a.1) = PositivityTheory.SiegelWeilFormula.Gen.phiInf θ l fr (gAt θ a) P (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) *
        (g fun i j => ∑ k, HeckeCharacterZeroLocus.SiegelWeilU.projFin X k i * finPart D (a.1 k j))
      rw [hφe]
      simp only []
      rw [hP, hfin]
      congr 1
      unfold PositivityTheory.SiegelWeilFormula.Gen.phiInf PositivityTheory.SiegelWeilFormula.Gen.crd
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hcomp τ, Matrix.mul_assoc]
  · intro z hz
    obtain ⟨i1, -, i3, -, -, -⟩ := lattice_Mx D n n
    haveI : IsTopologicalAddGroup (Mx D n n) := i1
    haveI : SecondCountableTopology (Mx D n n) := i3
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
    haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
    haveI : IsTopologicalAddGroup (Matrix (Fin n) (Fin n) (AE D)) := i1
    haveI : BorelSpace (HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    set r := absA D (Matrix.GeneralLinearGroup.det a) with hr
    have hr0 : r ≠ 0 := ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (absA D)).ne_zero
    have hS' : Std D n V ψ χ θ μ ω H l s ν (⟨φ, hsch⟩ : schwartzA θ V.rank n) := { hS with hΦ := hfock }
    have hF0 : Integrable (fun b : hermA D n => sect ω H (⟨φ, hsch⟩ : schwartzA θ V.rank n) z (w * nb b * 1)) lam :=
      (PositivityTheory.PfSWUS.HUnfold.unfold D n V ψ χ θ μ ω H l s ν _ hS' hR nb lam 𝓖 ⟨hnb, hlam⟩ w hw β hβ z hz 1).1
    have hF : Integrable (fun b : hermA D n => npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ φ b) lam :=
      hF0.congr (Filter.Eventually.of_forall fun b => sect_w D n V ψ χ θ μ ω H hS.hω nb hnb w hw ⟨φ, hsch⟩ z b)
    have hFp := integrable_pull D n lam hlam.1 a _ hF
    have hch : Continuous fun b : hermA D n =>
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) := by
      have h := continuous_chi hS.hψ (-(β.1.map (incA D)))
      exact h.congr fun b => chi_neg_left ψ _ b
    have hcn : ∀ b : hermA D n, ‖ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))‖ = 1 :=
      fun b => hS.hψ.2.1 _
    have hrm : npow r (V.rank : ℂ) ≠ 0 := by
      unfold npow
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => hr0 (by exact_mod_cast h.1)

    have hR1 : Integrable (fun b : hermA D n => npow (H (w * nb (pull a b))) (z - s0 V n) *
        Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) lam := by
      have h1 : Integrable (fun b : hermA D n => (npow r (V.rank : ℂ))⁻¹ *
          (npow (H (w * nb (pull a b))) (z - s0 V n) * Jt ψ V μ φ (pull a b))) lam := hFp.const_mul _
      have h2 : Integrable (fun b : hermA D n => npow (H (w * nb (pull a b))) (z - s0 V n) *
          Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b) lam := by
        refine h1.congr (Filter.Eventually.of_forall fun b => ?_)
        show (npow r (V.rank : ℂ))⁻¹ * (npow (H (w * nb (pull a b))) (z - s0 V n) * Jt ψ V μ φ (pull a b)) = _
        rw [jt_pull D n V ψ μ 𝓕 hμ φ a b, ← hr, mul_left_comm (npow (H (w * nb (pull a b))) (z - s0 V n)),
          inv_mul_cancel_left₀ hrm]
      refine h2.mono (h2.aestronglyMeasurable.mul hch.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun b => ?_)
      rw [norm_mul, hcn, mul_one]
    have hwhI : ∀ b : hermA D n,
        PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
          (fun X => φ (HMul.hMul (tupOf X) a.1))
          (PositivityTheory.SiegelWeilFormula.Gen.nuA θ (gAt θ a) lamG (latAt a.1) (latAt (adj (a⁻¹).1)))
          (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z (hermTo b) =
        npow (H (w * nb (pull a b))) (z - s0 V n) *
          Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b *
          ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) := by
      intro b
      unfold PositivityTheory.SiegelWeilFormula.Gen.whI
      have e1 := GlobalTheory.T.local_haar_lattice_unipotent_integral D n θ hS.hθ H hS.hH nb hnb w hw a lamG hlamG b
      have e2 := jtR_hermTo V ψ μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b
      have e3 : (z - ((V.rank : ℂ) - n) / 2) = z - s0 V n := by
        unfold s0
        ring
      show ((PositivityTheory.SiegelWeilFormula.Gen.nuA θ (gAt θ a) lamG (latAt a.1) (latAt (adj (a⁻¹).1)) b.1 : ℝ) : ℂ) ^
          (-(z - ((V.rank : ℂ) - n) / 2)) * _ * _ = _
      rw [e1, e3, npow_inv, e2]
      rfl
    let Mh : hermA D n ≃ₜ HermR (AF D.host.F) D.sp.cm.sig n :=
      { toEquiv := ⟨hermTo, hermFrom, hermFrom_hermTo, hermTo_hermFrom⟩
        continuous_toFun := continuous_hermTo
        continuous_invFun := continuous_hermFrom }
    have hemb : MeasurableEmbedding (hermTo (D := D) (r := n)) := Mh.measurableEmbedding
    constructor
    · exact hemb.integrable_map_iff.2 (hR1.congr (Filter.Eventually.of_forall fun b => (hwhI b).symm))
    · refine Eq.trans ?_ (congrArg (fun t => npow r ((V.rank : ℂ) - n) * t)
        (integral_map_of (hermTo (D := D) (r := n)) hermFrom hermFrom_hermTo hermTo_hermFrom hermTo_add continuous_hermTo
        continuous_hermFrom lam _)).symm
      beta_reduce
      rw [integral_congr_ae (Filter.Eventually.of_forall fun b => hwhI b)]
      show ∫ b, npow (H (w * nb b * k)) (z - s0 V n) * Jt ψ V μ φ b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (adj a.1 * β.1.map (incA D) * a.1) b.1 : Mx D n n))) ∂lam = _
      rw [integral_pull D n lam hlam.1 a]
      have hcong : ∀ b : hermA D n, npow (H (w * nb (pull a b) * k)) (z - s0 V n) * Jt ψ V μ φ (pull a b) *
          ψ (-halfTr (Matrix.trace (HMul.hMul (adj a.1 * β.1.map (incA D) * a.1) (pull a b).1 : Mx D n n))) =
          npow r (V.rank : ℂ) * (npow (H (w * nb (pull a b))) (z - s0 V n) *
            Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b *
            ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) := by
        intro b
        rw [GlobalTheory.CompanionTheory.PfSWUS.height_mul_K hS.hH _ hk, jt_pull D n V ψ μ 𝓕 hμ φ a b, trace_pull, ← hr]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hcong), integral_const_mul, ← mul_assoc]
      congr 1
      rw [sub_eq_add_neg, npow_add_of r hr0, mul_comm]
  · intro μH 𝓕H hμH hF
    exact congrArg (fun t => npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) * t)
      (ifrB_eq_meanC D n V ν hS.hν _ μH 𝓕H hμH hF β hβ)
end GlobalTheory.CompanionTheory.MM
