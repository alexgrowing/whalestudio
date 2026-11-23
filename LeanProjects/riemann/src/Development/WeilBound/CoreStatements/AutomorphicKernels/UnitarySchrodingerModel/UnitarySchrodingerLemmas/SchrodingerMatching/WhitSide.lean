import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.Transport
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.IntegrableWhitOfUnfold
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.TrPairEqHalfTr
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.ConjHConjHInv
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.MonoSch

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem whit_side (hRc : RealConj) (hM : ConjMod) (hU : Unfold) (hK : HeightKInv)
    {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {Φ : schwartzA θ V.rank n} (hstd : Std D n V ψ χ θ μ ω H l s ν Φ) (hrange : InRange V n)
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} {nb : hermA D n → G D n} (hcd : CoefData nb lam 𝓖)
    {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) {β : HermE D n} (hβ : β.1.det ≠ 0) (a : GL (Fin n) (AE D))
    {k : G D n} (hk : k ∈ K D n) {φ : Mx D V.rank n → ℂ} (hsch : φ ∈ schwartzA θ V.rank n) (hfock : φ ∈ fockA θ V n l s)
    (lamS : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (hlamS : ∀ v, (lamS v).IsAddHaarMeasure)
    (L L₁ L₂ : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (hLnu : ∀ lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
        Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E),
      (∀ v, (lam v).IsAddHaarMeasure) →
      ∀ b : hermA D n, ((H (w * nb b) : ℝ))⁻¹ = PositivityTheory.SiegelWeilFormula.Gen.nuA θ (fun _ => 1) lam L L b.1)
    (hnu2 : ∀ v (b : hermA D n),
      PositivityTheory.SiegelWeilFormula.Gen.nu2 (lamS v) (L₁ v) (L₂ v) (PositivityTheory.SiegelWeilFormula.Gen.matV v (conjH a b).1) =
        PositivityTheory.SiegelWeilFormula.Gen.nu2 (lamS v) (L v) (L v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1))
    (𝓕μ : Set (Mx D V.rank n)) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕μ) :
    ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
        (fun X => φ (HMul.hMul (tupOf X) a.1))
        (PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lamS L₁ L₂) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z)
        (lam.map hermTo) ∧
      whitT ψ V μ lam nb w H φ (adj a.1 * β.1.map (incA D) * a.1) k z =
        npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
          ∫ b, PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
            (fun X => φ (HMul.hMul (tupOf X) a.1))
            (PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lamS L₁ L₂)
            (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z b ∂(lam.map hermTo) := by
  classical
  refine ⟨(n : ℝ) / 2, fun z hz => ?_⟩
  set r : ℝ≥0 := absA D (Matrix.GeneralLinearGroup.det a) with hr
  have hr0 : r ≠ 0 := ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (absA D)).ne_zero
  set T : Mx D n n := adj a.1 * β.1.map (incA D) * a.1 with hT

  set I : hermA D n → ℂ := fun c => npow (H (w * nb c * k)) (z - s0 V n) * Jt ψ V μ φ c *
    ψ (-halfTr (Matrix.trace (HMul.hMul T c.1 : Mx D n n))) with hI
  set W := PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
        (fun X => φ (HMul.hMul (tupOf X) a.1))
        (PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lamS L₁ L₂) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z
    with hW
  have hzs : z - s0 V n ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp only [s0, Complex.sub_re, Complex.div_re, Complex.natCast_re, Complex.natCast_im, Complex.zero_re] at hre
    have h2 : (V.rank : ℝ) ≤ 2 * n := by exact_mod_cast hrange.2.1
    norm_num at hre
    linarith
  have hpt : ∀ c : hermA D n, W (hermTo (conjH a c)) = npow r (-(V.rank : ℂ)) * I c := by
    intro c
    have h1 := nu_conj hRc hstd.hθ a lamS L L₁ L₂ hnu2 c
    rw [← hLnu lamS hlamS c] at h1
    have h2 := jt_conj V ψ μ 𝓕μ hμ a φ c
    have h3 := char_conj ψ β a c
    have h4 : H (w * nb c * k) = H (w * nb c) := hK D n H hstd.hH (w * nb c) k hk
    have h5 : ((V.rank : ℂ) - n) / 2 = s0 V n := by unfold s0; ring
    simp only [hW, hI, PositivityTheory.SiegelWeilFormula.Gen.whI]
    change (((PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lamS L₁ L₂ (conjH a c).1 : ℝ)) : ℂ) ^ (-(z - ((V.rank : ℂ) - n) / 2)) *
        PositivityTheory.PfSWUS.Loc.jtR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
          (fun X => φ (HMul.hMul (tupOf X) a.1)) (hermTo (conjH a c)) *
        ψ (-PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))) (hermTo (conjH a c)).1) = _
    rw [h1, h2, h3, h4, h5, inv_cpow_neg' _ hzs]
    ring
  have hHaar : lam.IsAddHaarMeasure := hcd.2.1
  have hIint : Integrable I lam := by
    have h := integrable_whit_of_unfold hU D n V ψ χ θ μ ω H l s ν Φ hstd hrange lam 𝓖 nb hcd w hw β hβ φ hsch hfock
      T z hz
    refine h.congr (Filter.Eventually.of_forall fun c => ?_)
    simp only [hI, hK D n H hstd.hH (w * nb c) k hk]
  have hWcomp : (fun b => W (hermTo b)) = fun b => npow r (-(V.rank : ℂ)) * I (conjH a⁻¹ b) := by
    funext b
    conv_lhs => rw [← conjH_conjH_inv' a b]
    exact hpt _
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0
  have key : npow r ((V.rank : ℂ) - n) * (((r : ℝ) : ℂ) ^ n * npow r (-(V.rank : ℂ))) = 1 := by
    unfold npow
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hrC, ← Complex.cpow_add _ _ hrC]
    have : ((V.rank : ℂ) - n) + ((n : ℂ) + -(V.rank : ℂ)) = 0 := by ring
    rw [this, Complex.cpow_zero]
  have hwI : whitT ψ V μ lam nb w H φ T k z = ∫ c, I c ∂lam := rfl
  refine ⟨?_, ?_⟩
  · refine integrable_map_hermTo lam W ?_
    rw [hWcomp]
    exact (integrable_comp_conjH lam hHaar a⁻¹ hIint).const_mul _
  · rw [integral_map_hermTo lam W]
    have hc := hM D n lam hHaar a (fun B => if h : B ∈ hermA D n then W (hermTo ⟨B, h⟩) else 0)
    have e1 : ∫ b, (fun B => if h : B ∈ hermA D n then W (hermTo ⟨B, h⟩) else 0) b.1 ∂lam = ∫ b, W (hermTo b) ∂lam :=
      integral_congr_ae (Filter.Eventually.of_forall fun b => by
        show (if h : b.1 ∈ hermA D n then W (hermTo ⟨b.1, h⟩) else 0) = W (hermTo b)
        rw [dif_pos b.2])
    have e2 : ∫ c, (fun B => if h : B ∈ hermA D n then W (hermTo ⟨B, h⟩) else 0) (a.1 * c.1 * adj a.1) ∂lam =
        ∫ c, W (hermTo (conjH a c)) ∂lam :=
      integral_congr_ae (Filter.Eventually.of_forall fun c => by
        show (if h : a.1 * c.1 * adj a.1 ∈ hermA D n then W (hermTo ⟨_, h⟩) else 0) = W (hermTo (conjH a c))
        rw [dif_pos (show a.1 * c.1 * adj a.1 ∈ hermA D n from (conjH a c).2)]
        rfl)
    rw [← e1, hc, e2]
    simp only [hpt]
    rw [integral_const_mul, hwI]
    calc ∫ c, I c ∂lam = (npow r ((V.rank : ℂ) - n) * (((r : ℝ) : ℂ) ^ n * npow r (-(V.rank : ℂ)))) * ∫ c, I c ∂lam := by
          rw [key, one_mul]
      _ = _ := by ring

end PositivityTheory.PfSWUS.SwMatch

end
