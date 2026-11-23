import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

open scoped TensorProduct Matrix

namespace GlobalTheory.CosetOrth

section Local

open GlobalTheory.AdelicU GlobalTheory.LFun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valued_toCompl_le_one {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)
    {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) : Valued.v (toCompl h y) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 <|
    intLoc_induction (p := fun y => toCompl h y ∈ w.adicCompletionIntegers E)
      (fun _ ha x => mul_mem (complMap_mem h ha) (GlobalTheory.AdeleBaseChange.algebraMap_int_mem x w))
      (by rw [map_zero]; exact zero_mem _) (fun _ _ h h' => by rw [map_add]; exact add_mem h h')
      (fun _ h => by rw [map_neg]; exact neg_mem h) hy

theorem map_evalV_map_sndA (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) =
      Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

end Local

variable {D : D7}

theorem valued_finMat_finStd_le_one (V : HSp D) (hG : V.gram = 1) (k : GA D V)
    (w : HeightOneSpectrum (𝓞 D.host.E))
    (hk : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (w.under (𝓞 D.host.F)) k ∈
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (stdLat V) (w.under (𝓞 D.host.F))) (i j : Fin V.rank) :
    Valued.v (finMat (GlobalTheory.BotClassDict.finStd V hG k) i j w) ≤ 1 := by
  have hL : stdLat V = GlobalTheory.AdelicU.stdLattice D.host.E V.rank := by
    ext x
    exact ⟨fun h i _ => Submodule.mem_one.1 (h i trivial), fun h i _ => Submodule.mem_one.2 (h i trivial)⟩
  rw [hL] at hk
  have h1 := (GlobalTheory.AdelicU.mem_stabLoc_stdLattice_iff.1 hk).1 i j
  have e : finMat (GlobalTheory.BotClassDict.finStd V hG k) i j =
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((finHom V k).1 i j) := by
    rw [← GlobalTheory.BotClassDict.toAfE_finStd V hG, GlobalTheory.BotClassDict.finAdEquiv_toAfE]
    rfl
  rw [e, GlobalTheory.LFun.finAdEquiv_apply rfl]
  refine valued_toCompl_le_one rfl ?_
  have e2 := map_evalV_map_sndA (w.under (𝓞 D.host.F)) ((matHom V k).1 i j)
  exact e2 ▸ h1

end GlobalTheory.CosetOrth

theorem GlobalTheory.CosetOrth.valued_finMat_le_one_of_mem_openOff : ∀ {D : D7} (V : HSp D) (g : GA D V) (y : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (Sf : Finset (FinPl D)), V.gram = 1 →
  GlobalTheory.BotFormula.IsFinPt V g y → g ∈ openOff V (stdLat V) Sf →
  ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sf → ∀ i j,
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
  intro D V g y Sf hG hy hg w hw i j
  have hfy := GlobalTheory.BotClassDict.finStd_of_isFinPt V hG hy
  subst hfy
  have h := hg _ hw
  refine ⟨GlobalTheory.CosetOrth.valued_finMat_finStd_le_one V hG g w h i j, ?_⟩
  rw [← map_inv]
  refine GlobalTheory.CosetOrth.valued_finMat_finStd_le_one V hG g⁻¹ w ?_ i j
  have h' := inv_mem h
  rwa [← map_inv] at h'
