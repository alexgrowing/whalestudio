import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionUnipotentRadicalInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConstantTermSourceTargetConjAdjointCorrStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.TargetUnipMean

open GlobalTheory.MixModel (rat)
open scoped GlobalTheory.MixModel

variable {D : D7}

theorem exists_split (W : HSp D) {s : ℕ} (I : Matrix (Fin W.rank) (Fin s) D.host.E) (hI : IsIsoFrame W I) :
    ∃ (W' : HSp D) (ι : W'.V →ₗ[D.host.E] W.V), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W' I (frameMat W W' ι) := by
  obtain ⟨e, rfl⟩ := GlobalTheory.BesselCompare.eMat_surj W I
  have he : LinearIndependent D.host.E e :=
    LinearIndependent.of_comp W.frame.equivFun.toLinearMap hI.2.1
  have hiso : ∀ a b, W.hT (e a) (e b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hI.2.2]; rfl
  obtain ⟨W', ι, h1, h2, h3⟩ := GlobalTheory.WittLow.exists_lower Examples₂.star_isIntegral W e he hiso
  refine ⟨W', ι, ⟨hI, ?_, ?_, by omega⟩⟩
  · refine Matrix.ext fun a b => ?_
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
    exact h2 _ _
  · refine Matrix.ext fun a b => ?_
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul, ← W.herm.eq, h3]
    simp

theorem decomp {W W' : HSp D} {s k : ℕ} {I : Matrix (Fin W.rank) (Fin s) D.host.E}
    {B : Matrix (Fin W.rank) (Fin W'.rank) D.host.E} (hsp : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W' I B) (x : Mx D W.rank k)
    (hx : rat (Iᴴ * W.gram) ⬝ x = 0) : ∃ (z : Mx D s k) (w : Mx D W'.rank k), x = rat I ⬝ z + rat B ⬝ w := by
  obtain ⟨d, hde, hdi, -⟩ := GlobalTheory.WittSect.exists_hypDec_mem_NI D W W' s I B hsp
  have h := d.sum_eq_one_rat
  simp only [GlobalTheory.MixModel.HypDec.qX, GlobalTheory.MixModel.HypDec.qY, GlobalTheory.MixModel.HypDec.q0, hde, hdi] at h
  have h1 : rat (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E) ⬝ x = x := by
    rw [GlobalTheory.MixModel.rat_one, Matrix.one_mul]
  rw [← h, GlobalTheory.MixModel.rat_add, GlobalTheory.MixModel.rat_add, Matrix.add_mul, Matrix.add_mul] at h1
  have h2 : rat (d.e' * (Iᴴ * W.gram)) ⬝ x = 0 := by
    rw [GlobalTheory.MixModel.rat_mul, Matrix.mul_assoc, hx, Matrix.mul_zero]
  rw [h2, add_zero] at h1
  rw [GlobalTheory.MixModel.rat_mul I, GlobalTheory.MixModel.rat_mul B, Matrix.mul_assoc (rat I), Matrix.mul_assoc (rat B)] at h1
  exact ⟨_, _, h1.symm⟩

theorem periodic {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {g : WO V W → ℂ} (hg : IsThetaFunO ψ V W g) {s : ℕ}
    (I : Matrix (Fin W.rank) (Fin s) D.host.E) (p : WO V W) (hp : rat (Iᴴ * W.gram) ⬝ p = 0)
    (γ : Matrix (Fin s) (Fin V.rank) D.host.E) : g (rat I ⬝ rat γ + p) = g p := by
  have e1 : rat I ⬝ rat γ = ratW W V (I * γ) := by rw [GlobalTheory.MixModel.ratW_eq, GlobalTheory.MixModel.rat_mul]
  have e2 : GlobalTheory.MixModel.adj p ⬝ rat (W.gram * I) = 0 := by
    have := congrArg GlobalTheory.MixModel.adj hp
    rwa [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_zero, ← GlobalTheory.MixModel.rat_conjTranspose, conjTranspose_mul,
      GlobalTheory.MixModel.gram_conjTranspose, conjTranspose_conjTranspose] at this
  have e3 : GlobalTheory.MixModel.adj p ⬝ (GlobalTheory.MixModel.gA W ⬝ ratW W V (I * γ)) = 0 := by
    have e2' : GlobalTheory.MixModel.adj p ⬝ (rat W.gram ⬝ rat I) = 0 := by rw [← GlobalTheory.MixModel.rat_mul]; exact e2
    rw [GlobalTheory.MixModel.ratW_eq, GlobalTheory.MixModel.gA, GlobalTheory.MixModel.rat_mul I γ, ← Matrix.mul_assoc (rat W.gram) (rat I) (rat γ),
      ← Matrix.mul_assoc, e2', Matrix.zero_mul]
  rw [e1, hg.quasi, GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, e3, Matrix.mul_zero, Matrix.trace_zero,
    map_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.TargetUnipMean

namespace GlobalTheory.TargetUnipMean

open GlobalTheory.MixModel (rat)
open scoped GlobalTheory.MixModel

theorem mean_unip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ n ∈ NI W I, ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, om (1, n) f (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f (HMul.hMul (I.map (incA D)) y + x) ∂ν := by
  intro D ψ V W χV χW om hom s I hI ν 𝓨 hν n hn f hf x hx
  obtain ⟨W', ι, hsp⟩ := exists_split W I hI
  obtain ⟨omt, hmt, hsw⟩ := GlobalTheory.T.exists_conj_weilDatum_exchangedPair D ψ V W χV χW om hom
  obtain ⟨μ', 𝓖', hμ', he⟩ := (GlobalTheory.T.weilConstantTerm_source_target_conjAdjoint_corr D V W W' s ι I).1 ν 𝓨 hν
  have hlaw := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hom.std V W'
  have hlawW := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hom.std V W
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 (om (1, n) f) = GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 f := by
    have h1 := GlobalTheory.UnipRes.res_unip D W W' V s I (frameMat W W' ι) hsp ψ χW χV omt hmt μ' 𝓖' hμ' ⟨n, hn⟩
      (GlobalTheory.PairLift.dag V W f) (hlawW.theta f hf)
    have h2 : GlobalTheory.PairLift.dag V W' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 (om (1, n) f)) =
        GlobalTheory.PairLift.dag V W' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 f) := by
      rw [← he, ← he, ← hsw]
      exact h1
    funext w
    have h3 := congrFun h2 (GlobalTheory.PairLift.adjO W' V w)
    simp only [GlobalTheory.PairLift.dag, hlaw.invol] at h3
    exact (starRingEnd ℂ).injective h3
  have hII : Iᴴ * W.gram * I = 0 := hI.2.2
  have hIB : Iᴴ * W.gram * frameMat W W' ι = 0 := hsp.orth
  obtain ⟨z, w, hz⟩ := decomp hsp x hx
  have hred : ∀ g, IsThetaFunO ψ V W g → ∫ y in 𝓨, g (HMul.hMul (I.map (incA D)) y + x) ∂ν =
      GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 g w := by
    intro g hg
    have hper : ∀ γ ∈ GlobalTheory.MixModel.ratMx D s V.rank, ∀ a : Mx D s V.rank,
        g (rat I ⬝ (γ + a) + rat (frameMat W W' ι) ⬝ w) = g (rat I ⬝ a + rat (frameMat W W' ι) ⬝ w) := by
      intro γ hγ a
      obtain ⟨γ0, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hγ
      rw [Matrix.mul_add, add_assoc]
      refine periodic hg I _ ?_ γ0
      rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, hII,
        hIB, GlobalTheory.MixModel.rat_zero, GlobalTheory.MixModel.rat_zero, Matrix.zero_mul, Matrix.zero_mul, add_zero]
    have := GlobalTheory.MixModel.covolOne_integral_add hν (fun a => g (rat I ⬝ a + rat (frameMat W W' ι) ⬝ w)) hper z
    rw [hz]
    calc ∫ y in 𝓨, g (HMul.hMul (I.map (incA D)) y + (rat I ⬝ z + rat (frameMat W W' ι) ⬝ w)) ∂ν
        = ∫ y in 𝓨, g (rat I ⬝ (y + z) + rat (frameMat W W' ι) ⬝ w) ∂ν := by
          congr 1
          funext y
          show g (rat I ⬝ y + _) = _
          rw [Matrix.mul_add, add_assoc]
      _ = _ := this
  rw [hred (om (1, n) f) (hom.om_pres (1, n) f hf), hred f hf, hr]

end GlobalTheory.TargetUnipMean
