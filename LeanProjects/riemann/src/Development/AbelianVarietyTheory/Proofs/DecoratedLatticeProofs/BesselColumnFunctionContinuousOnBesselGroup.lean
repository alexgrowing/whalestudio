import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierCoefficientBessel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFlagStabilizerAnisotropicBlockExists
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.PhCont

variable {D : D7}

theorem psiBes_mul_embA (ψ : AddChar (AF D.host.F) ℂ) {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (o : OrthDec S₀ A L) (θ : D.host.E) (ζ : Fin L.rank → D.host.E) (n : GA D S) (a : GA D A) :
    psiBes ψ d θ (vecB o ζ) (n * embA d o a) = psiBes ψ d θ (vecB o ζ) n := by
  have hX : blockX d (n * embA d o a) = blockX d n := by
    rw [blockX, blockX, mt_mul, Matrix.mul_assoc, embA_apply, d.wittDecomp_anisotropicEmbedding_inclX]
  have hC : coefX d (vecB o ζ) (n * embA d o a) = coefX d (vecB o ζ) n := by
    rw [coefX, coefX, mt_mul, Matrix.mul_assoc, embA_apply, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mulVec_mulVec, GlobalTheory.CharLaws.emb_vecB]
    simp only [Matrix.mul_assoc]
  rw [psiBes, psiBes, simpleSum, simpleSum, hX, hC]

theorem ph_continuousOn : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK)
    (y : X.B.I.Ginf), IsCharAF D.host.F ψ →
      ContinuousOn (fun g => Ph X u hK T (iotaX X h g * (y, X.xu u))) (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := by
  intro D X h u ψ A B hK T y hψ
  obtain ⟨p, hp, hpv⟩ := GlobalTheory.BesProj.exists_continuous_proj D _ _ A _ _ B.d B.o
  obtain ⟨hcont, hval⟩ := GlobalTheory.Core.Mi.PhCol.ph_colForm D X h u ψ A B hK T
  refine continuousOn_iff_continuous_restrict.2 ?_
  show Continuous fun g : (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) => Ph X u hK T (iotaX X h g.1 * (y, X.xu u))
  have e : (fun g : (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) => Ph X u hK T (iotaX X h g.1 * (y, X.xu u))) =
      fun g => star (psiBes ψ B.d 1 (vecB B.o B.ζ) g.1) * B.colForm T.1 (X.Wu u y) (p g) := by
    funext g
    obtain ⟨g, hg⟩ := g
    obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o _).1 hg
    have hpa : p ⟨n * embA B.d B.o a, hg⟩ = a := hpv a ⟨n, hn⟩
    show Ph X u hK T (iotaX X h (n * embA B.d B.o a) * (y, X.xu u)) = _
    rw [hval n hn a y]
    show _ = star (psiBes ψ B.d 1 (vecB B.o B.ζ) (n * embA B.d B.o a)) * B.colForm T.1 (X.Wu u y) (p ⟨n * embA B.d B.o a, hg⟩)
    rw [psiBes_mul_embA]
    exact congrArg (fun a' => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) * B.colForm T.1 (X.Wu u y) a') hpa.symm
  rw [e]
  have hps : Continuous (psiBes ψ B.d 1 (vecB B.o B.ζ)) :=
    GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1 1 _
  exact (continuous_star.comp (hps.comp continuous_subtype_val)).mul ((hcont (X.Wu u y)).2.comp hp)

end GlobalTheory.Core.Mi.PhCont
