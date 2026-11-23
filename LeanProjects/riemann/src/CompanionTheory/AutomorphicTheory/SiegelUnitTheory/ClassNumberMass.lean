import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.PacketStatementOfIndependence
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicQuotientVolumeEqOfSignatureRankIndep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeRatio
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryVolumeEqRankMassAllSignatures

namespace CompanionTheory.HU

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SiegelOneAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J → SW1b2 F E σ M J

theorem hU_of (h : SiegelOneAll) (D : D7) : RT.MassRatioUnderVolume D := GlobalTheory.VolRatioFromSecondClause.volumeRatio h D

theorem volSigIndep_of_hU (h : ∀ D, RT.MassRatioUnderVolume D) (D : D7) : VolSigIndep D := by
  refine GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep (fun D hT W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr => ?_) D
  have h2 := volumeMass_of_unfolding D (h D hT)
  have e1 := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
  have e2 := Formalism.BasicNotions.sig_sum W₀ hW₀ D.host.φ₀
  rw [hs] at e1
  rw [hs₀] at e2
  rw [GlobalTheory.Glob.vol_eq_massI_all_sig D hT h2 W P Q hW hs, GlobalTheory.Glob.vol_eq_massI_all_sig D hT h2 W₀ P₀ Q₀ hW₀ hs₀]
  congr 1
  simp only at e1 e2
  omega

theorem volSigIndep_of (h : SiegelOneAll) (D : D7) : VolSigIndep D := volSigIndep_of_hU (hU_of h) D

end CompanionTheory.HU
