import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.HypothesesAtTriple
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SiegelTransport
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locpair

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
  PositivityTheory.ThK.PT

namespace FunSieg

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locField {F : Type} [Field F] [NumberField F] (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) :=
  GlobalTheory.LocalData.isLocalField v

local instance charZeroFv {F : Type} [Field F] [NumberField F] (v : Pl F) : CharZero (Fv F v) :=
  charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective

local instance invTwoFv {F : Type} [Field F] [NumberField F] (v : Pl F) : Invertible (2 : Fv F v) :=
  invertibleOfNonzero two_ne_zero

local instance modTopEv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) :
    IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩

theorem siegSt : SiegSt := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW P hW v w hw _ ω ρ hR m Cy hL _ l hl p hp t hpt z hz hzt u hu φ hφ
  obtain ⟨ψv, dv, χXv, χWv, omv, L⟩ := ThKH.Locpair.locPairEx F E σ n d B X W M om χX χW P hW v
  have hσ := P.base.cm
  obtain ⟨r, s, hX⟩ := P.herm
  obtain ⟨r', s', hWs⟩ := P.skew
  obtain ⟨c1, c2⟩ := psi_good P.base.std (P.base.inert v w hw).2.2 L.psi
  have a1 := isHerm_loc (v := v) hX
  have a2 := isSkew_loc (v := v) hWs
  have a3 := isLagr_loc hσ hw hWs hL
  have R := siegel_transport _ _ _ ψv (isField_Ev hw) (isQuad_Ev hσ v) c1 c2 _ _ _ _ _ _ dv _ _ _ a1 a2 a3 L.weil.1
  obtain ⟨hv, ehv⟩ := exW L hp
  have eω : ω (1, p) φ = omv.comp (MonoidHom.inr _ _) hv φ :=
    (actsW L hp ehv hφ _).1 ((hR.acts 1 (one_mem_UAt X v) p hp φ hφ (ω (1, p) φ)).2 rfl)
  by_cases h0 : ∃ φ ∈ SB (Fin n × Fin d → Fv F v), l φ ≠ 0
  · have hdet : IsUnit (t.map (compFin F E v)).det := by
      rw [← hzt]; exact (Units.map (compFin F E v).toMonoidHom z).isUnit
    let tv : GL (Fin m) (Ev E v) := ((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit
    have htv : (tv : Matrix (Fin m) (Fin m) (Ev E v)) = t.map (compFin F E v) := rfl
    have hdt : Matrix.GeneralLinearGroup.det tv = Units.map (compFin F E v).toMonoidHom z :=
      Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, htv]; exact hzt.symm)
    have hpv : ((hv : GL (Fin d) (Ev E v)) : Matrix (Fin d) (Fin d) (Ev E v)) * Cy.map (compFin F E v) =
        Cy.map (compFin F E v) * (tv : Matrix (Fin m) (Fin m) (Ev E v)) := by
      rw [show ((hv : GL (Fin d) (Ev E v)) : Matrix (Fin d) (Fin d) (Ev E v)) = hv.1.1 from rfl, ← ehv, htv,
        ← Matrix.map_mul, ← Matrix.map_mul, hpt]
    have hu' : Units.map (Algebra.norm (Fv F v) : Ev E v →* Fv F v) (Matrix.GeneralLinearGroup.det tv) = u :=
      Units.ext (by rw [hdt, hu]; rfl)
    have key := R l (Set.mem_univ _) (isEv_of L hL.supp hl h0).2 hv tv hpv φ hφ
    rw [eω, key, hu', hdt, L.chX z hz, Fintype.card_fin]
  · push Not at h0
    rw [h0 _ (hR.pres 1 (one_mem_UAt X v) p hp φ hφ), h0 φ hφ, mul_zero]

end FunSieg

theorem siegSt : SiegSt := FunSieg.siegSt

end PositivityTheory.Sph

end
