import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrRecOfHasSat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.WeilDeligne
section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
variable {N A}
end
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
end
end UpperTheory.GalS
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp
variable (D : D7) (T : WDTie D.nd D.naut) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
variable {D T ι π s r}
end GlobalTheory.TripleLocal
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
theorem exists_galois_character_crystalline_at_places (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hG : _root_.UpperTheory.GalS.CuspUAlt)
    (ι : Qbar l ≃+* ℂ) (ψ : HChar E) (hu : ∀ v, ψ.UnrAt v) (hr : ∀ τ, ∃ n : ℤ, expo ψ τ = n)
    (hp : ∃ χ, IsPolarized ((CuspSub.triv E (le_refl 1)).twist ψ) χ) :
    ∃ c : G E Ω →* (Qbar l)ˣ, Continuous c ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (B : ValuationSubring Ω) (g : G E Ω),
        IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g → ι (c g : Qbar l) = (((ψ.val w)⁻¹ : ℂˣ) : ℂ)) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
      ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
        (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
        IsCrysAt P Bw ((GeneralLinearGroup.scalar (Fin 1)).comp (c.comp (Dec (F := E) A).subtype)) := by
  obtain ⟨χ, hχ⟩ := hp
  have hreg : (CG.mk ((CuspSub.triv E (le_refl 1)).twist ψ)).IsRegAlg := (CG.isRegAlg_ofChar ψ).2 hr
  obtain ⟨r, wt, HT, H⟩ := hG E Ω l ι 1 le_rfl _ χ hreg hχ
  have hcr : Continuous fun g => (r g : Matrix (Fin 1) (Fin 1) (Qbar l)) := Units.continuous_val.comp H.cont
  have hsc : (GeneralLinearGroup.scalar (Fin 1)).comp (Matrix.GeneralLinearGroup.det.comp r) = r := by
    ext g i j
    rw [MonoidHom.comp_apply, coe_scalar, Subsingleton.elim i 0, Subsingleton.elim j 0]
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    change Matrix.det (r g : Matrix (Fin 1) (Fin 1) (Qbar l)) = _
    rw [Matrix.det_fin_one]
  have hdet : Continuous fun x : GL (Fin 1) (Qbar l) => Matrix.GeneralLinearGroup.det x := GeneralLinearGroup.continuous_det
  refine ⟨MonoidHom.comp Matrix.GeneralLinearGroup.det r, hdet.comp H.cont, fun w hl B g hB hg => ?_, fun P AI hT w A h O _ _ _ Bw hj => ?_⟩
  · obtain ⟨y1, y2⟩ := _root_.GlobalTheory.HodgeOfTrue.locPar_ofChar_unr_and_frobEig hL ψ hB (hu w)
    have e1 : wdOf hB hl ι r = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar ψ) hB := by
      rw [H.eq_locPar hL hF hl hB y1, show (1 - ((1 : ℕ) : ℝ)) / 2 = 0 by norm_num, WD.lpTw_zero]
      rfl
    have f := frobEig_wdOf hl ι hcr (e1 ▸ y1) hB hg
    rw [e1, y2] at f
    have h1 : (r g : Matrix (Fin 1) (Fin 1) (Qbar l)).charpoly = X - C ((r g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0) := by
      simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]
    rw [h1] at f
    have f2 := congrArg (fun p => p.coeff 0) f
    simp at f2
    change ι (Matrix.det _) = _
    rw [Matrix.det_fin_one]
    exact f2.trans (Units.val_inv_eq_inv_val _).symm
  · obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E 1 ((CuspSub.triv E (le_refl 1)).twist ψ) w
    have hc := (H.above P AI hT w A h O Bw hj).crys σ hσ ((_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) (ParLaws.toRep σ)).1 (by
      rw [← _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h]
      exact (_root_.GlobalTheory.HodgeOfTrue.locPar_ofChar_unr_and_frobEig hL ψ h (hu w)).1))
    have e : (GeneralLinearGroup.scalar (Fin 1)).comp ((Matrix.GeneralLinearGroup.det.comp r).comp (Dec (F := E) A).subtype) =
        r.comp (Dec (F := E) A).subtype := by
      rw [← MonoidHom.comp_assoc, hsc]
    rw [e]
    exact hc
end G
end GlobalTheory.HodgeOfTrue
namespace GlobalTheory.GalAway
end GlobalTheory.GalAway
end
end
