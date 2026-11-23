import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexNormalizationInertNormEqNeg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeIntertwinerCoefficientAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumSourceInertPlaceEqLatticeIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexHomLatticeInertMoveSourceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SplitScalar GlobalTheory.FinWeil GlobalTheory.WeilParts GlobalTheory.FinWeilO GlobalTheory.LatCoef in

theorem GlobalTheory.VacSource.latticeIntertwiner_coefficient_vacua_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1)) (lam : ℕ →* ℂ) (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)), GlobalTheory.FinWeilO.IsLatRep hψ.1 (frameLat S) (frameLat T) w₀ lam Om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : Gv S v) (f₁ f₂ : GlobalTheory.FinWeilO.thetaSub ψ S T), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ → Lift.pet μ 𝓕 (Om (embV S v a, 1) f₁ : WO S T → ℂ) f₂ = (lam (GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (embV S v a, 1)))))⁻¹ * Lift.pet μ 𝓕 (f₁ : WO S T → ℂ) f₂ := by
  intro D ψ S T hψ lam w₀ Om h μ 𝓕 hμ v a f₁ f₂ h₁ h₂
  obtain ⟨η, hηdef⟩ : ∃ η : AF D.host.F, η = pairA D.host.F 0 (singleV D.host.F v 1) := ⟨_, rfl⟩
  have hε : IsPlaceIdem D v η := hηdef ▸
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hg : SuppPl η S (embV S v a) := hηdef ▸ GlobalTheory.PlaceTensor.suppPl_emb S v a
  have hk : SuppPl η T (1 : GA D T) := fun i j => by rw [mt_one, sub_self]; simp
  have hoff := smul_actO (off_smul_mt_place hg) (off_smul_mt_place hk)
  have H := isHeis_opF hψ.1 S T h.hw
  have hphase : ∀ x : XF S T, phase ψ w₀ x * (starRingEnd ℂ) (phase ψ w₀ x) = 1 := fun x => by
    rw [Complex.mul_conj', show ‖phase ψ w₀ x‖ = 1 from hψ.1.2.1 _]; simp
  have laws := fun g : thetaSub ψ S T => GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ g f₂ g.2 f₂.2
  let ℓ : thetaSub ψ S T →ₗ[ℂ] ℂ :=
    { toFun := fun g => GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (g : WO S T → ℂ) f₂
      map_add' := fun g g' => ((laws g).2.2.2.1 g' g'.2).1
      map_smul' := fun c g => ((laws g).2.2.1 c).1 }
  have hℓ : ∀ a' ∈ latF S T (frameLat S) (frameLat T), ∀ g,
      ℓ (opF hψ.1 S T w₀ (mulF S T (algebraMap (AF D.host.F) (AE D) η) a') g) = ℓ g := by
    intro a' ha' g
    obtain ⟨x, hx⟩ : ∃ x, x = mulF S T (algebraMap (AF D.host.F) (AE D) η) a' := ⟨_, rfl⟩
    have hfix := opF_mulF_fix h hε h₂.2 ha'
    rw [← hx] at hfix ⊢
    have hg' := GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 x.fin g.2
    have hf' := GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 x.fin f₂.2
    have l2' := GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ _ _ hg' hf'
    have l3 := GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ _ _ ((thetaSub ψ S T).smul_mem (phase ψ w₀ x) hg') hf'
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (opF hψ.1 S T w₀ x g : WO S T → ℂ) f₂ = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (g : WO S T → ℂ) f₂
    conv_lhs => rw [← hfix]
    rw [coe_opF, coe_opF, (l3.2.2.1 (phase ψ w₀ x)).2, (l2'.2.2.1 (phase ψ w₀ x)).1,
      ((GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ g f₂ g.2 f₂.2).2.2.2.2.2.2.1 x).1, ← mul_assoc, mul_comm (starRingEnd ℂ _),
      hphase, one_mul]
  have hm : ∀ a' ∈ latF S T (frameLat S) (frameLat T),
      opF hψ.1 S T w₀ (mulF S T (algebraMap (AF D.host.F) (AE D) η) a') f₁ = f₁ := fun a' ha' =>
    opF_mulF_fix h hε h₁.2 ha'
  exact coef_of_local_vacuum H lam _ h.sd h.span (rhoF S T (embV S v a, 1)) (h.sd' _) (h.fin _) (Om (embV S v a, 1)) (h.op _)
    (h.vac _) (mulF S T (algebraMap (AF D.host.F) (AE D) η))
    (fun x y => by rw [gamF, gamF, coe_mulF, coe_mulF, symplO_smul, cA_algebraMap])
    (fun a' ha' => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_placeIdem hε) _ ha')
    (fun x => XF.ext (by
      rw [coe_mulF, coe_mulF, smul_smul, ← map_mul, placeIdem_mul_self hε]))
    (fun x => XF.ext (by
      have e1 : ((x - mulF S T (algebraMap (AF D.host.F) (AE D) η) x : XF S T) : WO S T) =
          (1 - algebraMap (AF D.host.F) (AE D) η) • (x : WO S T) := by
        rw [sub_smul, one_smul]; rfl
      rw [coe_rhoF, e1, actO_smul, hoff]))
    (fun x => XF.ext (actO_smul _ _ _ _)) ℓ hℓ f₁ hm

namespace GlobalTheory.VacSource

theorem isSelfDualC_frameLat {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem inv_neg_pow_mul (x : ℂ) (N M : ℕ) :
    ((-x) ^ (N * M))⁻¹ = ((((-1 : ℂˣ) ^ N : ℂˣ) : ℂ) * (x ^ N)⁻¹) ^ (M : ℤ) := by
  rw [zpow_natCast, pow_mul, ← inv_pow, neg_pow, mul_inv, ← inv_pow (-1 : ℂ), inv_neg_one]
  push_cast
  rfl

theorem vacuum_matrixCoefficient_source_inert_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c e → ∃ φ : GU c S.rank → ℂ, KerU ϖ (qV D.host.F v) T.rank ((-1) ^ T.rank) φ ∧ ∀ (g : GU c S.rank) (f₁ f₂ : WO S T → ℂ), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ → Lift.pet μ 𝓕 (om (embV S v (e.symm g), 1) f₁) f₂ = φ g * Lift.pet μ 𝓕 f₁ f₂ := by
  intro D ψ S T χS χT om hom μ 𝓕 hμ v w h hw uS uT c ϖ e hU he
  classical
  obtain ⟨lam, hlam, hsq⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w₀, Om, hL⟩ := GlobalTheory.FinWeilO.exists_isLatRep hom.std (isSelfDualC_frameLat S) (isSelfDualC_frameLat T) hlam
  refine ⟨fun g => (lam (GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T))
    ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (embV S v (e.symm g), 1)))))⁻¹,
    fun d t ht k₁ hk₁ k₂ hk₂ => ?_, fun g f₁ f₂ h₁ h₂ => ?_⟩
  · show (lam _)⁻¹ = _
    rw [GlobalTheory.T.relIndex_homLattice_inert_move_source D S T v w h hw c ϖ e hU he d t ht k₁ hk₁ k₂ hk₂, map_pow, GlobalTheory.LamInert.lam_qV_inert D lam hlam v w hw]
    have hs0 : 0 ≤ ∑ i, max (d i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
    rw [← Int.toNat_of_nonneg hs0, zpow_natCast]
    generalize (∑ i, max (d i) 0).toNat = M
    exact inv_neg_pow_mul _ _ _
  · let g₁ : GlobalTheory.FinWeilO.thetaSub ψ S T := ⟨f₁, h₁.1⟩
    let g₂ : GlobalTheory.FinWeilO.thetaSub ψ S T := ⟨f₂, h₂.1⟩
    have hn := GlobalTheory.T.weilDatum_source_inertPlace_eq_latticeIntertwiner D ψ S T χS χT om hom hom.std lam w₀ Om hL hlam v w h hw uS uT (e.symm g) g₁
    have hc := GlobalTheory.VacSource.latticeIntertwiner_coefficient_vacua_source D ψ S T hom.std lam w₀ Om hL μ 𝓕 hμ v (e.symm g) g₁ g₂ h₁ h₂
    show Lift.pet μ 𝓕 (om (embV S v (e.symm g), 1) (g₁ : WO S T → ℂ)) (g₂ : WO S T → ℂ) = _ * Lift.pet μ 𝓕 (g₁ : WO S T → ℂ) (g₂ : WO S T → ℂ)
    rw [hn, hc]

end GlobalTheory.VacSource

end
