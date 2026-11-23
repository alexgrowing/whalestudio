import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftLevelActsByInverseCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTowerConstantsDifferByFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.KerDiag
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotTranslate

open GlobalTheory.Grid (neg sgn ofSgn)

variable {D : D7}

theorem compAt_eq_map (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (w : Mx D m n) :
    compAt θ τ w = w.map ((θ τ).comp (infPart D)) := rfl

theorem compAt_mt_of_suppAt {e : AE D} (he : infPart D e = 0) (hce : infPart D (cA D e) = 0) {V : HSp D} {g : GA D V}
    (hg : SuppAt e V g) (θ : InfFam D) (τ : D.what₂.Tau) : compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  ext i j
  have h1 := hg i j
  have e1 : Formalism.L2.Theta.mt V g i j = (e + cA D e) * (Formalism.L2.Theta.mt V g - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by
    rw [h1, Matrix.sub_apply, sub_add_cancel]
  simp only [compAt, Matrix.map_apply]
  rw [e1, (infPart D).map_add, (infPart D).map_mul, (infPart D).map_add, he, hce, add_zero, zero_mul, (θ τ).map_add,
    (θ τ).map_zero, zero_add]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [Matrix.one_apply_ne hij]

theorem compAt_mt_inv {V : HSp D} {g : GA D V} {θ : InfFam D} {τ : D.what₂.Tau} (hg : compAt θ τ (Formalism.L2.Theta.mt V g) = 1) :
    compAt θ τ (Formalism.L2.Theta.mt V g⁻¹) = 1 := by
  have hm : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by
    simp only [Formalism.L2.Theta.mt]
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : compAt θ τ (Formalism.L2.Theta.mt V g⁻¹) * compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
    rw [compAt_eq_map, compAt_eq_map, ← Matrix.map_mul, hm, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hg, Matrix.mul_one] at h2

theorem integrableOn_mul_right_iff {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (k : G) (hk : Measure.map (fun g => g * k) μ = μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    IntegrableOn (fun g => f (g * k)) 𝓕 μ ↔ IntegrableOn f 𝓕 μ := by
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  rw [h𝓕.integrableOn_iff h2 (fun γ g => by simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]; exact hf γ γ.2 _)]
  exact hmp.integrableOn_comp_preimage hemb

end GlobalTheory.BotTranslate

namespace GlobalTheory.BotTranslate

open GlobalTheory.Grid (neg sgn ofSgn)

set_option maxHeartbeats 2000000 in

theorem translate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (g : T → GA D A) (g' : T → GA D A') (h : T → GA D WW) (κ κ' : T → ℂ), (∀ t, κ t ≠ 0) → (∀ t, κ' t ≠ 0) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A (g t) ∧ Formalism.IndefR.Lev.finE A (g t) ∈ Formalism.L2.DIV.St Y.rA.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A' (g' t) ∧ Formalism.IndefR.Lev.finE A' (g' t) ∈ Formalism.L2.DIV.St Y.rA'.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) WW (h t) ∧ Formalism.IndefR.Lev.finE WW (h t) ∈ Formalism.L2.DIV.St Y.rW.β) →
    ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c →
      (GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW (fun t => κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
        (fun t => κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t))).IsConst W.ψ W.θ fun t => κ t / κ' t * c t := by
  intro D T L sc G W i j A A' WW X Y hX hY g g' h κ κ' hκ hκ' hg hg' hh c hc
  obtain ⟨⟨t₀, hc₀⟩, P, P', H⟩ := hc
  have hYi := hY.is
  have hψ := hYi.isVac.1
  have hθ := hYi.isVac.2.inf
  have sA := GlobalTheory.BotFrames.isStd_s_eq hX.std hY.std
  have sA' := GlobalTheory.BotFrames.isStd_s_eq hX.std' hY.std'
  have sW := GlobalTheory.BotFrames.isStd_s_eq hX.stdW hY.stdW
  have bA := GlobalTheory.BotFrames.isStd_B_eq hX.std hY.std
  have bA' := GlobalTheory.BotFrames.isStd_B_eq hX.std' hY.std'
  have bW := GlobalTheory.BotFrames.isStd_B_eq hX.stdW hY.stdW
  have he := fun t => Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_idemSum (hYi.idem t)
  have hce := fun t => Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_cA_idemSum (hYi.idem t)
  have cg : ∀ t τ, compAt W.θ τ (Formalism.L2.Theta.mt A (g t)⁻¹) = 1 := fun t τ =>
    compAt_mt_inv (compAt_mt_of_suppAt (he t) (hce t) (hg t).1 W.θ τ)
  have cg' : ∀ t τ, compAt W.θ τ (Formalism.L2.Theta.mt A' (g' t)⁻¹) = 1 := fun t τ =>
    compAt_mt_inv (compAt_mt_of_suppAt (he t) (hce t) (hg' t).1 W.θ τ)
  have ch : ∀ t τ, compAt W.θ τ (Formalism.L2.Theta.mt WW (h t)⁻¹) = 1 := fun t τ =>
    compAt_mt_inv (compAt_mt_of_suppAt (he t) (hce t) (hh t).1 W.θ τ)
  set Y₁ := GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW (fun t => κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
    (fun t => κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)) with hY₁

  have hK : ∀ t Q h'' g'', Y₁.ker W.ψ W.θ t Q h'' g'' = κ t * Y.ker W.ψ W.θ t Q (h'' * (h t)⁻¹) (g'' * (g t)⁻¹) := by
    intro t Q h'' g''
    have tf := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hYi.fst t) hYi.isVac.2.theta
    have c0 : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm (g t)⁻¹)) = 1 := cg t
    have key := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ ((Y.ω t).toSgn true) (hYi.weil t) hθ
      (fun τ => -Y.rA.s τ) (fun τ => -Y.rA.s τ) Y.rA.B Y.rA.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B
      ((ofSgn true A).symm (g t)⁻¹) (h t)⁻¹ (fun τ => by rw [c0 τ, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [c0 τ, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.one_mul]) (Y.f t) tf Q).2
    have key' : Y.ω t ((g t)⁻¹, (h t)⁻¹)
        (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) Q) =
        pureTensorO W.ψ W.θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t)) Q :=
      key
    show thetaKO (Y.ω t) g'' h'' (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
        (κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t)) Q) =
      κ t * thetaKO (Y.ω t) (g'' * (g t)⁻¹) (h'' * (h t)⁻¹)
        (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) Q)
    rw [sA, sW, bA, bW, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul, ← key']
    unfold thetaKO
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]
  have hK' : ∀ t Q h'' g'', Y₁.ker' W.ψ W.θ t Q h'' g'' = κ' t * Y.ker' W.ψ W.θ t Q (h'' * (h t)⁻¹) (g'' * (g' t)⁻¹) := by
    intro t Q h'' g''
    have tf := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hYi.snd t) hYi.isVac'.2.theta
    have hw : IsWeilDatumO W.ψ A' WW _ _ (Y.ω' t) := hYi.weil' t
    have key := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ A' WW _ _ (Y.ω' t) hw hθ
      Y.rA'.s Y.rA'.s Y.rA'.B Y.rA'.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B
      (g' t)⁻¹ (h t)⁻¹ (fun τ => by rw [cg' t τ, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [cg' t τ, Matrix.one_mul])
      (fun τ => by rw [ch t τ, Matrix.one_mul]) (Y.f' t) tf Q).2
    show thetaKO (Y.ω' t) g'' h'' (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B
        (κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)) Q) =
      κ' t * thetaKO (Y.ω' t) (g'' * (g' t)⁻¹) (h'' * (h t)⁻¹)
        (pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) Q)
    rw [sA', sW, bA', bW, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul, ← key]
    unfold thetaKO
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

  haveI := hYi.meas.1
  haveI := hYi.meas'.1
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D A Y.m hYi.meas.1).1
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D A' Y.m' hYi.meas'.1).1
  have mk : ∀ k : GA D A, Measure.map (fun x => x * k) Y.m = Y.m := fun k => MeasureTheory.map_mul_right_eq_self Y.m k
  have mk' : ∀ k : GA D A', Measure.map (fun x => x * k) Y.m' = Y.m' := fun k => MeasureTheory.map_mul_right_eq_self Y.m' k
  have hI : ∀ t Q h'', Y₁.I W.ψ W.θ t Q h'' = κ t * Y.I W.ψ W.θ t Q (h'' * (h t)⁻¹) := by
    intro t Q h''
    show ∫ x in Y.fd, Y₁.ker W.ψ W.θ t Q h'' x ∂Y.m = κ t * ∫ x in Y.fd, Y.ker W.ψ W.θ t Q (h'' * (h t)⁻¹) x ∂Y.m
    simp_rw [hK]
    rw [integral_const_mul]
    congr 1
    exact GlobalTheory.DownLift.TypeLaw.setIntegral_mul_right_of_fd (GQ A) Y.m Y.fd hYi.meas.2 _ (mk _) _
      (GlobalTheory.SqTower.Normal.ker_left hYi t Q _)
  have hI' : ∀ t Q h'', Y₁.I' W.ψ W.θ t Q h'' = κ' t * Y.I' W.ψ W.θ t Q (h'' * (h t)⁻¹) := by
    intro t Q h''
    show ∫ x in Y.fd', Y₁.ker' W.ψ W.θ t Q h'' x ∂Y.m' = κ' t * ∫ x in Y.fd', Y.ker' W.ψ W.θ t Q (h'' * (h t)⁻¹) x ∂Y.m'
    simp_rw [hK']
    rw [integral_const_mul]
    congr 1
    exact GlobalTheory.DownLift.TypeLaw.setIntegral_mul_right_of_fd (GQ A') Y.m' Y.fd' hYi.meas'.2 _ (mk' _) _
      (GlobalTheory.SqTower.Normal.ker'_left hYi t Q _)
  refine ⟨⟨t₀, mul_ne_zero (div_ne_zero (hκ t₀) (hκ' t₀)) hc₀⟩, P, P', fun t => ⟨fun h'' => ⟨?_, ?_⟩, ?_, fun h'' => ?_⟩⟩
  · show IntegrableOn (Y₁.ker W.ψ W.θ t P h'') Y.fd Y.m
    rw [show Y₁.ker W.ψ W.θ t P h'' = fun x => κ t * Y.ker W.ψ W.θ t P (h'' * (h t)⁻¹) (x * (g t)⁻¹) from funext (hK t P h'')]
    exact ((integrableOn_mul_right_iff (GQ A) Y.m Y.fd hYi.meas.2 _ (mk _) _
      (GlobalTheory.SqTower.Normal.ker_left hYi t P _)).2 ((H t).1 _).1).const_mul _
  · show IntegrableOn (Y₁.ker' W.ψ W.θ t P' h'') Y.fd' Y.m'
    rw [show Y₁.ker' W.ψ W.θ t P' h'' = fun x => κ' t * Y.ker' W.ψ W.θ t P' (h'' * (h t)⁻¹) (x * (g' t)⁻¹) from funext (hK' t P' h'')]
    exact ((integrableOn_mul_right_iff (GQ A') Y.m' Y.fd' hYi.meas'.2 _ (mk' _) _
      (GlobalTheory.SqTower.Normal.ker'_left hYi t P' _)).2 ((H t).1 _).2).const_mul _
  · obtain ⟨h₀, hne⟩ := (H t).2.1
    refine ⟨h₀ * h t, ?_⟩
    rw [hI', mul_inv_cancel_right]
    exact mul_ne_zero (hκ' t) hne
  · rw [hI, hI', (H t).2.2]
    field_simp [hκ' t]

end GlobalTheory.BotTranslate

end
