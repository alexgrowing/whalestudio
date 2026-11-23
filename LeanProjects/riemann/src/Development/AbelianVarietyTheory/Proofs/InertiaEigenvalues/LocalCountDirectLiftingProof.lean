import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenModSpanSUnionLeOfDirectedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenModMonoLeftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMergedModulePushoutsContainBothStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorLocalFieldIsCrystallineOverFamilyFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRankBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateDualLocalGaloisRepAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftAllOfBlochKatoLiftingFamilyAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PushoutsMemSpanLocalSelmerPushoutsStatement

noncomputable section

namespace GlobalTheory.Pass.LocDirect

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem main : StepLocDirect := by
  intro D hLOC hBK hFont hPDR i r hr Xs w hw hdeg n e hPot hLift k M hSub
  have hM : Continuous fun g => M g := hSub.1
  have hc : ∀ x, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r x) g := fun x =>
    GlobalTheory.PotDual.continuous_loc D i w hw _ (FamCont.stepCont D i r hr x).1
  unfold LocBoundP
  have hcut : cutCoc i w hw r Xs M = ⋃₀ {A | ∃ (a : ℕ) (x : Fin a → D.nd.X i) (_ : ∀ j, x j ∈ Xs)
      (E : Fin a → Fin D.R.nV → KK D.nd i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (_ : Y.FG)
      (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
      (hE : ∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y),
      A = LocDirect.pushSet i w hw r M x E Y hst hE} := by
    ext c
    rw [LocDirect.mem_cutCoc, Set.mem_sUnion]
    constructor
    · rintro ⟨a, x, hx, E, Y, hY, hst, hE, hc⟩
      exact ⟨_, ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩, hc⟩
    · rintro ⟨_, ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩, hc⟩
      exact ⟨a, x, hx, E, Y, hY, hst, hE, hc⟩
  rw [hcut]
  apply GlobalTheory.T.lenMod_span_sUnion_le_of_directed'
  · rintro _ ⟨a₁, x₁, hx₁, E₁, Y₁, hY₁, hst₁, hE₁, rfl⟩ _ ⟨a₂, x₂, hx₂, E₂, Y₂, hY₂, hst₂, hE₂, rfl⟩
    obtain ⟨a, x, hx, E, Y, hY, hst, hE, h1, h2⟩ :=
      GlobalTheory.T.exists_merged_module_pushouts_contain_both D i w hw r Xs M a₁ x₁ hx₁ E₁ Y₁ hY₁ hst₁ hE₁ a₂ x₂ hx₂ E₂ Y₂ hY₂ hst₂ hE₂
    exact ⟨_, ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩, h1, h2⟩
  · rintro _ ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩
    let U := LocDirect.ModuleGaloisRepresentation i w hw M hM
    let X := LocDirect.Xgrep i w hw r x (fun j => hc (x j)) Y hst
    obtain ⟨K', hK', hcrys⟩ := GlobalTheory.T.tensorLocalField_isCrystalline_over_familyField D hFont i r hr Xs w hw n hPot M hSub hM
    have hUdR : IsDR (Br.PD D.loc D.nbr i w hw) U.ρ :=
      hPDR (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL hK' U hcrys
    obtain ⟨U', LT', PU, hdual, hrank⟩ := GlobalTheory.T.crystalline_over_extension D hFont hBK hPDR i w hw hdeg M hM K' hK' hcrys
    obtain ⟨X', PX, hX⟩ := GlobalTheory.T.exists_tateDual_localGaloisRep_atPlace D i w hw X
    have hLA := GlobalTheory.T.liftAll_of_blochKatoLiftingFamilyAtPlace D i w hw r hr Xs e hLift M hSub hM a x hx (fun j => hc (x j)) Y hst
    have hsub := GlobalTheory.T.pushouts_mem_span_localSelmerPushouts D hFont i r hr Xs w hw n hPot M hM a x hx (fun j => hc (x j)) E Y hY hst hE
    obtain ⟨m, k', hm, hk', hle⟩ := hLOC.2 (D.nd.l i) (D.nbr i w hw).Kw (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)
      (goodO_ringOfIntegers _ _) X X U X' U' 1 PX PU (Br.locLat D.nbr i w hw M) LT' e
      ⟨⟨LinearEquiv.refl _ _, fun g v => by simp⟩, hUdR, hX, hdual, Or.inl hLA⟩
    have hmono := GlobalTheory.T.lenMod_mono_left' _ _ (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M))
      (Submodule.span_le.2 hsub)
    have hT : finrank (Br.OLL D.nbr i w hw) ↥(Br.locLat D.nbr i w hw M).T = k := by
      have hinj := stdG_inj (O := Br.OLL D.nbr i w hw) (LL := Br.LL D.nbr i w hw) Subtype.val_injective k
      show finrank _ ↥(stdG (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) k) = k
      exact (LinearEquiv.ofInjective _ hinj).finrank_eq.symm.trans (Module.finrank_fin_fun _)
    have h2 : m ≤ 2 * k * e * k' := by
      refine hle.trans ?_
      calc _ ≤ e * (k + k) * k' := by
            gcongr
            · exact hrank
            · exact hT.le
        _ = 2 * k * e * k' := by ring
    calc _ ≤ BlochKatoDuality.lenMod (BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X U (Br.locLat D.nbr i w hw M))
          (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) := hmono
      _ = (m : ℕ∞) := hm
      _ ≤ ((2 * k * e * k' : ℕ) : ℕ∞) := by exact_mod_cast h2
      _ = _ := by
        rw [show lenOl (Br.PD D.loc D.nbr i w hw) (O := Br.OLL D.nbr i w hw) = (k' : ℕ∞) from hk']
        push_cast; ring

end GlobalTheory.Pass.LocDirect
