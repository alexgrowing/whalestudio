import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsChoiceAndIsChoiceOfCard
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

open Formalism.MainNotions.BridgeLemma IsDedekindDomain

namespace GlobalTheory.RowLev.FixedChoice

theorem isChoice_wB_plGw : ∀ (D : D7) (X : HidaSetting D), GlobalTheory.RowLev.IsChoice X.B.I D.host.g D.nd.PlG (fun k v => Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw k v)) := by
  intro D X
  let e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE
  have he : ∀ a : 𝓞 X.B.I.E, ((e a : 𝓞 D.host.E) : D.host.E) = X.ιE (a : X.B.I.E) := fun a => rfl
  have hnat : ∀ m : ℕ, e (m : 𝓞 X.B.I.E) = (m : 𝓞 D.host.E) := fun m => map_natCast e m
  have hmemB : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (a : 𝓞 X.B.I.E),
      a ∈ (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal ↔ e a ∈ w.asIdeal := fun w a => Iff.rfl

  have hspl : ∀ k, SplitsCompl D.host.E (D.host.g k) := by
    intro k
    have hp := D.host.g_prime k
    have := span_isMaximal hp
    apply splitsCompl_of_ncard _ _ hp
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k
  have hsp : ∀ k (P : Ideal (𝓞 X.B.I.E)), P.IsMaximal → ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P →
      Ideal.absNorm P = D.host.g k ∧ ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∉ P ^ 2 := by
    intro k P hP hg
    have hQ : (P.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hgQ : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.map e := by
      rw [← hnat]; exact Ideal.mem_map_of_mem _ hg
    obtain ⟨h1, h2⟩ := hspl k _ hQ hgQ
    refine ⟨?_, fun h => h2 ?_⟩
    · rw [← h1, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
      exact Nat.card_congr (Ideal.quotientEquiv P (P.map e) e rfl).toEquiv
    · rw [← hnat, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ h
  have hf : X.B.I.f = D.R.f := Formalism.L2.SG.Pf.RowDictPf.f_eq X
  refine (GlobalTheory.SplitChoice.exists_isChoice_and_isChoice_of_card X.B.I D.host.g D.host.g_prime D.host.g_ne hsp).2
    D.nd.PlG _ (fun k => by rw [hf]; convert D.nd.card_PlG k) (fun k v => ?_) (fun k => ?_) (fun k v v' hc => ?_)
  · rw [hmemB, hnat]; exact D.naut.plGw_over k v
  · intro v v' h
    simp only at h
    apply D.naut.plGw_inj k
    apply HeightOneSpectrum.ext
    have h1 : ∀ w : HeightOneSpectrum (𝓞 D.host.E), (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal.map e = w.asIdeal :=
      fun w => Ideal.map_comap_of_surjective _ e.surjective w.asIdeal
    rw [← h1, ← h1 (D.naut.plGw k v'), h]
  · apply D.naut.plGw_nconj k v v'
    intro x y hxy
    have hst : ((e.symm y : 𝓞 X.B.I.E) : X.B.I.E) = star ((e.symm x : 𝓞 X.B.I.E) : X.B.I.E) := by
      apply X.ιE.injective
      rw [X.ιE_conj, ← he, ← he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hxy]
    have := hc (e.symm x) (e.symm y) hst
    rwa [hmemB, hmemB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at this

end GlobalTheory.RowLev.FixedChoice
