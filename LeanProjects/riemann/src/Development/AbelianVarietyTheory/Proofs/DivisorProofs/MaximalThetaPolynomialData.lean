import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementInSocleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxThetaVanishingLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxThetaVanishingGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxThetaVanishingArchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxThetaVanishingFiniteStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThKLocSS

theorem stableComplementAt : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (P : Submodule ℂ (GlobalTheory.ThK.Fn F a (a + a'))), N ≤ P → P ≤ GlobalTheory.ThK.PolData B G.M → (∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), ∀ Φ ∈ P, om (1, h) Φ ∈ P) → ∃ C : Submodule ℂ (GlobalTheory.ThK.Fn F a (a + a')), C ≤ GlobalTheory.ThK.PolData B G.M ∧ (∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), ∀ Φ ∈ C, om (1, h) Φ ∈ C) ∧ P ⊔ C = GlobalTheory.ThK.PolData B G.M ∧ P ⊓ C = N := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT N hN hker v P hNP hPD hP
  set D := GlobalTheory.ThK.PolData B G.M with hD
  set T := GlobalTheory.ThKLocSS.opsAt om v with hTdef
  have hND : N ≤ D := hN.le
  have hWS : GlobalTheory.ThetaFac.WStable B om D (GlobalTheory.ThKLocSS.socleOver T N D) :=
    ⟨GlobalTheory.T.om_finPlace_mem_socleOver_polData hKP F E σ B a a' G X om om' hT N hN hker v,
     GlobalTheory.T.max_theta_vanishing_finite hKP F E σ B a a' G X om om' hT N hN hker v,
     GlobalTheory.T.om_kInf_mem_socleOver_polData hKP F E σ B a a' G X om om' hT N hN hker v⟩
  have hsoc : GlobalTheory.ThKLocSS.socleOver T N D = D := by
    rcases hN.max _ (GlobalTheory.ThKLocSS.le_socleOver T N D) (GlobalTheory.ThKLocSS.socleOver_le T hND) hWS with h | h
    · exfalso
      obtain ⟨S, hSD, hS⟩ := GlobalTheory.T.max_theta_vanishing_local hKP F E σ B a a' G X om om' hT N hN hker v
      have := GlobalTheory.ThKLocSS.le_socleOver_of_simple T hSD hS
      rw [h] at this
      exact lt_irrefl _ (lt_of_lt_of_le hS.1 this)
    · exact h
  have hNs : GlobalTheory.ThKLocSS.OpStable T N := (GlobalTheory.ThKLocSS.opStable_opsAt_iff om v N).2 (hN.stab.fin v)
  have hPs : GlobalTheory.ThKLocSS.OpStable T P := (GlobalTheory.ThKLocSS.opStable_opsAt_iff om v P).2 hP
  obtain ⟨C, hCD, hCs, hsup, hinf⟩ := GlobalTheory.T.stable_complement_in_socle _ T N D P hND hNs hsoc hNP hPD hPs
  exact ⟨C, hCD, (GlobalTheory.ThKLocSS.opStable_opsAt_iff om v C).1 hCs, hsup, hinf⟩

end GlobalTheory.ThKLocSS

end
