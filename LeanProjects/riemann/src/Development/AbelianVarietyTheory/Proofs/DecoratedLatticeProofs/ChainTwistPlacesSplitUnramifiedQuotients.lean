import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPlNeOfIsSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadraticPowerCharacterSplitPlacesValuesInverse
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharUnramifiedAtQuotientSameResidualStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedConjugatePlaceInverseUniformizerValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw.TwPlaces

variable {D : D7}

theorem absNorm_under_of_ne {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F))
    (hne : w ≠ w') : Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal = Ideal.absNorm w.asIdeal := by
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq (GlobalTheory.AdelicU.isCMExt_host D) hne rfl h.symm
  rw [← GlobalTheory.LFun.SplitChart.absNorm_splitPrime τ, hτ]

theorem conjPrime_ne_of_mem {P : Finset (Pl D.host.E)} {e : AE D} (h : IsIdemSum e P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    GlobalTheory.IdemSupport.cP PP ≠ PP := by
  classical
  have hinj := GlobalTheory.LevelPlaces.under_injOn h
  obtain ⟨⟨es, hes, rfl⟩, h0⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  intro hc
  have hd : ∀ Q ∈ P, GlobalTheory.IdemSupport.IsDelta Φ Q (es Q) := fun Q hQ =>
    GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hes Q hQ)
  have e1 : Φ (∑ Q ∈ P, es Q) PP = 1 := by
    rw [GlobalTheory.LevelPlaces.ev_sum, Finset.sum_eq_single PP (fun Q hQ hQP => (hd Q hQ).2.2 PP (Ne.symm hQP))
      (fun h => absurd hPP h), (hd PP hPP).2.1]
  have e2 : Φ (cA D (∑ Q ∈ P, es Q)) PP = 1 := by
    rw [map_sum, GlobalTheory.LevelPlaces.ev_sum, Finset.sum_eq_single PP ?_ (fun h => absurd hPP h)]
    · have := (GlobalTheory.IdemSupport.delta_conj hΦ (hd PP hPP)).2.1
      rwa [hc] at this
    · intro Q hQ hQP
      refine (GlobalTheory.IdemSupport.delta_conj hΦ (hd Q hQ)).2.2 PP fun hQc => hQP ?_
      have hv : Q.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) := by rw [← GlobalTheory.IdemSupport.under_cP Q, ← hQc]
      exact hinj (Finset.mem_coe.2 hQ) (Finset.mem_coe.2 hPP) hv
  have e3 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) (∑ Q ∈ P, es Q) (cA D (∑ Q ∈ P, es Q)) PP
  rw [h0, GlobalTheory.IdemSupport.ev_zero, e1, e2, one_mul] at e3
  exact zero_ne_one e3

theorem exists_fin_of_mem {m i : ℕ} (hi : i ∈ Finset.Icc 1 m) : ∃ k : Fin m, (k : ℕ) + 1 = i := by
  rw [Finset.mem_Icc] at hi
  exact ⟨⟨i - 1, by omega⟩, by simp; omega⟩

end GlobalTheory.ChainTw.TwPlaces

open GlobalTheory.ChainTw.TwPlaces in

theorem GlobalTheory.ChainTw.twist_places : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → (∀ v, v ∈ c.S ↔ v ∈ w.S₀ ∨ ∃ PP ∈ w.Q, PP.under (𝓞 D.host.F) = v) ∧ (∀ PP ∈ w.Q, PP.under (𝓞 D.host.F) ∉ w.S₀) ∧ Set.InjOn (fun PP : Pl D.host.E => PP.under (𝓞 D.host.F)) w.Q ∧ (∀ PP ∈ w.Q, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (PP.under (𝓞 D.host.F)) ∧ Ideal.absNorm (PP.under (𝓞 D.host.F)).asIdeal = Ideal.absNorm PP.asIdeal ∧ ∃ PP' : Pl D.host.E, PP' ≠ PP ∧ (∀ P : Pl D.host.E, P.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) ↔ P = PP ∨ P = PP') ∧ Ideal.absNorm PP'.asIdeal = Ideal.absNorm PP.asIdeal ∧ ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP' = (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP)⁻¹) ∧ ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, GlobalTheory.LFun.UnrOff (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w.S₀ := by
  intro D c w hw
  classical
  obtain ⟨e, he⟩ := hw.com.split
  have hinj : Set.InjOn (fun PP : Pl D.host.E => PP.under (𝓞 D.host.F)) (c.Pg : Set (Pl D.host.E)) :=
    GlobalTheory.LevelPlaces.under_injOn he
  have hQ : ∀ PP ∈ w.Q, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_right _ h
  have hPg : ∀ PP ∈ w.Pg, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_left _ h
  have hS : ∀ v, v ∈ c.S ↔ v ∈ w.S₀ ∨ ∃ PP ∈ w.Q, PP.under (𝓞 D.host.F) = v := by
    intro v
    simp only [Com.S, Twist.S₀, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_image, hw.union,
      Finset.mem_union]
    constructor
    · rintro ⟨PP, h | h, rfl⟩
      · exact Or.inl ⟨PP, h, rfl⟩
      · exact Or.inr ⟨PP, h, rfl⟩
    · rintro (⟨PP, h, rfl⟩ | ⟨PP, h, rfl⟩)
      · exact ⟨PP, Or.inl h, rfl⟩
      · exact ⟨PP, Or.inr h, rfl⟩
  have hnot : ∀ PP ∈ w.Q, PP.under (𝓞 D.host.F) ∉ w.S₀ := by
    intro PP hPP h
    simp only [Twist.S₀, Finset.coe_image, Set.mem_image, Finset.mem_coe] at h
    obtain ⟨PP₀, h0, he0⟩ := h
    have := hinj (Finset.mem_coe.2 (hPg PP₀ h0)) (Finset.mem_coe.2 (hQ PP hPP)) he0
    subst this
    exact Finset.disjoint_left.1 hw.disj h0 hPP
  have hsplit : ∀ PP ∈ c.Pg, Formalism.DivisionValues.conjPl PP ≠ PP := fun PP h => by
    rw [GlobalTheory.LevelPlaces.conjPl_eq_cP]; exact conjPrime_ne_of_mem he h
  have hres : ∀ PP ∈ w.Q, ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m,
      GlobalTheory.LFun.UnrAt (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP := by
    intro PP hPP i hi j hj
    obtain ⟨a, rfl⟩ := exists_fin_of_mem hi
    obtain ⟨b, rfl⟩ := exists_fin_of_mem hj
    obtain ⟨Ha, hca, hra⟩ := hw.com.res a
    obtain ⟨Hb, hcb, hrb⟩ := hw.com.res b
    have ra := hra PP (hQ PP hPP)
    have rb := hrb PP (hQ PP hPP)
    rw [hw.chiQ _ PP hPP, inv_inv] at ra rb
    exact GlobalTheory.T.heckeCharUnramifiedAt_quotient_same_residual D _ _ Ha Hb PP _ hca hcb ra rb
  have hre : ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, ResEta D (c.μ i * (c.μ j)⁻¹) 0 := by
    intro i hi j hj
    obtain ⟨-, ⟨η, hη⟩, hi'⟩ := hw.com.chars.2.2.2.2 i hi
    obtain ⟨-, -, hj'⟩ := hw.com.chars.2.2.2.2 j hj
    refine ⟨⟨η, hη⟩, fun η' hη' a => ?_⟩
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hi' η' hη' a, hj' η' hη' a]
    simp
  refine ⟨hS, hnot, hinj.mono fun x hx => Finset.mem_coe.2 (hQ x (Finset.mem_coe.1 hx)), fun PP hPP => ?_, ?_⟩
  · have hne : Formalism.DivisionValues.conjPl PP ≠ PP := hsplit PP (hQ PP hPP)
    have hu : (Formalism.DivisionValues.conjPl PP).under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) := ParInv.under_conjPl PP
    refine ⟨GlobalTheory.LFun.ConjPlace.isSplit_of_ne hne.symm rfl hu, absNorm_under_of_ne hu.symm hne.symm,
      Formalism.DivisionValues.conjPl PP, hne, fun P => ⟨fun h => ?_, ?_⟩, ParInv.absNorm_conjPl' PP, fun i hi j hj => ?_⟩
    · rcases GlobalTheory.GridPlaces.eq_or_eq_conjP h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (h1.trans (ParInv.conjP_eq_conjPl' PP))
    · rintro (rfl | rfl)
      · rfl
      · exact hu
    · exact (GlobalTheory.T.unramified_conjugate_place_inverse_uniformizer_value D _ (hre i hi j hj) PP _ hu.symm hne.symm (hres PP hPP i hi j hj)).2
  · intro i hi j hj W hW
    by_cases hWS : W.under (𝓞 D.host.F) ∈ c.S
    · rcases (hS _).1 hWS with h | ⟨PP, hPP, hPPW⟩
      · exact absurd h hW
      · rcases GlobalTheory.GridPlaces.eq_or_eq_conjP hPPW.symm with h1 | h1
        · rw [h1]; exact hres PP hPP i hi j hj
        · have hne := hsplit PP (hQ PP hPP)
          rw [h1, ParInv.conjP_eq_conjPl']
          exact (GlobalTheory.T.unramified_conjugate_place_inverse_uniformizer_value D _ (hre i hi j hj) PP _ (ParInv.under_conjPl PP).symm hne.symm
            (hres PP hPP i hi j hj)).1
    · obtain ⟨a, rfl⟩ := exists_fin_of_mem hi
      obtain ⟨b, rfl⟩ := exists_fin_of_mem hj
      have hW' : W ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := hWS
      exact (hw.com.unr a W hW').mul (hw.com.unr b W hW').inv

end
