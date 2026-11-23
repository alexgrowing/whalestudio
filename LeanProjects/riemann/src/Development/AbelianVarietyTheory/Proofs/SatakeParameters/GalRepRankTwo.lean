import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalFirstClause

open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp

set_option maxHeartbeats 2000000 in

theorem galRep_rankTwo : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.LocalGlobalAboveL → GlobalTheory.Published.RegularAlgebraicPurity → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (i : D.nd.Loc) (a : ℕ), 2 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2) ∧ D.naut.tempered (D.naut.locG π w)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ (∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.jumpsInf i π τ) ∧ D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2) := by
  intro hF hG hLG hRP hL D P i a ha π hc hr
  have := host_isCMField D.host
  have ha1 : 1 ≤ a := by omega
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (P.cg.e a π).1
  have hmk : CG.mk π₀ = (P.cg.e a π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (P.cg.csd a π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [P.cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  obtain ⟨r, wt, HT, H⟩ := hG.of_isCsd D.nd.Om (D.naut.iotaQC i) ha1 hr₀ hc₀
  have hcoh := (hRP D.host.E a ha1 π₀ hr₀).2
  have hcont : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))) := Units.continuous_val.comp H.cont
  have hloc : ∀ (w : PlE D.host) (u : ℝ), P.T.e w (D.naut.lpTw (D.naut.locG π w) u) =
      (ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw u := fun w u => by
    rw [P.T.tw, P.cg.loc, hmk]
    rfl
  have haway : ∀ (w : PlE D.host) (hl : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      wdOf (D.nd.plOm.2 w) hl (D.naut.iotaQC i) r =
        P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) := fun w hl => by
    rw [wdOfEqLocPar hL hF H hl, hloc]
  have hv : (1 - (a : ℝ)) / 2 + (wt : ℝ) / 2 = 0 := by
    refine exponentEqZero D.naut ha1 π hc (D.nd.l i) _ fun w hl => ?_
    have h1 := H.tempered_wdOf hl (D.nd.plOm.2 w)
    rw [haway w hl, ← P.T.tw, ← P.T.tempered, D.naut.lpTw_add] at h1
    exact h1
  have htemp : ∀ w : PlE D.host, ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal →
      D.naut.tempered (D.naut.locG π w) := fun w hl => by
    have h1 := H.tempered_wdOf hl (D.nd.plOm.2 w)
    rw [haway w hl, ← P.T.tw, ← P.T.tempered, D.naut.lpTw_add, hv, D.naut.lpTw_zero] at h1
    exact h1
  have hWaway : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      D.naut.wdOf i r w = D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2) := fun w hw => by
    rw [(P.wdOf i a r w).1]
    exact (P.T.e w).injective (by rw [P.wd.away _ _ r w hw, haway w hw])
  obtain ⟨K, ρ, hρc, hρ⟩ := finextRep (D.nd.l i) D.host.E D.nd.Om a r hcont
  have hside : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), P.wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w ∧
      ∀ τ : D.host.E →+* Qbar (D.nd.l i), (∀ (A : ValuationSubring D.nd.Om), IsPlaceOver A w →
        ∀ (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
          (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) A) O),
          Induces Bw → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Bw.LL.1, IsInduced Bw τ τ') →
        P.wd.jumpsW (D.nd.l i) (D.naut.iotaQC i) r τ = HT τ := by
    intro w hw
    obtain ⟨j, L0, hj, hLL⟩ := GlobalTheory.PlaceBridge.exists_locBridge (D.nd.l i) D.host.E D.nd.Om w (D.nd.plOm.1 w) hw
      (D.nd.plOm.2 w)
    obtain ⟨Bw, hBj, hBLL, -, hBto⟩ := hLL L0 le_rfl
    have hind : Induces Bw := fun x => by rw [hBj]; exact hj x
    let LL' : FinExt (D.nd.l i) := supExt K Bw.LL
    have hK : K.1 ≤ LL'.1 := le_sup_left
    have hB : Bw.LL.1 ≤ LL'.1 := le_sup_right
    let ρ' : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1 := mapRep (IntermediateField.inclusion hK).toRingHom ρ
    have hρ' : mapRep (algebraMap ↥LL'.1 (Om (D.nd.l i))) ρ' = r := by
      rw [← hρ]
      ext g i k
      rfl
    have hρ'c : Continuous fun g => (ρ' g : Matrix (Fin a) (Fin a) ↥LL'.1) := by
      have hi : Continuous (IntermediateField.inclusion hK) :=
        continuous_induced_rng.2 continuous_subtype_val
      exact hρc.matrix_map hi
    have hmodel : IsModel Bw (resDec D.nd.plOm.1 r w) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
      ⟨hB, by rw [← hρ']; rfl⟩
    let φ : ↥(OL L0) →+* Qbar (D.nd.l i) := L0.1.val.toRingHom.comp (OL L0).val.toRingHom
    have hφ : ∀ x, φ x = ((Bw.toLL x : ↥Bw.LL.1) : Om (D.nd.l i)) := fun x => (hBto x).symm
    have hcl := (P.wd.loc (D.nd.l i) (D.naut.iotaQC i) w hw _ Bw hind φ hφ).2 LL' hB a ρ' hρ'c
    rw [hρ'] at hcl
    have hab := H.above (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw hind
    have hdR : Bw.IsdRE (D.loc (D.nd.l i)) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
      (hmodel.isdRAt_iff (D.loc (D.nd.l i))).1 hab.deRham
    refine ⟨hcl.2.1.2 hdR, fun τ hτ => ?_⟩
    obtain ⟨τ₀, hτ₀⟩ := hτ _ (D.nd.plOm.2 w) _ Bw hind
    let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1 := (IntermediateField.inclusion hB).comp τ₀
    have hτ'' : IsInduced Bw τ τ'' := fun x => hτ₀ x
    have hJ := hab.jumps τ LL' τ'' hτ''
    ext n
    apply Nat.cast_injective (R := ℤ)
    rw [(hcl.2.2.2 τ τ'' hτ'').2 hdR n, IsJumpsAt.count_eq (D.loc (D.nd.l i)) hmodel hτ'' hJ n]
  refine ⟨r, hcont, H.ss, fun w hw => ⟨hWaway w hw, htemp w hw⟩, fun w hw => ⟨?_, fun τ _ => ?_, ?_⟩⟩
  · exact ((P.wdOf i a r w).2.2.2.1).2 (hside w hw).1
  · obtain ⟨w', hw', hτ⟩ := existsIsInduced (D.nd.l i) D.host.E D.nd.Om τ
    rw [(P.wdOf i a r w).2.2.2.2 τ, (hside w' hw').2 τ hτ]
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights, D.naut.jumpsInf_def i π τ hr, hinf]
    refine Multiset.map_congr rfl fun z _ => ?_
    ring
  · rw [(P.wdOf i a r w).1]
    obtain ⟨LL, Bw', hj', he⟩ := P.wd.above _ (D.naut.iotaQC i) r w hw
    obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp hF _ _ π₀ w
    have h2 := hLG D.host.E D.nd.Om (D.nd.l i) (D.naut.iotaQC i) a ha π₀ hc₀ hcoh r wt HT H (D.loc _) (D.locA _)
      ⟨D.locT _⟩ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw' hj' σ₀ hσ₀ _ (ParLaws.isRec_locRec hL (D.nd.plOm.2 w))
    refine (P.T.e w).injective ?_
    rw [he]
    refine h2.trans ?_
    rw [rec_algNorm (ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) σ₀, hloc, ParLaws.locPar_mk hL hσ₀ (D.nd.plOm.2 w)]
    rfl

end GlobalTheory.GalFirstClause
