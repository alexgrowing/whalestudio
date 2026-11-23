import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAtSeesawProductDatumEqVacuumCombinationsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepVectorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCombinationsComposeFinitelyManyPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationsDistinctSplitPlacesCollectStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldrSplitPlaceSecondCombinationsVacuumNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.MidDatum

theorem vac_true_mono {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T}
    (P : GlobalTheory.FinPl.Pl D → Prop) {F : WO S T → ℂ} (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) F) :
    GlobalTheory.FinPl.Vac ψ S T LS LT P F := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) (fun _ => True) := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun _ hv => (hv trivial).elim, rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem moved_datum_eq : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (o' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb f.c.ψ _ _ o' ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j))) ∧ (((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j)) ≠ 0 → comb f.c.ψ _ _ o' ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) d → (pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((pk W).vac j)) = κ • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o' ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j))) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀
  have hstd : IsStdChar D f.c.ψ (-1) := hd₀.2.1.1
  obtain ⟨M, M', hM, hM', hmv, hmv', hvac⟩ := GlobalTheory.T.descent_data_step_lattice D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀
  obtain ⟨κ, hκ, Lp, hq, he, hint, hdat⟩ :=
    GlobalTheory.T.descent_data_step_vector D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀ M M' hM hM' hmv hmv' hvac
  have hinj : Function.Injective fun i => (Lp i).q.v := by
    intro a b h
    apply hPin.inj
    simpa only [hq] using h
  have hP : ∀ i, (Lp i).q.v ∈ v.gP := fun i => (hPin.places _).2 ⟨i, hq i⟩
  obtain ⟨o', ho', hcomb⟩ := GlobalTheory.T.localCombinations_compose_finitely_many_places D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj (· ∈ v.gP) hP
  have hN : IsSelfDualC (Yc D j) (v.N j) := hv.sd j (by omega)
  have hN' : IsSelfDualC (Yc D (j + 1)) (v.N (j + 1)) := hv.sd (j + 1) hj
  have hoff := GlobalTheory.T.descent_data_step_self_dual D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj M M' hmv hmv'
  obtain ⟨F₀, hF₀t, hF₀at, -⟩ := hdat d₀ hd₀
  have hV := (GlobalTheory.T.thetaAt_seesawProductDatum_eq_vacuumCombinations D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj _ F₀ hvac hF₀at hF₀t).2 (v.N j) (v.N (j + 1)) hN hN' hint
    (fun p hp => hoff p (by
      rw [hPin.places]
      rintro ⟨i, rfl⟩
      exact hp i (hq i).symm))
  have hth : IsThetaFunO f.c.ψ _ _ (comb f.c.ψ _ _ o' ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j))) := by
    rw [hcomb]; exact hV.1
  refine ⟨M, M', o', hM, hM', ho', vac_true_mono _ hvac, ?_, ?_, κ, hκ, ?_⟩
  · rw [hcomb]; exact vac_true_mono _ hV
  · intro hne; rw [hcomb]; exact GlobalTheory.T.foldr_splitPlaceSecondCombinations_vacuum_ne_zero D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj _ hvac hne
  · intro d hd
    obtain ⟨F, hFt, hFat, hFeq⟩ := hdat d hd
    rw [hFeq]
    congr 1
    rw [(GlobalTheory.T.thetaAt_seesawProductDatum_eq_vacuumCombinations D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj _ F hvac hFat hFt).1, GlobalTheory.T.heisenbergCombinations_distinct_split_places_collect D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj, ← hcomb,
      hPin.eG j hj _ hth]
    simp only [he]

end GlobalTheory.MidDatum
