import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsLatInd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExistsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelCombinationEqSinglePlaceOnVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsModelChg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointWeilCharConductorOneOfUnits
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixUpImageCompletedHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasisStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section
namespace GlobalTheory.VacComb

variable {D : D7}

theorem isThetaFunO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 where
  quasi _ _ := by simp
  level := ⟨⊤, isOpen_univ, fun _ _ _ => funext fun _ => by simp [heisO]⟩
  cont := continuous_const
  smooth _ _ _ _ _ := by simpa using (contDiff_const : ContDiff ℝ _ fun _ : Fin _ → ℝ => (0 : ℂ))

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : heisO ψ S T u 0 = 0 :=
  funext fun _ => by simp [heisO]

theorem isModel_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) :
    p.IsModel ψ FS FT (0 : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) where
  theta _ := isThetaFunO_zero ψ S T
  trans _ _ _ _ := by simp [heisO_zero]
  modul _ _ _ _ _ := by simp [heisO_zero]

theorem model_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {Y Y' : Type} [Fintype Y]
    [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y} {Tm}
    (hTm : p.IsModel ψ FS FT Tm) {Φ₀ : SB (Matrix Y Y' k)} (h₀ : Tm Φ₀ ≠ 0) {O : SB (Matrix Y Y' k)} (hO : O ≠ 0) :
    Tm O ≠ 0 := by
  intro h
  have := (GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k p Y Y' S T FS FT ψ hψ).1 Tm 0 hTm (isModel_zero p ψ FS FT) O hO (by simpa using h)
  exact h₀ (by rw [this]; rfl)

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

theorem exists_adapted_frame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (M : GlobalTheory.FinPl.Lat S), IsSelfDualC S M → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y), ∃ G : Frame k S.rank Y, ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((G.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S M (· = q.v) := by
  intro D k _ _ _ _ q S M hM Y _ _ F
  obtain ⟨gl, h1, h2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D k q S Y F.β F.γ F.βγ F.γβ
  let α : GlobalTheory.FinPl.Frame q S Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, h1, h2⟩
  obtain ⟨Λ, hΛ, hα, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y α M hM
  haveI := hΛ
  obtain ⟨g, hg⟩ := GlobalTheory.LatPair.exists_smul_lat (GlobalTheory.LatPair.stdLat k Y) Λ
  have hgg : g.1 * (g⁻¹).1 = 1 := by rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hgg' : (g⁻¹).1 * g.1 = 1 := by rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  refine ⟨⟨F.β * g.1, (g⁻¹).1 * F.γ, ?_, ?_⟩, fun y => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc g.1, hgg, Matrix.one_mul, F.βγ]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, hgg']
  · have e1 : (∀ i, y i ∈ 𝒪[k]) ↔ g • y ∈ Λ := by
      rw [← hg, GlobalTheory.LatPair.mem_smul_iff, inv_smul_smul, GlobalTheory.LatPair.mem_stdLat]
    rw [e1, hα (g • y)]
    show _ ∈ _ ↔ _ ∈ _
    have e2 : F.β *ᵥ (g • y) = (F.β * g.1) *ᵥ y := by
      rw [← Matrix.mulVec_mulVec]; rfl
    change (fun i => q.sec ((F.β *ᵥ (g • y)) i)) ∈ _ ↔ _
    rw [e2]

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

variable {D : D7}

theorem down_up {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) : p.down FS FT (p.up FS FT x) = x := by
  unfold Place.down Place.up
  have h : ((FT.β * x * FS.γ).map p.ι : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = FT.β * x * FS.γ := by
    ext i j; simp [p.π_ι]
  rw [h, Matrix.mul_assoc FT.β, ← Matrix.mul_assoc FT.γ, FT.γβ, Matrix.one_mul, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]

theorem exists_model_vac : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ G, GlobalTheory.FinPl.Vac ψ S T M M' (· = q.v) G → ∃ Tm, (ofSplit q).IsModel ψ FS FT Tm ∧ ∀ Φ₀ : SB (Matrix Y Y' k), Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v)} (fun _ => 1) → Tm Φ₀ = G := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT ψ hψ M M' hM hM' G hG
  obtain ⟨GS, hGS⟩ := exists_adapted_frame D k q S M hM Y' FS
  obtain ⟨GT, hGT⟩ := exists_adapted_frame D k q T M' hM' Y FT
  obtain ⟨ψk, hch, hcond⟩ := GlobalTheory.SplitWeilChar.weil_char_conductor_one D k q ψ hψ hU
  obtain ⟨Tm', hTm', hO'⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D k q hU Y Y' S T GS GT ψ ψk hψ hch hcond M M' hM hM' hGS hGT).2 G hG
  obtain ⟨Tm, hTm, hrel⟩ := GlobalTheory.LocMod.Place.exists_isModel_chg D k (ofSplit q) Y Y' S T GS GT Y Y' FS FT ψ Tm' hTm'
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  refine ⟨Tm, hTm, fun Φ₀ h₀ => ?_⟩
  rw [hrel O Φ₀ ?_, hO' O hO]
  intro x
  have hup : (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) = (ofSplit q).up GS GT x :=
    GlobalTheory.LocMod.Place.up_chg (ofSplit q) GS GT FS FT x
  rw [hO, h₀]
  by_cases hx : ∀ r s, x r s ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (show x ∈ {x : Matrix Y Y' k | ∀ r s, x r s ∈ 𝒪[k]} from hx), Set.indicator_of_mem]
    show (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v)
    rw [hup]
    exact GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T GS GT M M' hM hM' hGS hGT x hx
  · rw [Set.indicator_of_notMem (show x ∉ {x : Matrix Y Y' k | ∀ r s, x r s ∈ 𝒪[k]} from hx), Set.indicator_of_notMem]
    intro hmem
    change (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v) at hmem
    rw [hup] at hmem
    obtain ⟨x', hx', he⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T GS GT M M' hM hM' hGS hGT _ hmem
      (GlobalTheory.LocMod.Witness.up_half (ofSplit q) GS GT x)
    have : x = x' := by rw [← down_up (ofSplit q) GS GT x, he, down_up]
    exact hx (this ▸ hx')

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

variable {D : D7}

theorem comb_o_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M')
    (L : LocPl ψ S T M M') {G : WO S T → ℂ} (hG : GlobalTheory.FinPl.Vac ψ S T M M' (· = L.q.v) G) (hG0 : G ≠ 0) :
    comb ψ S T L.o G ≠ 0 := by
  obtain ⟨Tm, hTm, hTG⟩ := exists_model_vac D L.k L.q L.unit L.Y L.Y' S T L.FS L.FT ψ hψ M M' hM hM' G hG
  obtain ⟨Φ₀, h₀⟩ := GlobalTheory.SeeSaw.LocPlModel.exists_latInd L.q L.unit L.FS L.FT hM hM'
  obtain ⟨O, hO, hO0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := L.k) (Y := L.Y) (Y' := L.Y')
  have hO' : O ≠ 0 := by rintro rfl; simp at hO0
  rw [← hTG Φ₀ h₀, ← L.o_is Tm hTm Φ₀ O hO h₀]
  exact model_ne_zero _ hψ hTm (by rwa [hTG Φ₀ h₀]) hO'

theorem combAt_o {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (L : LocPl ψ S T M M') : GlobalTheory.FinPl.CombAt (· = L.q.v) L.o := fun u hu r c =>
  (GlobalTheory.FinPl.FrameLat.idem_iff L.q _).2 (L.o_at u hu r c)

theorem foldr_comb_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) F → F ≠ 0 → (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F ≠ 0 := by
  intro D ψ hψ S T M M' hM hM' n L hL F hF hF0
  have hI := fun P P' hd => GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D ψ hψ S T P P' hd
  let g : Fin n → (WO S T → ℂ) → (WO S T → ℂ) := fun i f => comb ψ S T (L i).o f
  have key : ∀ l : List (Fin n), l.Nodup → l.foldr g F ≠ 0 ∧
      ∀ j, j ∉ l → GlobalTheory.FinPl.Vac ψ S T M M' (· = (L j).q.v) (l.foldr g F) := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨hF0, fun j _ => GlobalTheory.GSuppComb.vac_mono (fun _ _ => trivial) hF⟩
    | cons a l ih =>
      intro hl
      obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
      obtain ⟨h0, hv⟩ := ih hl'
      have hdisj : ∀ j, j ≠ a → ∀ p, p = (L a).q.v → ¬ p = (L j).q.v := fun j hj p hp hq =>
        hj (hL (hq.symm.trans hp))
      refine ⟨comb_o_ne_zero hψ hM hM' (L a) (hv a ha) h0, fun j hj => ?_⟩
      have hja : j ≠ a := fun h => hj (h ▸ List.mem_cons_self)
      have hjl : j ∉ l := fun h => hj (List.mem_cons_of_mem _ h)
      exact ((hI _ _ (hdisj j hja)).2.1 _ (combAt_o (L a))).2 M M' _ (hv j hjl)
  exact (key _ (List.nodup_finRange n)).1

end GlobalTheory.VacComb
