import Mathlib
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KCoinvOfDict
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoCoinvariantsOfBernstein
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.RamifiedMultiplicityOneOfBernstein
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitTop

open ValuativeRel Matrix Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BernBridge.Split

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr

def NarrowBernstein : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
    (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible

def IndIrredLt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (α β : kˣ →* ℂˣ), (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
    IsSmoothChar α → IsSmoothChar β → a' < a →
    ∀ N : Submodule ℂ (GL (Fin (a + a')) k → ℂ), N ≤ indSp a a' α β → (∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N) →
      N = ⊥ ∨ N = indSp a a' α β

theorem indIrredLt_of (NB : NarrowBernstein) : IndIrredLt := by
  intro k _ _ _ _ a a' α β hα hβ sα sβ hlt N hN hr
  by_cases h0 : N = ⊥
  · exact Or.inl h0
  refine Or.inr (le_antisymm hN ?_)
  obtain ⟨F, hFN, hF0⟩ := (Submodule.ne_bot_iff N).1 h0
  have hI : (parInd (two (stdE a a')) (rhoD a a' α β)).IsIrreducible :=
    NB k a a' α β sα sβ hα hβ (Or.inl hlt.ne')
  let S : Subrepresentation (parInd (two (stdE a a')) (rhoD a a' α β)) :=
    ⟨N.comap (toFn a a' α β), fun g f hf => hr g _ hf⟩
  rcases hI.eq_bot_or_eq_top S with e | e
  · obtain ⟨f, rfl⟩ := exists_toFn (hN hFN)
    have hf : f ∈ S.toSubmodule := hFN
    rw [e] at hf
    have hf0 : f = 0 := hf
    exact absurd (by rw [hf0, map_zero]) hF0
  · intro G hG
    obtain ⟨f, rfl⟩ := exists_toFn hG
    have hf : f ∈ S.toSubmodule := by rw [e]; trivial
    exact hf

section Onto
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem onto_of_irredLt (hI : IndIrredLt) {a a' : ℕ} {α β : kˣ →* ℂˣ} (hα : ∀ x, ‖(α x : ℂ)‖ = 1)
    (hβ : ∀ x, ‖(β x : ℂ)‖ = 1) (sα : IsSmoothChar α) (sβ : IsSmoothChar β) (hlt : a' < a)
    {X : Type} [TopologicalSpace X] (p : (X → ℂ) → GL (Fin (a + a')) k → ℂ)
    (hlin : ∀ Φ ∈ SB X, ∀ Φ₁ ∈ SB X, ∀ c : ℂ, p (Φ + c • Φ₁) = p Φ + c • p Φ₁)
    (hin : ∀ Φ ∈ SB X, p Φ ∈ indSp a a' α β)
    (heq : ∀ Φ ∈ SB X, ∀ h₁, ∃ Φ' ∈ SB X, p Φ' = rtr h₁ (p Φ))
    (hne : ∃ Φ ∈ SB X, p Φ ≠ 0) : ∀ F ∈ indSp a a' α β, ∃ Φ ∈ SB X, p Φ = F := by
  have h0 : p 0 = 0 := by
    have := hlin 0 (SB X).zero_mem 0 (SB X).zero_mem 1
    simpa using this
  let N : Submodule ℂ (GL (Fin (a + a')) k → ℂ) :=
    { carrier := {F | ∃ Φ ∈ SB X, p Φ = F}
      add_mem' := by
        rintro _ _ ⟨Φ, hΦ, rfl⟩ ⟨Φ₁, hΦ₁, rfl⟩
        exact ⟨Φ + (1 : ℂ) • Φ₁, (SB X).add_mem hΦ ((SB X).smul_mem _ hΦ₁), by rw [hlin _ hΦ _ hΦ₁, one_smul]⟩
      zero_mem' := ⟨0, (SB X).zero_mem, h0⟩
      smul_mem' := by
        rintro c _ ⟨Φ, hΦ, rfl⟩
        exact ⟨0 + c • Φ, (SB X).add_mem (SB X).zero_mem ((SB X).smul_mem _ hΦ), by
          rw [hlin _ (SB X).zero_mem _ hΦ, h0, zero_add]⟩ }
  have hle : N ≤ indSp a a' α β := by
    rintro _ ⟨Φ, hΦ, rfl⟩
    exact hin Φ hΦ
  have hst : ∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N := by
    rintro h₁ _ ⟨Φ, hΦ, rfl⟩
    exact heq Φ hΦ h₁
  rcases hI k a a' α β hα hβ sα sβ hlt N hle hst with h | h
  · obtain ⟨Φ, hΦ, hne⟩ := hne
    have hm : p Φ ∈ N := ⟨Φ, hΦ, rfl⟩
    rw [h] at hm
    exact absurd ((Submodule.mem_bot ℂ).1 hm) hne
  · intro F hF
    rw [← h] at hF
    exact hF

end Onto

theorem unrMaps_of_lt (hI : IndIrredLt) : UnrMaps := by
  intro k _ _ _ _ _ _ a a' ϖ α β ν hS hα hβ
  have hν := isUnram_nu hS hα hβ
  have hp1 := p_lin hS hν
  have hp2 := p'_lin hS hν
  have hp3 := p_mem hS hν hβ
  have hp4 := p'_mem hS hν hα
  have hu := p_unit hS hν hβ
  have hu' := p'_unit hS hν hα
  have sα : IsSmoothChar α := isSmoothChar_of_isUnram hα
  have sβ : IsSmoothChar β := isSmoothChar_of_isUnram hβ
  refine ⟨hp1, hp2, hp3, hp4, p_inv hS hν, p'_inv hS hν, fun Φ _ h₁ => p_equiv Φ h₁, fun Ψ _ h₁ => p'_equiv Ψ h₁,
    ?_, ?_, hu, hu'⟩
  · refine onto_of_irredLt hI hS.unitα hS.unitβ sα sβ hS.lt _ hp1 hp3
      (fun Φ hΦ h₁ => ⟨_, omA_mem_SB ν β 1 h₁ hΦ, p_equiv Φ h₁⟩) ⟨_, indicator_int_mem_SB, fun h0 => ?_⟩
    simpa [hu 1 (one_mem _)] using congrFun h0 1
  · refine onto_of_irredLt hI hS.unitα hS.unitβ sα sβ hS.lt _ hp2 hp4
      (fun Ψ hΨ h₁ => ⟨_, omB_mem_SB ν α 1 h₁ hΨ, p'_equiv Ψ h₁⟩) ⟨_, indicator_int_mem_SB, fun h0 => ?_⟩
    simpa [hu' 1 (one_mem _)] using congrFun h0 1

section Global

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThK PositivityTheory.ThK.SplitAsm

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance measFv {F : Type} [Field F] [NumberField F] (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFv {F : Type} [Field F] [NumberField F] (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

theorem finSplit_of_lt (hU : UnrMaps) (hI : IndIrredLt) (hIw : IndIwasawa) (hD : Dict) (hAU : ActsUniq) (hC : ChrFacts)
    (hZ : IntEq) : FinSplit := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v ⟨hv, ⟨τ⟩⟩
  obtain ⟨hα, hβ, hν, hcond, -, hunr⟩ := hC F E B X a a' v τ hT.chars
  obtain ⟨hαu, hβu⟩ := hunr hv
  have hS : HidaSetting a a' (unifAt v) (chrW X.α τ) (chrW X.β τ) (chrW X.ν τ) :=
    ⟨GlobalTheory.SplitFlip.exists_isUnif.choose_spec, hα, hβ, hν, hT.geo.lt, hT.geo.even, hcond⟩
  obtain ⟨hlin, hlin', hmem, hmem', hinv, hinv', heq, heq', hon, hon', hsph, hsph'⟩ :=
    hU (Fv F v) a a' _ _ _ _ hS hαu hβu
  obtain ⟨b, b', c, ι, ι', gl, gl', hl, hW, hB, -, hvac, hvac', hRg, hRh, hRg', hRh', hhl⟩ :=
    hD F E σ B a a' G X om om' hT v τ
  have hind : ∀ m n : ℕ, (intInd v : Matrix (Fin m) (Fin n) (Fv F v) → ℂ) =
      Set.indicator {Y | ∀ i j, Y i j ∈ 𝒪[Fv F v]} 1 := by
    intro m n
    unfold intInd
    congr 1
    ext Y
    simp only [Set.mem_setOf_eq, hZ F v]
  have h1 : ∀ h ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (a + a')), pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) h = 1 :=
    fun h hh => by rw [hind]; exact hsph h hh
  have h1' : ∀ h ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (a + a')), pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) h = 1 :=
    fun h hh => by rw [hind]; exact hsph' h hh
  have hiSB : intInd v ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) := by
    rw [← hvac]; exact hW.bij.mapsTo (hT.geo.hM.vac v).1
  have hnz : pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) ≠ 0 := fun h0 => by
    have := h1 1 (one_mem _)
    rw [h0] at this
    exact zero_ne_one this
  obtain ⟨p, p', hp, hp', hon1, hon1', hinv1, hinv1', heq1, hnt, hirr1⟩ := core hAU v G om om' _ _ _ (indSp a a' _ _)
    (pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ)) (pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ))
    (fun Φ h Φ₁ h₁ => hlin Φ h Φ₁ h₁) (fun Φ h Φ₁ h₁ => hlin' Φ h Φ₁ h₁)
    (fun Φ h => hmem Φ h) (fun Φ h => hmem' Φ h) (fun Φ h => hinv Φ h)
    (fun Φ h => hinv' Φ h) (fun Φ h => heq Φ h) (fun Φ h => heq' Φ h)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon y hy; exact ⟨Φ, h, r⟩)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon' y hy; exact ⟨Φ, h, r⟩) ⟨_, hiSB, hnz⟩
    (fun N hN hst => hI (Fv F v) a a' _ _ hα hβ (isSmoothChar_of_isUnram hαu) (isSmoothChar_of_isUnram hβu)
      hT.geo.lt N hN hst) ι ι' hW.bij hB.bij gl gl' hl hRg hRh hRg' hRh' hhl
  refine ⟨oneMaps v _ p p', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [oneMaps_p]; exact hon1
  · rw [oneMaps_p']; exact hon1'
  · rw [oneMaps_p]; exact hinv1
  · rw [oneMaps_p']; exact hinv1'
  · rw [oneMaps_p, oneMaps_p']; exact heq1
  · exact hnt
  · rw [oneMaps_p]; exact hirr1
  · intro _
    rw [oneMaps_p, oneMaps_p']
    have e1 := hp _ (hT.geo.hM.vac v).1
    have e2 := hp' _ (hT.geo.hM'.vac v).1
    rw [hvac] at e1
    rw [hvac'] at e2
    have hm1 := hmem _ hiSB
    have hm2 : pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) ∈ indSp a a' (chrW X.α τ) (chrW X.β τ) := by
      rw [← e2]; exact (p' (G.M'.vac v)).2
    have hd : pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) -
        pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) = 0 :=
      hIw (Fv F v) a a' _ _ _ (Submodule.sub_mem _ hm1 hm2) fun h hh => by
        simp only [Pi.sub_apply, h1 h hh, h1' h hh, sub_self]
    refine ⟨Subtype.ext ?_, fun h0 => hnz ?_⟩
    · erw [e1, e2]; exact sub_eq_zero.1 hd
    · have := congrArg Subtype.val h0
      erw [e1] at this
      exact this
  · intro _ hvT; exact absurd hvT hv

theorem finSplit_of_narrow : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
    (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible) → PositivityTheory.ThK.FinSplit :=
  fun NB => finSplit_of_lt (unrMaps_of_lt (indIrredLt_of NB)) (indIrredLt_of NB) induced_vanish_of_vanish_on_integral split_place_dictionary
    PositivityTheory.KCo.action_uniqueness split_character_facts valuation_integers_eq_completion

end Global

end GlobalTheory.CompanionTheory.BernBridge.Split
