import Mathlib
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KCoinvOfDict
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoCoinvariantsOfBernstein
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.RamifiedMultiplicityOneOfBernstein
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitTop

open ValuativeRel Matrix Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitNarrow

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitDict PositivityTheory.ThK.SplitAsm

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_of_condLE {ϖ : kˣ} {e : ℕ} {χ : kˣ →* ℂˣ} (h : CondLE ϖ e χ) : IsSmoothChar χ := by
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have h1 : IsOpen (({x : kˣ | (x : k) ∈ (𝒪[k] : Set k)} ∩ {x : kˣ | ((x⁻¹ : kˣ) : k) ∈ (𝒪[k] : Set k)}) ∩
      {x : kˣ | ((x : k) - 1) * (((ϖ ^ e : kˣ) : k))⁻¹ ∈ (𝒪[k] : Set k)}) :=
    ((ho.preimage Units.continuous_val).inter (ho.preimage Units.continuous_coe_inv)).inter
      (ho.preimage ((Units.continuous_val.sub continuous_const).mul continuous_const))
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (h1.mem_nhds ?_) ?_)
  · refine ⟨⟨one_mem 𝒪[k], by simpa using one_mem 𝒪[k]⟩, ?_⟩
    simpa using zero_mem 𝒪[k]
  · rintro x ⟨⟨hx, hx'⟩, hx''⟩
    have a1 : valuation k (x : k) ≤ 1 := hx
    have a2 : valuation k ((x⁻¹ : kˣ) : k) ≤ 1 := hx'
    have a3 : valuation k (((x : k) - 1) * (((ϖ ^ e : kˣ) : k))⁻¹) ≤ 1 := hx''
    have hc : valuation k (((ϖ ^ e : kˣ) : k)) ≠ 0 := by simp
    refine h x ⟨le_antisymm a1 ?_, ?_⟩
    · rw [Units.val_inv_eq_inv_val, map_inv₀] at a2
      exact (inv_le_one₀ (zero_lt_iff.2 (by simp))).1 a2
    · rw [map_mul, map_inv₀] at a3
      have a4 := (mul_inv_le_iff₀ (zero_lt_iff.2 hc)).1 a3
      rwa [one_mul] at a4

def IndIrredNarrow : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (α β : kˣ →* ℂˣ), IsSmoothChar α → IsSmoothChar β → (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
    a' < a → ∀ N : Submodule ℂ (GL (Fin (a + a')) k → ℂ), N ≤ indSp a a' α β → (∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N) →
      N = ⊥ ∨ N = indSp a a' α β

theorem indIrredNarrow_of
    (NB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
      (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
      (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible) : IndIrredNarrow := by
  intro k _ _ _ _ a a' α β sα sβ hα hβ hlt N hN hr
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

theorem irred_of_setting (hI : IndIrredNarrow) {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ} (H : HidaSetting a a' ϖ α β ν)
    (N : Submodule ℂ (GL (Fin (a + a')) k → ℂ)) (hN : N ≤ indSp a a' α β) (hst : ∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N) :
    N = ⊥ ∨ N = indSp a a' α β := by
  obtain ⟨e, h1, h2⟩ := H.cond
  exact hI k a a' α β (isSmoothChar_of_condLE h1) (isSmoothChar_of_condLE h2) H.unitα H.unitβ H.lt N hN hst

theorem onto_of_irred (hI : IndIrredNarrow) {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ} (H : HidaSetting a a' ϖ α β ν)
    {X : Type} [TopologicalSpace X] (p : (X → ℂ) → GL (Fin (a + a')) k → ℂ)
    (hadd : ∀ Φ ∈ SB X, ∀ Φ₁ ∈ SB X, ∀ c : ℂ, p (Φ + c • Φ₁) = p Φ + c • p Φ₁) (hmem : ∀ Φ ∈ SB X, p Φ ∈ indSp a a' α β)
    (heq : ∀ Φ ∈ SB X, ∀ h₁, ∃ Φ' ∈ SB X, p Φ' = rtr h₁ (p Φ)) (hne : ∃ Φ ∈ SB X, p Φ ≠ 0) :
    ∀ F ∈ indSp a a' α β, ∃ Φ ∈ SB X, p Φ = F := by
  have h0 : p 0 = 0 := by
    have := hadd 0 (zero_mem _) 0 (zero_mem _) 1
    simpa using this
  let N : Submodule ℂ (GL (Fin (a + a')) k → ℂ) :=
    { carrier := {F | ∃ Φ ∈ SB X, p Φ = F}
      add_mem' := by
        rintro _ _ ⟨Φ, hΦ, rfl⟩ ⟨Φ₁, hΦ₁, rfl⟩
        exact ⟨Φ + Φ₁, add_mem hΦ hΦ₁, by simpa using hadd Φ hΦ Φ₁ hΦ₁ 1⟩
      zero_mem' := ⟨0, zero_mem _, h0⟩
      smul_mem' := by
        rintro c _ ⟨Φ, hΦ, rfl⟩
        exact ⟨c • Φ, (SB X).smul_mem c hΦ, by simpa [h0] using hadd 0 (zero_mem _) Φ hΦ c⟩ }
  rcases irred_of_setting hI H N (by rintro _ ⟨Φ, hΦ, rfl⟩; exact hmem Φ hΦ)
    (by rintro h₁ _ ⟨Φ, hΦ, rfl⟩; exact heq Φ hΦ h₁) with h | h
  · obtain ⟨Φ, hΦ, hne⟩ := hne
    exact absurd ((Submodule.eq_bot_iff N).1 h _ ⟨Φ, hΦ, rfl⟩) hne
  · intro F hF
    rw [← h] at hF
    exact hF

end Local

section Ram

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [local instance 10000] GlobalTheory.SplitWeil.matrixMeasurableSpace

theorem ramMaps_of (hI : IndIrredNarrow) : RamMaps := by
  intro k _ _ _ _ _ _ a a' ϖ α β ν H hν
  exact ⟨fun _ h _ h₁ c => pRam_add H hν h h₁ c, fun _ h _ h₁ c => pRam'_add H h h₁ c, fun _ h => pRam_mem H hν h,
    fun _ h => pRam'_mem H h, fun _ h g => pRam_inv H hν h g, fun Ψ _ g => pRam'_inv Ψ g, fun Φ _ h => pRam_equiv Φ h,
    fun Ψ _ h => pRam'_equiv Ψ h,
    onto_of_irred hI H _ (fun _ h _ h₁ c => pRam_add H hν h h₁ c) (fun _ h => pRam_mem H hν h)
      (fun Φ h h₁ => ⟨_, omA_mem_SB ν β 1 h₁ h, pRam_equiv Φ h₁⟩) (pRam_ne_zero H),
    onto_of_irred hI H _ (fun _ h _ h₁ c => pRam'_add H h h₁ c) (fun _ h => pRam'_mem H h)
      (fun Ψ h h₁ => ⟨_, omB_mem_SB ν α 1 h₁ h, pRam'_equiv Ψ h₁⟩) (pRam'_ne_zero H)⟩

end Ram

section Fin

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.KCo PositivityTheory.ThK

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] PositivityTheory.ThK.SplitAsm.measFv PositivityTheory.ThK.SplitAsm.borelFv

theorem finRam_of (hR : RamMaps) (hRN : RamNonzero) (hI : IndIrredNarrow) (hD : Dict) (hAU : ActsUniq) (hC : ChrFacts) :
    FinRam := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv
  have hP : v ∈ B.P := hT.chars.sub hv
  obtain ⟨hα, hβ, hν, hcond, hram, -⟩ := hC F E B X a a' v (B.τ ⟨v, hP⟩) hT.chars
  have hS : HidaSetting a a' (unifAt v) (chrW X.α (B.τ ⟨v, hP⟩)) (chrW X.β (B.τ ⟨v, hP⟩)) (chrW X.ν (B.τ ⟨v, hP⟩)) :=
    ⟨GlobalTheory.SplitFlip.exists_isUnif.choose_spec, hα, hβ, hν, hT.geo.lt, hT.geo.even, hcond⟩
  obtain ⟨hlin, hlin', hmem, hmem', hinv, hinv', heq, heq', hon, hon'⟩ := hR (Fv F v) a a' _ _ _ _ hS (hram hv)
  obtain ⟨Φ0, hΦ0, hnz⟩ := hRN (Fv F v) a a' _ _ _ _ hS (hram hv)
  obtain ⟨b, b', c, ι, ι', gl, gl', hl, hW, hB, hbas, hvac, hvac', hRg, hRh, hRg', hRh', hhl⟩ :=
    hD F E σ B a a' G X om om' hT v (B.τ ⟨v, hP⟩)
  obtain ⟨rfl, rfl, rfl⟩ := hbas hP rfl
  obtain ⟨p, p', hp, hp', hon1, hon1', hinv1, hinv1', heq1, hnt, hirr1⟩ := core hAU v G om om' _ _ _ (indSp a a' _ _)
    (pRam a a' (unifAt v) (chrW X.ν (B.τ ⟨v, hP⟩)) (chrW X.β (B.τ ⟨v, hP⟩)))
    (pRam' a a' (chrW X.ν (B.τ ⟨v, hP⟩)) (chrW X.α (B.τ ⟨v, hP⟩)))
    (fun Φ h Φ₁ h₁ => hlin Φ h Φ₁ h₁) (fun Φ h Φ₁ h₁ => hlin' Φ h Φ₁ h₁)
    (fun Φ h => hmem Φ h) (fun Φ h => hmem' Φ h) (fun Φ h => hinv Φ h)
    (fun Φ h => hinv' Φ h) (fun Φ h => heq Φ h) (fun Φ h => heq' Φ h)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon y hy; exact ⟨Φ, h, r⟩)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon' y hy; exact ⟨Φ, h, r⟩) ⟨Φ0, hΦ0, hnz⟩
    (fun N hN hst => irred_of_setting hI hS N hN hst) ι ι' hW.bij hB.bij gl gl' hl hRg hRh hRg' hRh' hhl
  refine ⟨oneMaps v _ p p', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [oneMaps_p]; exact hon1
  · rw [oneMaps_p']; exact hon1'
  · rw [oneMaps_p]; exact hinv1
  · rw [oneMaps_p']; exact hinv1'
  · rw [oneMaps_p, oneMaps_p']; exact heq1
  · exact hnt
  · rw [oneMaps_p]; exact hirr1
  · intro hv'; exact absurd hv hv'
  · intro hv' _
    refine ⟨ι, ι', hW, hB, hvac, hvac', fun φ hφ φ' hφ' => ?_⟩
    rw [oneMaps_p, oneMaps_p']
    refine ⟨fun h => ?_, fun h => Subtype.ext ?_⟩
    · have := congrArg Subtype.val h
      erw [hp φ hφ, hp' φ' hφ'] at this
      exact this
    · erw [hp φ hφ, hp' φ' hφ']
      exact h

end Fin

theorem finRam_of_narrow :
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
      (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
      (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible) → PositivityTheory.ThK.FinRam :=
  fun NB => finRam_of (ramMaps_of (indIrredNarrow_of NB)) ramified_map_ne_zero (indIrredNarrow_of NB) split_place_dictionary
    PositivityTheory.KCo.action_uniqueness split_character_facts

end GlobalTheory.CompanionTheory.SplitNarrow
