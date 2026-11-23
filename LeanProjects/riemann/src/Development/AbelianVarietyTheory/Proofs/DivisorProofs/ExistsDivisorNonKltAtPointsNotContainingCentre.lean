import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSupp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffQCartierNumEquivMultipleNonnegSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSectionAngehrnSiuInductiveStepStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CartierLocalEquationCommon

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem qNum_principal_add_nsmul {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) {N : LB X} (hN : IsAmpleLB N) {A : CartierDiv X} (e : toPic A = cls N hN.isLB)
    (l : ℕ) {g : X.functionFieldˣ} (hg : (g : X.functionField) ∈ (l • A).sections) :
    QNum p N l (qWeil (CartierDiv.principal g + l • A) 1) := by
  letI := algebraΓOfHom p
  refine ⟨1, CartierDiv.principal g + l • A, one_pos, CartierDiv.mem_sections_iff_eff.1 hg, rfl, ?_⟩
  intro C hC
  have e1 : toPic (CartierDiv.principal g + l • A) = l • cls N hN.isLB := by
    rw [map_add, map_nsmul, toPic_principal, e, zero_add]
  have e2 : cls (toLB (CartierDiv.principal g + l • A)) (isLB_toLB _) =
      cls (lbPow N l) (isLB_lbPow hN.isLB l) := by
    rw [← toPic_apply, e1, GlobalTheory.CechPic.cls_lbPow hN.isLB]
  rw [interNumRed_one_congr _ _ e2 C, hC.interNumRed_lbPow hN hN.isLB l]
  push_cast
  ring

theorem exists_step_divisor : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsQCart D → (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k → topologicalKrullDim (closure ({z} : Set X)) = k → (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h → (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => N : ℤ) → ∃ (B : X → ℚ) (δ₀ : ℚ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧ QNum p N h B ∧ Off B z ∧ (∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P, ¬ KltAt p n (Δ + (1 - δ) • D + B) x) ∧ (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) := by
  intro hPr _ _ X _ _ _ p n hproj hdim Δ m G N D P z k h hΔ hklt hm hG hN hD hP hk hZ hz hh hnum
  letI := algebraΓOfHom p
  obtain ⟨A, hA⟩ := toPic_surjective (X := X) (cls N hN.isLB)
  have hAN : cls (toLB A) (isLB_toLB A) = cls N hN.isLB := by rw [← toPic_apply, hA]
  have hAamp : IsAmpleLB (toLB A) :=
    (isAmpleLB_congr (isLB_toLB A) hN.isLB ((GlobalTheory.CechPic.cls_eq_iff _ _).1 hAN)).2 hN
  have hcongr : (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A) =
      interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => N := by
    rw [interNumRed_def, interNumRed_def, interNumSub_def, interNumSub_def, interNumOn_def,
      interNumOn_def]
    exact interNum_congr_cls (k := ℂ) (F := _) (fun _ => isLB_toLB A) (fun _ => hN.isLB)
      fun _ => hAN
  have hnumA : (P.card : ℚ) * (k : ℚ) ^ k <
      h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) := by
    rw [hcongr]; exact hnum
  obtain ⟨l₁, hl₁⟩ :=
    GlobalTheory.GeneralLift.exists_lift_klt hPr X p n hproj hdim Δ D m G A z hm hG hD hAamp
  obtain ⟨l, hll, hl, f₀, hf₀, hgen, δ₀, hδ0, hδ1, hmain⟩ :=
    GlobalTheory.T.exists_global_section_angehrnSiu_inductive_step hPr X p n hproj hdim Δ m G A D P z k h hΔ hklt hm hG hAamp hD hP hk hZ hz hh
      hnumA l₁
  obtain ⟨u, hu, hvan, hoff⟩ := hl₁ l hll f₀ hf₀
  have hgen' : (l • A).GeneratesAt z (f₀ + u) :=
    GlobalTheory.Cartier.CommonEqn.generatesAt_add hgen hvan
  set g : X.functionFieldˣ := Units.mk0 (f₀ + u) hgen'.ne_zero with hg_def
  have hgval : (g : X.functionField) = f₀ + u := rfl
  have hgmem : (g : X.functionField) ∈ (l • A).sections := by
    rw [hgval]; exact add_mem hf₀ hu
  have hlpos : (0 : ℚ) < l := lt_trans hh hl
  have hEff : (CartierDiv.principal g + l • A).Eff := CartierDiv.mem_sections_iff_eff.1 hgmem
  have hzs : z ∉ (CartierDiv.principal g + l • A).supp := by
    rw [CartierDiv.notMem_supp_iff]
    have h1 : (CartierDiv.principal g).GeneratesAt z (g : X.functionField)⁻¹ :=
      CartierDiv.isEqn_iff_generatesAt_inv.1 (CartierDiv.isEqn_principal g z)
    have h2 : (l • A).GeneratesAt z (g : X.functionField) := by rw [hgval]; exact hgen'
    have h3 := h1.mul h2
    rwa [inv_mul_cancel₀ (Units.ne_zero g)] at h3
  refine ⟨(h / l) • qWeil (CartierDiv.principal g + l • A) 1, δ₀, hδ0, hδ1, ?_, ?_, ?_, ?_⟩
  · have h1 := qNum_principal_add_nsmul p hN hA l hgmem
    have h2 := qNum_smul X p hproj N (l : ℚ) (h / l) _ (div_nonneg hh.le hlpos.le) h1
    rwa [div_mul_cancel₀ h hlpos.ne'] at h2
  · intro w hw
    have h0 := (off_qWeil_iff_notMem_supp X (CartierDiv.principal g + l • A) 1 z hEff one_pos).2 hzs
    rw [Pi.smul_apply, h0 w hw, smul_zero]
  · intro δ h0 h1 x hx
    exact hmain u hu hvan g hgval δ h0 h1 x hx
  · intro y hy a ha hka
    exact hoff g hgval y hy a (h / l) ha ((div_lt_one hlpos).2 hl) hka

end GlobalTheory.PairStep
