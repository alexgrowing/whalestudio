import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPrincipalSeriesNonzeroAtOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesZeroOfCoordinateZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesCoordinateLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesCoordinateNearInfinityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPrincipalSeriesNoInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationDilationStableRadialElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RadialElementDifferenceExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferenceSpanLeStableSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateDifferenceMemSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DilationDifferenceMemSpanStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PrinTwo

namespace GlobalTheory.PrinTwo.Irr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unram_congr {μ : kˣ →* ℂˣ} (h : IsUnram μ) {a b : kˣ}
    (hab : valuation k (a : k) = valuation k (b : k)) : μ a = μ b := by
  have hb : valuation k (b : k) ≠ 0 := (Valuation.ne_zero_iff _).2 b.ne_zero
  have hu : valuation k ((a * b⁻¹ : kˣ) : k) = 1 := by
    rw [Units.val_mul, map_mul, hab, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀ hb]
  have := h _ hu
  rw [map_mul, map_inv, mul_inv_eq_one] at this
  exact this

theorem bchar_congr {μ₁ μ₂ : kˣ →* ℂˣ} (h₁ : IsUnram μ₁) (h₂ : IsUnram μ₂) {a d a' d' : kˣ}
    (ha : valuation k (a : k) = valuation k (a' : k)) (hd : valuation k (d : k) = valuation k (d' : k)) :
    bchar μ₁ μ₂ a d = bchar μ₁ μ₂ a' d' := by
  simp only [bchar]
  rw [unram_congr h₁ ha, unram_congr h₂ hd, unram_congr (isUnram_absPow k (1 / 2)) ha,
    unram_congr (isUnram_absPow k (-1 / 2)) hd]

theorem ne_zero_of_lt {R : kˣ} {x : k} (hx : valuation k (R : k) < valuation k x) : x ≠ 0 := by
  rintro rfl; rw [map_zero] at hx; exact not_lt_zero' hx

theorem isEvRad_coord (hasy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ, ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) → GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1) {μ₁ μ₂ : kˣ →* ℂˣ} (h₁ : IsUnram μ₁) (h₂ : IsUnram μ₂)
    (f : PSp μ₁ μ₂) : IsEvRad (coord f) := by
  obtain ⟨R, hR⟩ := hasy k μ₁ μ₂ f
  refine ⟨R, fun x y hx hxy => ?_⟩
  have hx0 := ne_zero_of_lt hx
  have hy : valuation k (R : k) < valuation k y := hxy ▸ hx
  have hy0 := ne_zero_of_lt hy
  have ex := hR (Units.mk0 x hx0) hx
  have ey := hR (Units.mk0 y hy0) hy
  simp only [Units.val_mk0] at ex ey
  rw [ex, ey, bchar_congr h₁ h₂ (a' := -(Units.mk0 y hy0)⁻¹) (d' := Units.mk0 y hy0)]
  · simp [Valuation.map_neg, map_inv₀, hxy]
  · simpa using hxy

theorem isCS_coord (hasy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ, ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) → GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1) {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (hf : ev f 1 = 0) :
    IsCS (coord f) := by
  obtain ⟨R, hR⟩ := hasy k μ₁ μ₂ f
  refine ⟨R, fun x hx => ?_⟩
  have := hR (Units.mk0 x (ne_zero_of_lt hx)) hx
  simpa [hf] using this

theorem eta_eq (μ₁ μ₂ : kˣ →* ℂˣ) (a : kˣ) :
    bchar μ₁ μ₂ a⁻¹ a * ((absPow k 1 (a⁻¹ * a⁻¹) : ℂˣ) : ℂ)⁻¹ = (((μ₂ * absPow k 1) a / μ₁ a : ℂˣ) : ℂ) := by
  have h1 : absPow k 1 = absPow k (1 / 2) * absPow k (1 / 2) := by rw [← absPow_add]; norm_num
  have h2 : absPow k (-1 / 2) = (absPow k (1 / 2))⁻¹ := by rw [neg_div, absPow_neg]
  simp only [bchar, h1, h2, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]
  have e1 : ((μ₁ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have e2 : ((absPow k (1 / 2) a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

end GlobalTheory.PrinTwo.Irr

namespace GlobalTheory.PrinTwo.Irr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 4000000 in

theorem isIrreducible_of
    (hnt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ → ∃ f : GlobalTheory.PrinTwo.PSp μ₁ μ₂, GlobalTheory.PrinTwo.ev f 1 ≠ 0) (hinj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), GlobalTheory.PrinTwo.ev f 1 = 0 → (∀ x : k, GlobalTheory.PrinTwo.coord f x = 0) → f = 0) (hlc : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), GlobalTheory.PrinTwo.IsLC (GlobalTheory.PrinTwo.coord f)) (hasy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ, ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) → GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1) (hnf : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ → μ₂ ≠ μ₁ * GlobalTheory.SmGL.absPow k 1 → ∀ f : GlobalTheory.PrinTwo.PSp μ₁ μ₂, (∀ x : k, GlobalTheory.PrinTwo.psRep μ₁ μ₂ (GlobalTheory.PrinTwo.nU x) f = f) → f = 0)
    (hrad : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (W : Submodule ℂ (k → ℂ)), (∀ Φ ∈ W, ∀ y : k, (fun x => Φ (x + y)) ∈ W) → (∀ Φ ∈ W, ∀ a : kˣ, (fun x => Φ (a * x)) ∈ W) → ∀ Φ ∈ W, Φ ≠ 0 → GlobalTheory.PrinTwo.IsLC Φ → GlobalTheory.PrinTwo.IsCS Φ → ∃ R ∈ W, GlobalTheory.PrinTwo.IsLC R ∧ GlobalTheory.PrinTwo.IsCS R ∧ R 0 ≠ 0 ∧ ∀ (u : kˣ) (x : k), ValuativeRel.valuation k (u : k) = 1 → R (u * x) = R x) (hone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (W : Submodule ℂ (k → ℂ)), (∀ Φ ∈ W, ∀ y : k, (fun x => Φ (x + y)) ∈ W) → ∀ R ∈ W, GlobalTheory.PrinTwo.IsLC R → GlobalTheory.PrinTwo.IsCS R → R 0 ≠ 0 → (∀ (u : kˣ) (x : k), ValuativeRel.valuation k (u : k) = 1 → R (u * x) = R x) → ∃ (y : k) (r : kˣ) (c : ℂ), c ≠ 0 ∧ ValuativeRel.valuation k (r : k) < ValuativeRel.valuation k y ∧ c • GlobalTheory.PrinTwo.elemDiff 0 y r ∈ W) (hall : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (W : Submodule ℂ (k → ℂ)), (∀ Φ ∈ W, ∀ y : k, (fun x => Φ (x + y)) ∈ W) → (∀ Φ ∈ W, ∀ a : kˣ, (fun x => Φ (a * x)) ∈ W) → ∀ (y : k) (r : kˣ) (c : ℂ), c ≠ 0 → ValuativeRel.valuation k (r : k) < ValuativeRel.valuation k y → c • GlobalTheory.PrinTwo.elemDiff 0 y r ∈ W → GlobalTheory.PrinTwo.elemSpan k ≤ W) (hdiff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Φ : k → ℂ), GlobalTheory.PrinTwo.IsLC Φ → GlobalTheory.PrinTwo.IsEvRad Φ → ∀ y : k, (fun x => Φ (x + y) - Φ x) ∈ GlobalTheory.PrinTwo.elemSpan k) (hdil : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Φ : k → ℂ), GlobalTheory.PrinTwo.IsLC Φ → GlobalTheory.PrinTwo.IsCS Φ → ∀ a : kˣ, (fun x => Φ (a * x) - ((GlobalTheory.SmGL.absPow k 1 a : ℂˣ) : ℂ)⁻¹ * Φ x) ∈ GlobalTheory.PrinTwo.elemSpan k)
    {μ₁ μ₂ : kˣ →* ℂˣ} (h₁ : IsUnram μ₁) (h₂ : IsUnram μ₂) (hne₁ : μ₁ ≠ μ₂ * absPow k 1)
    (hne₂ : μ₂ ≠ μ₁ * absPow k 1) : (psRep μ₁ μ₂).IsIrreducible := by
  obtain ⟨f₀, hf₀⟩ := hnt k μ₁ μ₂ h₁ h₂
  have hev_nU : ∀ (ψ : PSp μ₁ μ₂) (y : k), ev (psRep μ₁ μ₂ (nU y) ψ) 1 = ev ψ 1 := fun ψ y => by
    rw [nU, ev_act_bor_one, bchar_one, one_mul]
  have key : ∀ U : Subrepresentation (psRep μ₁ μ₂), U ≠ ⊥ → U = ⊤ := by
    intro U hU
    have hU' : U.toSubmodule ≠ ⊥ := fun h => hU (Subrepresentation.toSubmodule_injective h)
    obtain ⟨f, hfU, hf0⟩ := (Submodule.ne_bot_iff _).1 hU'
    have hex : ∃ y, psRep μ₁ μ₂ (nU y) f ≠ f := by
      by_contra hc
      push_neg at hc
      exact hf0 (hnf k μ₁ μ₂ h₁ h₂ hne₂ f hc)
    obtain ⟨y, hy⟩ := hex
    obtain ⟨g, hg⟩ : ∃ g, g = psRep μ₁ μ₂ (nU y) f - f := ⟨_, rfl⟩
    have hgU : g ∈ U.toSubmodule := hg ▸ U.toSubmodule.sub_mem (U.apply_mem_toSubmodule _ hfU) hfU
    have hg0 : g ≠ 0 := hg ▸ sub_ne_zero.2 hy
    have hg1 : ev g 1 = 0 := by rw [hg, ev_sub, hev_nU, sub_self]
    obtain ⟨W, memW, memW'⟩ : ∃ W : Submodule ℂ (k → ℂ),
        (∀ h, h ∈ U.toSubmodule → ev h 1 = 0 → coord h ∈ W) ∧
        (∀ Φ ∈ W, ∃ h ∈ U.toSubmodule, ev h 1 = 0 ∧ coord h = Φ) := by
      refine ⟨(U.toSubmodule ⊓ LinearMap.ker (evL μ₁ μ₂ 1)).map (coordL μ₁ μ₂), fun h hU h1 =>
        Submodule.mem_map.2 ⟨h, ⟨hU, by simpa using h1⟩, rfl⟩, fun Φ hΦ => ?_⟩
      obtain ⟨h, ⟨hhU, hh1⟩, rfl⟩ := Submodule.mem_map.1 hΦ
      exact ⟨h, hhU, by simpa using hh1, rfl⟩
    have hWt : ∀ Φ ∈ W, ∀ y : k, (fun x => Φ (x + y)) ∈ W := by
      intro Φ hΦ y
      obtain ⟨h, hhU, hh1', rfl⟩ := memW' Φ hΦ
      have : (fun x => coord h (x + y)) = coord (psRep μ₁ μ₂ (nU y) h) :=
        funext fun x => (coord_nU h y x).symm
      rw [this]
      exact memW _ (U.apply_mem_toSubmodule _ hhU) (by rw [hev_nU, hh1'])
    have hWd : ∀ Φ ∈ W, ∀ a : kˣ, (fun x => Φ (a * x)) ∈ W := by
      intro Φ hΦ a
      obtain ⟨h, hhU, hh1', rfl⟩ := memW' Φ hΦ
      have : (fun x => coord h (a * x)) =
          (bchar μ₁ μ₂ 1 a⁻¹)⁻¹ • coord (psRep μ₁ μ₂ (tD a⁻¹ 1) h) := by
        funext x
        rw [Pi.smul_apply, coord_tD, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (bchar_ne_zero _ _ _ _),
          one_mul]
        congr 1
        simp [mul_comm]
      rw [this]
      refine W.smul_mem _ (memW _ (U.apply_mem_toSubmodule _ hhU) ?_)
      rw [tD, ev_act_bor_one, hh1', mul_zero]
    have hΦ₀ : coord g ∈ W := memW g hgU hg1
    have hcg : coord g ≠ 0 := fun h => hg0 (hinj k μ₁ μ₂ g hg1 (fun x => congrFun h x))
    obtain ⟨R, hRW, hRlc, hRcs, hR0, hRrad⟩ :=
      hrad k W hWt hWd _ hΦ₀ hcg (hlc k μ₁ μ₂ g) (isCS_coord hasy g hg1)
    have hone' : ∃ (y : k) (r : kˣ) (c : ℂ), c ≠ 0 ∧ valuation k (r : k) < valuation k y ∧ c • elemDiff 0 y r ∈ W :=
      hone k W hWt R hRW hRlc hRcs hR0 hRrad
    obtain ⟨y₀, r₀, c₀, hc₀, hr₀, hmem⟩ := hone'
    have hspan : elemSpan k ≤ W := hall k W hWt hWd y₀ r₀ c₀ hc₀ hr₀ hmem
    have hK : ∀ h : PSp μ₁ μ₂, ev h 1 = 0 → coord h ∈ elemSpan k → h ∈ U.toSubmodule := by
      intro h h1 hs
      have hs' : coord h ∈ W := hspan hs
      obtain ⟨h', h'U, h'1', hh'⟩ := memW' (coord h) hs'
      have hd : h - h' = 0 := hinj k μ₁ μ₂ _ (by rw [ev_sub, h1, h'1', sub_self]) (fun x => by
        have := congrFun hh' x
        rw [coord, ev_sub, ← coord, ← coord, this, sub_self])
      rw [sub_eq_zero.1 hd]
      exact h'U
    have hN : ∀ (y : k) (ψ : PSp μ₁ μ₂), psRep μ₁ μ₂ (nU y) ψ - ψ ∈ U.toSubmodule := by
      intro y ψ
      refine hK _ (by rw [ev_sub, hev_nU, sub_self]) ?_
      have : coord (psRep μ₁ μ₂ (nU y) ψ - ψ) = fun x => coord ψ (x + y) - coord ψ x := funext fun x => by
        rw [coord, ev_sub, ← coord, ← coord, coord_nU]
      rw [this]
      exact hdiff k _ (hlc k μ₁ μ₂ ψ) (isEvRad_coord hasy h₁ h₂ ψ) y
    have hwE : ∀ ψ : PSp μ₁ μ₂, psRep μ₁ μ₂ wE (psRep μ₁ μ₂ wE ψ) = ψ := fun ψ => by
      rw [← Module.End.mul_apply, ← map_mul, wE_mul_wE, map_one, Module.End.one_apply]
    have hNL : ∀ (y : k) (ψ : PSp μ₁ μ₂), psRep μ₁ μ₂ (nL y) ψ - ψ ∈ U.toSubmodule := by
      intro y ψ
      have e : psRep μ₁ μ₂ (nL y) ψ = psRep μ₁ μ₂ wE (psRep μ₁ μ₂ (nU y) (psRep μ₁ μ₂ wE ψ)) :=
        ext_ev fun x => by simp only [ev_act, nL_eq, mul_assoc]
      have h3 := U.apply_mem_toSubmodule wE (hN y (psRep μ₁ μ₂ wE ψ))
      have h4 : psRep μ₁ μ₂ wE (psRep μ₁ μ₂ (nU y) (psRep μ₁ μ₂ wE ψ) - psRep μ₁ μ₂ wE ψ) =
          psRep μ₁ μ₂ (nL y) ψ - ψ :=
        (LinearMap.map_sub (psRep μ₁ μ₂ wE) _ _).trans (congrArg₂ HSub.hSub e.symm (hwE ψ))
      exact (congrArg (· ∈ U.toSubmodule) h4).mp h3
    have hmul : ∀ g₁ g₂ : GL (Fin (1 + 1)) k, (∀ ψ : PSp μ₁ μ₂, psRep μ₁ μ₂ g₁ ψ - ψ ∈ U.toSubmodule) →
        (∀ ψ : PSp μ₁ μ₂, psRep μ₁ μ₂ g₂ ψ - ψ ∈ U.toSubmodule) → ∀ ψ : PSp μ₁ μ₂, psRep μ₁ μ₂ (g₁ * g₂) ψ - ψ ∈ U.toSubmodule := by
      intro g₁ g₂ h1 h2 ψ
      have : psRep μ₁ μ₂ (g₁ * g₂) ψ - ψ =
          (psRep μ₁ μ₂ g₁ (psRep μ₁ μ₂ g₂ ψ) - psRep μ₁ μ₂ g₂ ψ) + (psRep μ₁ μ₂ g₂ ψ - ψ) := by
        have e : psRep μ₁ μ₂ (g₁ * g₂) ψ = psRep μ₁ μ₂ g₁ (psRep μ₁ μ₂ g₂ ψ) :=
          ext_ev fun x => by simp only [ev_act, mul_assoc]
        exact (congrArg (· - ψ) e).trans (by abel)
      rw [this]
      exact U.toSubmodule.add_mem (h1 _) (h2 _)
    have hT : ∀ (a : kˣ) (ψ : PSp μ₁ μ₂), psRep μ₁ μ₂ (tD a a⁻¹) ψ - ψ ∈ U.toSubmodule := by
      intro a
      rw [tD_inv_eq]
      exact hmul _ _ (hmul _ _ (hmul _ _ (hN _) (hNL _)) (hN _)) (hmul _ _ (hmul _ _ (hN _) (hNL _)) (hN _))
    have hV₀ : ∀ φ : PSp μ₁ μ₂, ev φ 1 = 0 → φ ∈ U.toSubmodule := by
      intro φ hφ
      by_contra hφU
      apply hne₁
      refine MonoidHom.ext fun a => ?_
      obtain ⟨η, hη⟩ : ∃ η : ℂ, η = bchar μ₁ μ₂ a⁻¹ a * ((absPow k 1 (a⁻¹ * a⁻¹) : ℂˣ) : ℂ)⁻¹ := ⟨_, rfl⟩
      have h2 : psRep μ₁ μ₂ (tD a a⁻¹) φ - η • φ ∈ U.toSubmodule := by
        refine hK _ (by rw [ev_sub, ev_smul, tD, ev_act_bor_one, hφ, mul_zero, mul_zero, sub_self]) ?_
        have : coord (psRep μ₁ μ₂ (tD a a⁻¹) φ - η • φ) = bchar μ₁ μ₂ a⁻¹ a •
            fun x => coord φ (((a⁻¹ * a⁻¹ : kˣ) : k) * x) -
              ((absPow k 1 (a⁻¹ * a⁻¹) : ℂˣ) : ℂ)⁻¹ * coord φ x := funext fun x => by
          rw [coord, ev_sub, ev_smul, ← coord, ← coord, coord_tD, Pi.smul_apply, smul_eq_mul, hη]
          rw [mul_sub, ← mul_assoc]
          congr 2
          push_cast
          ring
        rw [this]
        exact (elemSpan k).smul_mem _ (hdil k _ (hlc k μ₁ μ₂ φ) (isCS_coord hasy φ hφ) _)
      have h3 : (η - 1) • φ ∈ U.toSubmodule := by
        have := U.toSubmodule.sub_mem (hT a φ) h2
        have e3 : psRep μ₁ μ₂ (tD a a⁻¹) φ - φ - (psRep μ₁ μ₂ (tD a a⁻¹) φ - η • φ) = (η - 1) • φ := by
          rw [sub_smul, one_smul]; abel
        exact (congrArg (· ∈ U.toSubmodule) e3).mp this
      have h4 : η = 1 := by
        by_contra hne
        apply hφU
        have := U.toSubmodule.smul_mem (η - 1)⁻¹ h3
        rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul] at this
      rw [hη, eta_eq] at h4
      have h5 : ((μ₂ * absPow k 1) a / μ₁ a : ℂˣ) = 1 := Units.ext h4
      exact (div_eq_one.1 h5).symm
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hcg
    obtain ⟨h, hh⟩ : ∃ h, h = psRep μ₁ μ₂ wE (psRep μ₁ μ₂ (nU x) g) := ⟨_, rfl⟩
    have hhU : h ∈ U.toSubmodule := hh ▸ U.apply_mem_toSubmodule _ (U.apply_mem_toSubmodule _ hgU)
    have hh1 : ev h 1 ≠ 0 := by
      rw [hh, ev_act, ev_act, one_mul]
      exact hx
    apply Subrepresentation.toSubmodule_injective
    refine eq_top_iff.2 fun ψ _ => ?_
    have hψ : ψ - (ev ψ 1 / ev h 1) • h ∈ U.toSubmodule :=
      hV₀ _ (by rw [ev_sub, ev_smul, div_mul_cancel₀ _ hh1, sub_self])
    have := U.toSubmodule.add_mem hψ (U.toSubmodule.smul_mem (ev ψ 1 / ev h 1) hhU)
    rwa [sub_add_cancel] at this
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hf₀ ?_⟩, eq_bot_or_eq_top := fun U => or_iff_not_imp_left.2 (key U) }
  have hm : f₀ ∈ (⊤ : Subrepresentation (psRep μ₁ μ₂)).toSubmodule := Submodule.mem_top
  rw [← h] at hm
  have h0 : f₀ = 0 := (Submodule.mem_bot ℂ).1 hm
  rw [h0]
  exact map_zero (evL μ₁ μ₂ 1)

end GlobalTheory.PrinTwo.Irr

theorem GlobalTheory.PrinTwo.Irr.isIrreducible_prod₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (μ₁ μ₂ : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ →
    μ₁ ≠ μ₂ * GlobalTheory.SmGL.absPow k 1 → μ₂ ≠ μ₁ * GlobalTheory.SmGL.absPow k 1 →
    (GlobalTheory.SmGL.prod₂ (GlobalTheory.SmGL.detRep (Fin 1) μ₁) (GlobalTheory.SmGL.detRep (Fin 1) μ₂)).IsIrreducible :=
  fun k _ _ _ _ μ₁ μ₂ h₁ h₂ hne₁ hne₂ => GlobalTheory.PrinTwo.Irr.isIrreducible_of GlobalTheory.T.unramified_principal_series_nonzero_at_one GlobalTheory.T.principal_series_zero_of_coordinate_zero GlobalTheory.T.principal_series_coordinate_locally_constant
    GlobalTheory.T.principal_series_coordinate_near_infinity GlobalTheory.T.unramified_principal_series_no_invariant GlobalTheory.T.translation_dilation_stable_radial_element GlobalTheory.T.radial_element_difference_exists GlobalTheory.T.difference_span_le_stable_subspace GlobalTheory.T.translate_difference_mem_span GlobalTheory.T.dilation_difference_mem_span h₁ h₂ hne₁ hne₂
