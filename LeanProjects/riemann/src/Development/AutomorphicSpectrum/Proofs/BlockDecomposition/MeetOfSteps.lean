import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspFormStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.ClosedInvariantMeet

theorem exists_space (hG2a : G2a) (hG2b : G2b) (hG2c : G2c) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
    {a : ℕ} (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ)
    (S : Finset (Pl E)) (B : Pl E → Multiset ℂˣ) (hB : ∀ w, w ∉ S → (B w).card = a)
    (H : Submodule ℂ (L2 (latticeGL E a) μ)) (hH : IsSubrep (R (latticeGL E a) μ) H) :
    ∃ Y : Submodule ℂ (XB E a), YOK ψ S Y ∧ ∀ φ : XB E a, φ ∈ Y ↔
      (Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g) ∧
        (∃ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ H) ∧ ∀ w, w ∉ S → SatFn w (B w) φ := by
  obtain ⟨Y0, c0, s0, m0⟩ := hG2a E a ψ hψ
  obtain ⟨YH, cH, sH, mH⟩ := hG2b E a μ H hH
  have hw := fun w (hw : w ∉ S) => hG2c E a w (B w) (hB w hw)
  choose! Yw cw sw mw using hw
  have mem : ∀ φ : XB E a, φ ∈ Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w ↔
      (φ ∈ Y0 ∧ φ ∈ YH) ∧ ∀ w, w ∉ S → φ ∈ Yw w := fun φ => by
    simp only [Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w, ⟨?_, ?_, ?_⟩, fun φ => ?_⟩
  · have e : ((Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w : Submodule ℂ (XB E a)) : Set (XB E a)) =
        ((Y0 : Set (XB E a)) ∩ YH) ∩ ⋂ w, ⋂ (_ : w ∉ S), (Yw w : Set (XB E a)) := by
      ext φ
      simp only [SetLike.mem_coe, mem, Set.mem_inter_iff, Set.mem_iInter]
    rw [e]
    exact (c0.inter cH).inter (isClosed_iInter fun w => isClosed_iInter fun h => cw w h)
  · intro g hg φ hφ
    obtain ⟨⟨h0, h1⟩, h2⟩ := (mem φ).1 hφ
    exact (mem _).2 ⟨⟨s0 g φ h0, sH g φ h1⟩, fun w h => sw w h g (hg w h) φ (h2 w h)⟩
  · intro φ hφ
    exact ((m0 φ).1 ((mem φ).1 hφ).1.1).1
  · rw [mem, m0, mH]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨h0, h1, fun w h => (mw w h φ).1 (h2 w h)⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨h0, h1⟩, fun w h => (mw w h φ).2 (h2 w h)⟩

theorem eq_of_wh (hG5 : G5) (hG13 : WhittakerVanishingImpliesZero) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (S : Finset (Pl E)) (hc : ∀ w, w ∉ S → Cond ψ w) (B : Pl E → Multiset ℂˣ)
    (hYs : ∀ w, w ∉ S → ∃ Z : Submodule ℂ (XB E a), ∀ φ, φ ∈ Z ↔ SatFn w (B w) φ)
    (hY0 : ∃ Z : Submodule ℂ (XB E a), ∀ φ : XB E a, φ ∈ Z ↔ Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g)
    {φ φ' : XB E a} (h : (Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g) ∧ ∀ w, w ∉ S → SatFn w (B w) φ)
    (h' : (Good ψ (a - 1) φ' ∧ ∀ γ g, φ' (ratGL E a γ * g) = φ' g) ∧ ∀ w, w ∉ S → SatFn w (B w) φ')
    (hW : ∀ g, MirS S g → InS S g → Wh ψ φ g = Wh ψ φ' g) : φ = φ' := by
  obtain ⟨Z, hZ⟩ := hY0
  have d0 : φ - φ' ∈ Z := Z.sub_mem ((hZ φ).2 h.1) ((hZ φ').2 h'.1)
  have hd := (hZ _).1 d0
  have e := hG13 E a ψ hψ S hc (φ - φ') hd.1 hd.2
    (fun w hw => ⟨B w, by
      obtain ⟨Z', hZ'⟩ := hYs w hw
      exact (hZ' _).1 (Z'.sub_mem ((hZ' φ).2 (h.2 w hw)) ((hZ' φ').2 (h'.2 w hw)))⟩)
    (fun g h1 h2 => by
      obtain ⟨Λ, hΛ⟩ := (hG5 E a ψ hψ).1 g
      rw [← hΛ _ hd.1, map_sub, hΛ _ h.1.1, hΛ _ h'.1.1, hW g h1 h2, sub_self])
  exact sub_eq_zero.1 e

theorem meet_of_steps : S2 → MirabolicColumnBlock → G0 → G1 → AlmostEverywhereSpherical → G2a → G2b → G2c → G5 → G5b → FourierInductionSteps → G8 → StandardCharacterExists → WhittakerVanishingImpliesZero → Meet := by
  intro _ hS10 hG0 hG1 hG1b hG2a hG2b hG2c hG5 _ hG7i hG8 hG10 hG13 E _ _ _ a μ _ _ π π' H H' hn hn' hH hH' hm hm' hss
  obtain ⟨ψ, hψ, hcond⟩ := hG10 E
  obtain ⟨φ0, hφ0, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨φ0', hφ0', h0'⟩ := (Submodule.ne_bot_iff _).1 π'.ne_bot
  obtain ⟨x, hx, hxs, hxl⟩ := hG1 E a π hn φ0 hφ0
  obtain ⟨x', hx', hxs', hxl'⟩ := hG1 E a π' hn' φ0' hφ0'
  have hev := hcond.and (hss.and ((hG1b E a π hn φ0 hφ0 x hx).and (hG1b E a π' hn' φ0' hφ0' x' hx')))
  obtain ⟨S, hS⟩ : ∃ S : Finset (Pl E), ∀ w, w ∉ S → Cond ψ w ∧
      (∃ B, (CG.mk π).HasSat w B ∧ (CG.mk π').HasSat w B) ∧
      (∀ B, (CG.mk π).HasSat w B → SatFn w B x) ∧ (∀ B, (CG.mk π').HasSat w B → SatFn w B x') :=
    ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun w hw => by
      by_contra h
      exact hw ((Set.Finite.mem_toFinset _).2 h)⟩
  have hBex := fun w (hw : w ∉ S) => (hS w hw).2.1
  choose! B hB using hBex
  have hcard : ∀ w, w ∉ S → (B w).card = a := fun w hw => CG.HasSat.card (hB w hw).1
  have hc : ∀ w, w ∉ S → Cond ψ w := fun w hw => (hS w hw).1
  obtain ⟨Y, hYok, hY⟩ := exists_space hG2a hG2b hG2c μ hψ S B hcard H hH
  obtain ⟨Y', hYok', hY'⟩ := exists_space hG2a hG2b hG2c μ hψ S B hcard H' hH'

  have hxY : x ∈ Y := by
    refine (hY x).2 ⟨⟨?_, ?_⟩, ?_, fun w hw => (hS w hw).2.2.1 _ (hB w hw).1⟩
    · rw [hx]; exact _root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ0 (π.cusp _ hφ0)
    · rw [hx]; exact (π.cusp _ hφ0).1.left
    · rw [hx]; exact hm φ0 hφ0
  have hxY' : x' ∈ Y' := by
    refine (hY' x').2 ⟨⟨?_, ?_⟩, ?_, fun w hw => (hS w hw).2.2.2 _ (hB w hw).2⟩
    · rw [hx']; exact _root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ0' (π'.cusp _ hφ0')
    · rw [hx']; exact (π'.cusp _ hφ0').1.left
    · rw [hx']; exact hm' φ0' hφ0'
  have hx0 : x ≠ 0 := fun e => h0 (Subtype.ext (by rw [← hx, e]; rfl))
  have hx0' : x' ≠ 0 := fun e => h0' (Subtype.ext (by rw [← hx', e]; rfl))
  obtain ⟨φ₁, hφ₁, hs₁, hl₁, hw₁⟩ := hG8 E a ψ hψ S hc Y hYok x hxY hx0 hxs (hxl S)
    fun w hw => ⟨B w, ((hY x).1 hxY).2.2 w hw⟩
  obtain ⟨φ₂, hφ₂, hs₂, hl₂, hw₂⟩ := hG8 E a ψ hψ S hc Y' hYok' x' hxY' hx0' hxs' (hxl' S)
    fun w hw => ⟨B w, ((hY' x').1 hxY').2.2 w hw⟩
  have hst : St ψ S Y Y' 0 (fun _ => 0) := by
    refine ⟨φ₁, hφ₁, φ₂, hφ₂, hs₁, hs₂, hl₁, hl₂, by rw [hw₁]; exact one_ne_zero, fun g hg => ?_⟩
    have e : g = 1 := by
      obtain ⟨-, -, -, -, -, hext, -⟩ := hG0 E a
      refine hext g 1 ?_ fun w => ?_
      · rw [map_one]; exact (hS10 _ a 0).2.1 _ hg.1
      · rw [map_one]; exact (hS10 _ a 0).2.1 _ (hg.2 w)
    rw [e, hw₁, hw₂]
  obtain ⟨φ, hφ, φ', hφ', -, -, -, -, hw, hag⟩ := hG7i E a ψ hψ S Y Y' hYok hYok' hst
  have hφm := (hY φ).1 hφ
  have hφm' := (hY' φ').1 hφ'
  obtain ⟨Z, -, -, hZ⟩ := hG2a E a ψ hψ
  have heq : φ = φ' := by
    refine eq_of_wh hG5 hG13 hψ S hc B (fun w hw => ?_) ⟨Z, hZ⟩ ⟨hφm.1, hφm.2.2⟩
      ⟨hφm'.1, hφm'.2.2⟩ fun g hg hi => hag g ⟨hg.1, fun w => ?_⟩
    · obtain ⟨Z', -, -, hZ'⟩ := hG2c E a w (B w) (hcard w hw)
      exact ⟨Z', hZ'⟩
    · by_cases hw : w ∈ S
      · simpa only [if_pos hw] using hg.2 w hw
      · simp only [if_neg hw]
        rw [hi w hw]
        exact (hS10 _ a 0).2.2.1
  subst heq
  obtain ⟨h, hhH⟩ := hφm.2.1
  obtain ⟨h', hhH'⟩ := hφm'.2.1
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    obtain ⟨Λ, hΛ⟩ := (hG5 E a ψ hψ).1 1
    exact hw (by rw [← hΛ _ hφm.1.1, map_zero])
  have hne : h.toL2 ≠ 0 := toL2_ne_zero h φ.continuous fun e => hφ0 (DFunLike.coe_injective e)
  intro hbot
  have hmem : h.toL2 ∈ H ⊓ H' := ⟨hhH, hhH'⟩
  rw [hbot] at hmem
  exact hne ((Submodule.mem_bot _).1 hmem)

end GlobalTheory.CompanionTheory.ClosedInvariantMeet

end
