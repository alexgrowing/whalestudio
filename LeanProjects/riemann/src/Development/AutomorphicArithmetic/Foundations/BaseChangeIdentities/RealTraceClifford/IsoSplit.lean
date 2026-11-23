import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

section SlopeTestRemainingChoices

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem kSpan_self (F : Fin n → Fin n → Module.End ℂ V) (y : V) :
    y ∈ Formalism.REAL.kSpan (fun _ => true) F y := by
  rw [Formalism.REAL.kSpan, Submodule.mem_sInf]
  exact fun S hS => hS.1

private theorem kSpan_stb (F : Fin n → Fin n → Module.End ℂ V) (y : V) (a b : Fin n) {z : V}
    (hz : z ∈ Formalism.REAL.kSpan (fun _ => true) F y) : F a b z ∈ Formalism.REAL.kSpan (fun _ => true) F y := by
  rw [Formalism.REAL.kSpan, Submodule.mem_sInf] at hz ⊢
  exact fun S hS => hS.2 a b rfl z (hz S hS)

private theorem kSpan_le (F : Fin n → Fin n → Module.End ℂ V) {y : V} {Q : Submodule ℂ V}
    (hy : y ∈ Q) (hQ : Stb F Q) : Formalism.REAL.kSpan (fun _ => true) F y ≤ Q :=
  sInf_le ⟨hy, fun a b _ x hx => hQ a b x hx⟩

private theorem le_isoPart (F : Fin n → Fin n → Module.End ℂ V) {T : Set (Wt n)} {S : Submodule ℂ V}
    {y : V} {μ : Wt n} (hy : y ∈ S) (hμ : μ ∈ T) (h : KHighest (fun _ => true) F μ y) :
    Formalism.REAL.kSpan (fun _ => true) F y ≤ Formalism.REAL.isoPart (fun _ => true) F T S :=
  le_iSup₂_of_le (f := fun (y : V) (_ : y ∈ S ∧ ∃ μ ∈ T, KHighest (fun _ => true) F μ y) =>
    Formalism.REAL.kSpan (fun _ => true) F y) y ⟨hy, μ, hμ, h⟩ le_rfl

private theorem isoPart_map (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Wt n)) (S : Submodule ℂ V)
    (f : Module.End ℂ V) (Q : Submodule ℂ V)
    (h : ∀ y, y ∈ S → ∀ μ ∈ T, KHighest (fun _ => true) F μ y →
      ∀ z ∈ Formalism.REAL.kSpan (fun _ => true) F y, f z ∈ Q) :
    ∀ z ∈ Formalism.REAL.isoPart (fun _ => true) F T S, f z ∈ Q := by
  have hle : Formalism.REAL.isoPart (fun _ => true) F T S ≤ Q.comap f := by
    unfold Formalism.REAL.isoPart
    refine iSup₂_le fun y hy => ?_
    obtain ⟨hyS, μ, hμ, hk⟩ := hy
    exact fun w hw => h y hyS μ hμ hk w hw
  exact fun z hz => hle hz

private theorem isoPart_stb (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Wt n)) (S : Submodule ℂ V) :
    Stb F (Formalism.REAL.isoPart (fun _ => true) F T S) := fun a b =>
  isoPart_map F T S (F a b) _ fun y hy μ hμ hk z hz =>
    le_isoPart F hy hμ hk (kSpan_stb F y a b hz)

private theorem isoPart_cm (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Wt n)) (S : Submodule ℂ V)
    (B : Module.End ℂ V) (hB : Cm F S B) :
    ∀ x ∈ Formalism.REAL.isoPart (fun _ => true) F T S, B x ∈ Formalism.REAL.isoPart (fun _ => true) F T S := by
  have hc : ∀ a b x, B (F a b x) = F a b (B x) := fun a b x => LinearMap.congr_fun (hB.1 a b) x
  refine isoPart_map F T S B _ fun y hy μ hμ hk z hz => ?_
  have hkB : KHighest (fun _ => true) F μ (B y) :=
    ⟨fun a => by rw [← hc, hk.1 a, map_smul], fun a b hab he => by rw [← hc, hk.2 a b hab he, map_zero]⟩
  have hle : Formalism.REAL.kSpan (fun _ => true) F y ≤ (Formalism.REAL.kSpan (fun _ => true) F (B y)).comap B :=
    kSpan_le F (kSpan_self F (B y)) fun a b x hx => by
      rw [Submodule.mem_comap, hc]
      exact kSpan_stb F (B y) a b hx
  exact le_isoPart F (hB.2 y hy) hμ hkB (hle hz)

private theorem parts_zero {S₁ S₂ : Submodule ℂ V} (hd : Disjoint S₁ S₂) {u v : V} (hu : u ∈ S₁)
    (hv : v ∈ S₂) (h : u + v = 0) : u = 0 ∧ v = 0 := by
  have hv' : v = -u := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h
  have hv1 : v ∈ S₁ := hv' ▸ S₁.neg_mem hu
  have h0 : v = 0 := (Submodule.disjoint_def.mp hd) v hv1 hv
  refine ⟨?_, h0⟩
  rw [h0, add_zero] at h
  exact h

private theorem wt_comp (F : Fin n → Fin n → Module.End ℂ V) {S₁ S₂ : Submodule ℂ V} (hd : Disjoint S₁ S₂)
    (s1 : Stb F S₁) (s2 : Stb F S₂) {μ : Wt n} {y₁ y₂ : V} (h₁ : y₁ ∈ S₁) (h₂ : y₂ ∈ S₂)
    (h : IsWeight F μ (y₁ + y₂)) : IsWeight F μ y₁ ∧ IsWeight F μ y₂ := by
  have key : ∀ a, F a a y₁ = ↑(μ a) • y₁ ∧ F a a y₂ = ↑(μ a) • y₂ := by
    intro a
    have e := h a
    rw [map_add, smul_add] at e
    have hz := parts_zero hd (S₁.sub_mem (s1 a a y₁ h₁) (S₁.smul_mem _ h₁))
      (S₂.sub_mem (s2 a a y₂ h₂) (S₂.smul_mem _ h₂)) (by rw [sub_add_sub_comm, e, sub_self])
    exact ⟨sub_eq_zero.mp hz.1, sub_eq_zero.mp hz.2⟩
  exact ⟨fun a => (key a).1, fun a => (key a).2⟩

set_option maxHeartbeats 200000 in
private theorem hw_comp (F : Fin n → Fin n → Module.End ℂ V) {S₁ S₂ : Submodule ℂ V} (hd : Disjoint S₁ S₂)
    (s1 : Stb F S₁) (s2 : Stb F S₂) {μ : Wt n} {y₁ y₂ : V} (h₁ : y₁ ∈ S₁) (h₂ : y₂ ∈ S₂)
    (h : KHighest (fun _ => true) F μ (y₁ + y₂)) :
    KHighest (fun _ => true) F μ y₁ ∧ KHighest (fun _ => true) F μ y₂ := by
  obtain ⟨w1, w2⟩ := wt_comp F hd s1 s2 h₁ h₂ h.1
  refine ⟨⟨w1, fun a b hab e => ?_⟩, ⟨w2, fun a b hab e => ?_⟩⟩
  · have h0 := h.2 a b hab e
    rw [map_add] at h0
    exact (parts_zero hd (s1 a b _ h₁) (s2 a b _ h₂) h0).1
  · have h0 := h.2 a b hab e
    rw [map_add] at h0
    exact (parts_zero hd (s1 a b _ h₁) (s2 a b _ h₂) h0).2

end SlopeTestRemainingChoices

theorem UpperTheory.RealTr.isoSplit :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → S ≠ ⊥ → ∃ (ν : Wt n) (S₁ S₂ : Submodule ℂ V), S₁ ≠ ⊥ ∧ hw F ν ⊓ S₁ ≠ ⊥ ∧ S₁ ⊔ S₂ = S ∧ Disjoint S₁ S₂ ∧ Stb F S₁ ∧ Stb F S₂ ∧
      (∀ B, Cm F S B → Cm F S₁ B ∧ Cm F S₂ B) ∧ (∀ μ, μ ≠ ν → hw F μ ⊓ S₁ = ⊥) ∧
      ∀ μ, wsp F μ ⊓ S = (wsp F μ ⊓ S₁) ⊔ (wsp F μ ⊓ S₂) ∧ hw F μ ⊓ S = (hw F μ ⊓ S₁) ⊔ (hw F μ ⊓ S₂) := by
  intro n V _ _ F hF S hS hst hne
  have hK := Formalism.REAL.glRel_kRel (fun _ : Fin n => true) F hF.gl
  have hU : Formalism.REAL.KUnit (fun _ : Fin n => true) F := fun a b _ x y => hF.unit a b x y
  have hSt : Formalism.REAL.KStable (fun _ : Fin n => true) F S := fun a b _ x hx => hst a b x hx
  obtain ⟨x, hxS, hx0, ν, hxk⟩ := Formalism.REAL.kHiExist V n _ F S hS hK hU hSt hne
  obtain ⟨horth, hsup⟩ := Formalism.REAL.kIsoSplit V n _ F S {ν} hS hK hU hSt
  set S₁ := Formalism.REAL.isoPart (fun _ : Fin n => true) F {ν} S with hS₁
  set S₂ := Formalism.REAL.isoPart (fun _ : Fin n => true) F {ν}ᶜ S with hS₂
  have hd : Disjoint S₁ S₂ := by
    rw [Submodule.disjoint_def]
    intro v h1 h2
    have h0 := horth v h1 v h2
    rwa [inner_self_eq_zero] at h0
  have h1S : S₁ ≤ S := hsup ▸ le_sup_left
  have h2S : S₂ ≤ S := hsup ▸ le_sup_right
  have hst1 : Stb F S₁ := isoPart_stb F _ S
  have hst2 : Stb F S₂ := isoPart_stb F _ S
  have hx1 : x ∈ S₁ := le_isoPart (T := {ν}) F hxS (Set.mem_singleton ν) hxk (kSpan_self F x)
  refine ⟨ν, S₁, S₂, ?_, ?_, hsup, hd, hst1, hst2, ?_, ?_, ?_⟩
  · intro h
    rw [h] at hx1
    exact hx0 ((Submodule.mem_bot ℂ).mp hx1)
  · intro h
    have hm : x ∈ hw F ν ⊓ S₁ := Submodule.mem_inf.mpr ⟨hxk, hx1⟩
    rw [h] at hm
    exact hx0 ((Submodule.mem_bot ℂ).mp hm)
  · intro B hB
    exact ⟨⟨hB.1, isoPart_cm F _ S B hB⟩, ⟨hB.1, isoPart_cm F _ S B hB⟩⟩
  · intro μ hμ
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyk, hy1⟩ := Submodule.mem_inf.mp hy
    have hy2 : y ∈ S₂ := le_isoPart (T := {ν}ᶜ) F (h1S hy1) (show μ ∈ ({ν}ᶜ : Set (Wt n)) from hμ) hyk (kSpan_self F y)
    exact (Submodule.mem_bot ℂ).mpr (Submodule.disjoint_def.mp hd y hy1 hy2)
  · intro μ
    constructor
    · apply le_antisymm
      · intro y hy
        obtain ⟨hyw, hyS⟩ := Submodule.mem_inf.mp hy
        rw [← hsup] at hyS
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := Submodule.mem_sup.mp hyS
        obtain ⟨w1, w2⟩ := wt_comp F hd hst1 hst2 h₁ h₂ hyw
        exact Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨w1, h₁⟩) (Submodule.mem_inf.mpr ⟨w2, h₂⟩)
      · exact sup_le (inf_le_inf_left _ h1S) (inf_le_inf_left _ h2S)
    · apply le_antisymm
      · intro y hy
        obtain ⟨hyk, hyS⟩ := Submodule.mem_inf.mp hy
        rw [← hsup] at hyS
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := Submodule.mem_sup.mp hyS
        obtain ⟨k1, k2⟩ := hw_comp F hd hst1 hst2 h₁ h₂ hyk
        exact Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨k1, h₁⟩) (Submodule.mem_inf.mpr ⟨k2, h₂⟩)
      · exact sup_le (inf_le_inf_left _ h1S) (inf_le_inf_left _ h2S)
