import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WorkingClassesFrozen

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.RowsParts

variable {Bd : BdT} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {eps : ℝ} {Fm : FamP eps} {hc : 𝒜 Fm}

theorem ev_prem {p : Prop} {q : ℝ → BdP Bd} (h : p → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ind.Ev σ Fm hc (q C)) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ind.Ev σ Fm hc fun D O c b => p → q C D O c b := by
  by_cases hp : p
  · obtain ⟨C0, h0, h⟩ := h hp
    refine ⟨C0, h0, fun C hC => ?_⟩
    obtain ⟨x0, h⟩ := h C hC
    exact ⟨x0, fun x hx hle i _ => h x hx hle i⟩
  · exact ⟨0, le_rfl, fun _ _ => ⟨0, fun _ _ _ _ h => absurd h hp⟩⟩

end GlobalTheory.Fc.RowsParts

namespace GlobalTheory.Fc

open RowsParts

theorem row_rRows_of_parts : ∀ (DR : R1.DefT) (Q : V4.Slot) (Lk : LkT Bundle), Row Q Lk (fun 𝒜 σ => ∃ τ : TieSel σ, Ind.EvWC (fun _ => True) Ind.Small 𝒜 (partSel σ τ) ∧ Ind.EvWC (fun _ => True) Ind.L3 𝒜 (partSel σ τ) ∧ Ind.EvWC (fun Fm => DIVinN Fm) Ind.ON 𝒜 (partSel σ τ) ∧ Ind.EvWC (fun _ => True) Ind.L6 𝒜 (partSel σ τ) ∧ Ind.EvWC (fun Fm => DIVinN Fm) Ind.FUN 𝒜 (partSel σ τ)) → Row Q Lk (Ind.EvW (Bd := Bundle) fun _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) → Row Q Lk (Ind.EvW (Bd := Bundle) fun _ _ _ b => Formalism.L2.Rows.RowsHoldKap3 b.P) → Row Q Lk (Ind.EvWC (Bd := Bundle) (fun _ => True) fun C CH D O c b => DR D O c b C CH) → R1.RestRowsConditionAtBundlePoints DR Q Lk := by
  intro DR Q Lk h1 h2 h3 h4
  refine (h1.and (h2.and (h3.and h4))).imp fun 𝒜 σ _ H => ?_
  obtain ⟨⟨τ, hS, hL3, hON, hL6, hFUN⟩, hM, hK, hD⟩ := H
  have hw : ∀ {eps : ℝ} (Fm : FamP eps), GlobalTheory.Cp.D3 3 𝒜 Fm → W3 𝒜 Fm :=
    fun Fm h => (working_classes_frozen.1 𝒜 _ Fm).2.1 h
  have hall := Closed.and hS (Closed.and hL3 (Closed.and hON (Closed.and hL6 (Closed.and hFUN
    (Closed.and hM (Closed.and hK hD))))))
  refine Closed.imp (Pk.Closed.sub hall hw) fun Fm CH _ H hc => ?_
  obtain ⟨hS, hL3, hON, hL6, hFUN, hM, hK, hD⟩ := H
  have hc' := hw Fm hc
  obtain ⟨C1, p1, hS⟩ := hS hc' trivial
  obtain ⟨C2, -, hL3⟩ := hL3 hc' trivial
  obtain ⟨C3, -, hON⟩ := ev_prem (hON hc')
  obtain ⟨C4, -, hL6⟩ := hL6 hc' trivial
  obtain ⟨C5, -, hFUN⟩ := ev_prem (hFUN hc')
  obtain ⟨C6, -, hD⟩ := hD hc' trivial
  obtain ⟨C, k1, k2, k3, k4, k5, k6⟩ : ∃ C : ℝ, C1 ≤ C ∧ C2 ≤ C ∧ C3 ≤ C ∧ C4 ≤ C ∧ C5 ≤ C ∧ C6 ≤ C :=
    ⟨max C1 (max C2 (max C3 (max C4 (max C5 C6)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  obtain ⟨x1, hS⟩ := hS C k1
  obtain ⟨x2, hL3⟩ := hL3 C k2
  obtain ⟨x3, hON⟩ := hON C k3
  obtain ⟨x4, hL6⟩ := hL6 C k4
  obtain ⟨x5, hFUN⟩ := hFUN C k5
  obtain ⟨x6, hD⟩ := hD C k6
  obtain ⟨x7, hM⟩ := hM hc'
  obtain ⟨x8, hK⟩ := hK hc'
  obtain ⟨x0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :
      ∃ y : ℝ, x1 ≤ y ∧ x2 ≤ y ∧ x3 ≤ y ∧ x4 ≤ y ∧ x5 ≤ y ∧ x6 ≤ y ∧ x7 ≤ y ∧ x8 ≤ y :=
    ⟨max x1 (max x2 (max x3 (max x4 (max x5 (max x6 (max x7 x8)))))),
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  refine ⟨C, p1.trans k1, x0, fun x hx _ hle i => ⟨?_, hD x hx (l6.trans hle) i⟩⟩
  have s := hS x hx (l1.trans hle) i
  exact
    { w1 := s.1
      covol := hL3 x hx (l2.trans hle) i
      onto := hON x hx (l3.trans hle) i
      lamLow := fun _ => hL6 x hx (l4.trans hle) i
      seeIso := s.2.1
      miStar := hM x hx (l7.trans hle) i
      fun0 := hFUN x hx (l5.trans hle) i
      pass := s.2.2
      kap := hK x hx (l8.trans hle) i }

end GlobalTheory.Fc
