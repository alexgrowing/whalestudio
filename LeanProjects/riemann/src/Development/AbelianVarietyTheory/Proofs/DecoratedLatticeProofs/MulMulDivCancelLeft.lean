import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineOfGlued
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.LevZero

theorem sum_fin_two_mul_add_one {M : Type*} [AddCommMonoid M] {ρ n : ℕ} (hn : n = 2 * ρ + 1) (f : Fin n → M)
    (a b : Fin ρ → M) (m : M) (ha : ∀ (i : Fin ρ) (j : Fin n), j.1 = i.1 → f j = a i) (hm : ∀ j : Fin n, j.1 = ρ → f j = m)
    (hb : ∀ (i : Fin ρ) (j : Fin n), j.1 + i.1 = 2 * ρ → f j = b i) :
    ∑ j, f j = ∑ i, a i + m + ∑ i, b i := by
  subst hn
  have e : ρ + (1 + ρ) = 2 * ρ + 1 := by omega
  rw [← Fin.sum_congr' f e, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one, add_assoc]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => ha i _ (by simp)
  · congr 1
    · exact hm _ (by simp)
    · rw [← Equiv.sum_comp Fin.revPerm b]
      refine Finset.sum_congr rfl fun i _ => hb _ _ ?_
      simp [Fin.val_rev]
      omega

theorem mul_div_mem_integer_iff {k : Type} [Field k] [ValuativeRel k] {c : k} (hc : valuation k c = 1) (w z : k) :
    w * (z / c) ∈ 𝒪[k] ↔ w * z ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_mul, map_mul, map_div₀, hc, div_one]

theorem mul_mul_div_cancel_left' {k : Type} [Field k] {c : k} (hc : c ≠ 0) (P X : k) : c * P * (X / c) = P * X := by
  field_simp

theorem wShape_of_besFrame_loc : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (ρ : ℕ) (h0 : 0 + 2 * ρ + 2 = D.R.m) (L : GlobalTheory.FinPl.Lat (c.V 0)), (∀ y : XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1) → G.k, (fun r => G.q.sec (((G.FY 0 (G.s + 1) (zero_add _)).β *ᵥ y) r)) ∈ GlobalTheory.FinPl.latV (c.V 0) L (· = G.q.v) ↔ (∀ z, y (Sum.inl z) ∈ 𝒪[G.k]) ∧ ∀ i : Fin (G.s + 1), ((((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹ * y (Sum.inr i)) ∈ 𝒪[G.k]) → GlobalTheory.Core.Mi.LatMatch.WShape G.q (c.bes 0 ρ h0).d (c.bes 0 ρ h0).o (c.bes 0 ρ h0).ζ L (fun i => (((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹) (fun i => (((G.S.ϖ : G.kˣ) : G.k) ^ (2 * ρ - i.1 + 1))⁻¹) ((((G.S.ϖ : G.kˣ) : G.k) ^ (ρ + 1))⁻¹) 1 (c.x 0).L := by
  intro D c v G ρ h0 L hL
  obtain ⟨hc, hA, he, hz, he'⟩ := G.bes 0 ρ h0 (G.s + 1) (zero_add _)
  intro x x' t y
  have hsc : valuation G.k (G.sc 0) = 1 := G.sc_unit 0
  have hxi : valuation G.k (GlobalTheory.LocMod.ofSplit G.q).xi = 1 := GlobalTheory.MiTop.GluedLine.valuation_xi_zero_eq_one G.q G.unit
  have hhz : valuation G.k ((GlobalTheory.LocMod.ofSplit G.q).hz (c.B 0 ρ h0)) = 1 := G.hz_unit 0 ρ h0
  set cE : Fin ρ → G.k := fun i => G.sc 0 * (GlobalTheory.LocMod.ofSplit G.q).xi ^ (ρ - i.1) with hcE
  set cE' : Fin ρ → G.k := fun i => G.sc 0 * (-(GlobalTheory.LocMod.ofSplit G.q).hz (c.B 0 ρ h0) / (GlobalTheory.LocMod.ofSplit G.q).xi) *
    (-1 / (GlobalTheory.LocMod.ofSplit G.q).xi) ^ (ρ - 1 - i.1) with hcE'
  have vE : ∀ i, valuation G.k (cE i) = 1 := fun i => by simp [cE, map_pow, hsc, hxi]
  have vE' : ∀ i, valuation G.k (cE' i) = 1 := fun i => by
    simp [cE', map_pow, map_div₀, Valuation.map_neg, hsc, hxi, hhz]
  have nz : ∀ {c : G.k}, valuation G.k c = 1 → c ≠ 0 := fun h h0 => by simp [h0] at h
  have he2 : ∀ (i : Fin ρ) (j : Fin (G.s + 1)), j.1 = i.1 → ∀ r, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inr j) =
      cE i * G.q.pr (incA D ((c.bes 0 ρ h0).d.e r i)) := he
  have hz2 : ∀ (j : Fin (G.s + 1)), j.1 = ρ → ∀ r, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inr j) =
      G.sc 0 * G.q.pr (incA D (((c.bes 0 ρ h0).d.i₀ *ᵥ vecB (c.bes 0 ρ h0).o (c.bes 0 ρ h0).ζ) r)) := hz
  have he'2 : ∀ (i : Fin ρ) (j : Fin (G.s + 1)), j.1 + i.1 = 2 * ρ → ∀ r, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inr j) =
      cE' i * G.q.pr (incA D ((c.bes 0 ρ h0).d.e' r i)) := he'
  have hA2 : ∀ r a, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inl a) =
      (atW G.q ((c.bes 0 ρ h0).d.i₀ * (c.bes 0 ρ h0).o.iA) * (G.FX 0 (by omega)).β) r a := hA
  let Yr : Fin (G.s + 1) → G.k := fun j => if h : j.1 < ρ then x ⟨j.1, h⟩ / cE ⟨j.1, h⟩ else if j.1 = ρ then t / G.sc 0
      else if h' : 2 * ρ - j.1 < ρ then x' ⟨2 * ρ - j.1, h'⟩ / cE' ⟨2 * ρ - j.1, h'⟩ else 0
  let Y : StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1) → G.k := Sum.elim ((G.FX 0 (by omega)).γ *ᵥ y) Yr
  have YrE : ∀ (i : Fin ρ) (j : Fin (G.s + 1)), j.1 = i.1 → Yr j = x i / cE i := by
    intro i j hj
    have h : j.1 < ρ := hj ▸ i.2
    have : (⟨j.1, h⟩ : Fin ρ) = i := Fin.ext hj
    simp only [Yr, dif_pos h, this]
  have YrZ : ∀ (j : Fin (G.s + 1)), j.1 = ρ → Yr j = t / G.sc 0 := by
    intro j hj
    simp only [Yr, dif_neg (show ¬ j.1 < ρ by omega), if_pos hj]
  have YrE' : ∀ (i : Fin ρ) (j : Fin (G.s + 1)), j.1 + i.1 = 2 * ρ → Yr j = x' i / cE' i := by
    intro i j hj
    have h : 2 * ρ - j.1 < ρ := by omega
    have : (⟨2 * ρ - j.1, h⟩ : Fin ρ) = i := Fin.ext (by simp; omega)
    simp only [Yr, dif_neg (show ¬ j.1 < ρ by omega), if_neg (show ¬ j.1 = ρ by omega), dif_pos h, this]
  have hlat : (∀ a, Y (Sum.inl a) ∈ 𝒪[G.k]) ↔ (fun r => G.q.sec (y r)) ∈ GlobalTheory.FinPl.latV (c.X 0) (c.x 0).L (· = G.q.v) := by
    have h := G.latX 0 (by omega) ((G.FX 0 (by omega)).γ *ᵥ y)
    rw [Matrix.mulVec_mulVec, (G.FX 0 (by omega)).βγ, Matrix.one_mulVec] at h
    exact h
  refine Iff.trans (Eq.to_iff ?_) ((hL Y).trans ?_)
  · congr 1
    funext r
    congr 1
    symm
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    simp only [Y, Sum.elim_inl, Sum.elim_inr]
    have h1 : ∑ a, (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inl a) * ((G.FX 0 (by omega)).γ *ᵥ y) a =
        (atW G.q ((c.bes 0 ρ h0).d.i₀ * (c.bes 0 ρ h0).o.iA) *ᵥ y) r := by
      calc _ = ((atW G.q ((c.bes 0 ρ h0).d.i₀ * (c.bes 0 ρ h0).o.iA) * (G.FX 0 (by omega)).β) *ᵥ
            ((G.FX 0 (by omega)).γ *ᵥ y)) r := by simp only [hA2]; rfl
        _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, (G.FX 0 (by omega)).βγ, Matrix.mul_one]
    have h2 := sum_fin_two_mul_add_one hc (fun j => (G.FY 0 (G.s + 1) (zero_add _)).β r (Sum.inr j) * Yr j)
      (fun i => G.q.pr (incA D ((c.bes 0 ρ h0).d.e r i)) * x i) (fun i => G.q.pr (incA D ((c.bes 0 ρ h0).d.e' r i)) * x' i)
      (G.q.pr (incA D (((c.bes 0 ρ h0).d.i₀ *ᵥ vecB (c.bes 0 ρ h0).o (c.bes 0 ρ h0).ζ) r)) * t)
      (fun i j hj => by beta_reduce; rw [he2 i j hj r, YrE i j hj, mul_mul_div_cancel_left' (nz (vE i))])
      (fun j hj => by beta_reduce; rw [hz2 j hj r, YrZ j hj, mul_mul_div_cancel_left' (nz hsc)])
      (fun i j hj => by beta_reduce; rw [he'2 i j hj r, YrE' i j hj, mul_mul_div_cancel_left' (nz (vE' i))])
    rw [h1, h2]
    have hm : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun V => rfl
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm, Matrix.map_one _ (map_zero G.q.pr) (map_one G.q.pr),
      Matrix.one_mulVec]
    simp only [Matrix.mulVec, dotProduct, atW, Matrix.map_apply]
    ring
  · have hinr : (∀ j : Fin (G.s + 1), (((G.S.ϖ : G.kˣ) : G.k) ^ (j.1 + 1))⁻¹ * Yr j ∈ 𝒪[G.k]) ↔
        (∀ a : Fin ρ, (((G.S.ϖ : G.kˣ) : G.k) ^ (a.1 + 1))⁻¹ * x a ∈ 𝒪[G.k]) ∧
        (∀ a : Fin ρ, (((G.S.ϖ : G.kˣ) : G.k) ^ (2 * ρ - a.1 + 1))⁻¹ * x' a ∈ 𝒪[G.k]) ∧
        (((G.S.ϖ : G.kˣ) : G.k) ^ (ρ + 1))⁻¹ * t ∈ 𝒪[G.k] := by
      constructor
      · intro h
        refine ⟨fun a => ?_, fun a => ?_, ?_⟩
        · have := h ⟨a.1, by omega⟩
          rwa [YrE a _ rfl, mul_div_mem_integer_iff (vE a)] at this
        · have := h ⟨2 * ρ - a.1, by omega⟩
          rwa [YrE' a _ (by simp only; omega), mul_div_mem_integer_iff (vE' a)] at this
        · have := h ⟨ρ, by omega⟩
          rwa [YrZ _ rfl, mul_div_mem_integer_iff hsc] at this
      · rintro ⟨h1, h2, h3⟩ j
        rcases lt_trichotomy j.1 ρ with hj | hj | hj
        · rw [YrE ⟨j.1, hj⟩ j rfl, mul_div_mem_integer_iff (vE _)]
          exact h1 ⟨j.1, hj⟩
        · rw [YrZ j hj, mul_div_mem_integer_iff hsc, hj]
          exact h3
        · have hi : 2 * ρ - j.1 < ρ := by omega
          rw [YrE' ⟨2 * ρ - j.1, hi⟩ j (by simp only; omega), mul_div_mem_integer_iff (vE' _)]
          have h4 := h2 ⟨2 * ρ - j.1, hi⟩
          have h5 : 2 * ρ - (2 * ρ - j.1) = j.1 := by omega
          simp only [h5] at h4
          exact h4
    constructor
    · rintro ⟨hl, hr⟩
      obtain ⟨a, b, c⟩ := hinr.1 hr
      exact ⟨a, b, c, hlat.1 hl⟩
    · rintro ⟨a, b, c, l⟩
      exact ⟨hlat.2 l, hinr.2 ⟨a, b, c⟩⟩

end GlobalTheory.LevZero

end
