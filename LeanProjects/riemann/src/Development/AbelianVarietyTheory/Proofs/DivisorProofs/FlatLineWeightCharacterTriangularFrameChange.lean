import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

namespace GlobalTheory.FlatChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

open Classical in

theorem exOf_flatWt_some (τ : Psi H) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) = if σ = τ.1 then -1 else if σ = conjEmb τ.1 then 1 else 0 := by
  classical
  show (wtOf Dw (flatWt Dw τ) 0).1 (σ, (i : ℕ)) = _
  have hi := i.2
  by_cases h : σ (H.rt : E) = H.rt0
  · have hp : (i : ℕ) < Dw.p := by simpa [Datum.mult, h] using hi
    have e0 := wtOf_big (flatWt Dw τ) 0 ⟨σ, h⟩ i hp
    refine e0.trans ?_
    have hne : σ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
    by_cases e : σ = τ.1
    · have : (⟨σ, h⟩ : Psi H) = τ := Subtype.ext e
      simp [flatWt, parWt, this, e]
    · have : (⟨σ, h⟩ : Psi H) ≠ τ := fun e' => e (congrArg Subtype.val e')
      simp [flatWt, parWt, this, e, hne]
  · have h' := conj_mem h
    have hq : (i : ℕ) < Dw.q := by simpa [Datum.mult, h] using hi
    have e0 := wtOf_small (flatWt Dw τ) 0 ⟨conjEmb σ, h'⟩ i hq
    simp only [conjEmb_conjEmb] at e0
    refine e0.trans ?_
    have hne : σ ≠ τ.1 := fun e' => h (e' ▸ τ.2)
    have hiff : (⟨conjEmb σ, h'⟩ : Psi H) = τ ↔ σ = conjEmb τ.1 := by
      constructor
      · intro e'; rw [← congrArg Subtype.val e', conjEmb_conjEmb]
      · intro e'; apply Subtype.ext; show conjEmb σ = τ.1; rw [e', conjEmb_conjEmb]
    by_cases e : σ = conjEmb τ.1
    · have h2 := hiff.2 e
      rw [if_neg hne, if_pos e]
      simp only [flatWt, parWt, if_pos h2]
      norm_num
    · have : (⟨conjEmb σ, h'⟩ : Psi H) ≠ τ := fun e' => e (hiff.1 e')
      simp [flatWt, parWt, this, e, hne]

theorem flatWt_char (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (τ : Psi H) (S : Type) [Field S] (t : Ix Dw → Sˣ) :
    (((∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i : Sˣ)) : S) * ∏ i : Fin (Dw.mult τ.1), (t (some ⟨τ.1, i⟩) : S) =
      ∏ j : Fin (Dw.mult (conjEmb τ.1)), (t (some ⟨conjEmb τ.1, j⟩) : S) := by
  classical
  have hne : τ.1 ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ τ.2)
  have key : (∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i) =
      (∏ i : Fin (Dw.mult τ.1), t (some ⟨τ.1, i⟩))⁻¹ * ∏ j : Fin (Dw.mult (conjEmb τ.1)), t (some ⟨conjEmb τ.1, j⟩) := by
    rw [Fintype.prod_option, Fintype.prod_sigma]
    have h0 : exOf Dw (flatWt Dw τ) 0 none = 0 := rfl
    rw [h0, zpow_zero, one_mul]
    rw [Fintype.prod_eq_mul τ.1 (conjEmb τ.1) hne ?_]
    · congr 1
      · rw [← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [exOf_flatWt_some, if_pos rfl, zpow_neg_one]
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [exOf_flatWt_some, if_neg hne.symm, if_pos rfl, zpow_one]
    · rintro σ ⟨h1, h2⟩
      refine Finset.prod_eq_one fun i _ => ?_
      rw [exOf_flatWt_some, if_neg h1, if_neg h2, zpow_zero]
  rw [key, ← Units.coe_prod, ← Units.coe_prod, ← Units.val_mul]
  congr 1
  rw [mul_comm, mul_inv_cancel_left]

example : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (S : Type) [Field S] (t : Ix Dw → Sˣ), (((∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i : Sˣ)) : S) * ∏ i : Fin (Dw.mult τ.1), (t (some ⟨τ.1, i⟩) : S) = ∏ j : Fin (Dw.mult (conjEmb τ.1)), (t (some ⟨conjEmb τ.1, j⟩) : S) := @flatWt_char

end GlobalTheory.FlatChar
