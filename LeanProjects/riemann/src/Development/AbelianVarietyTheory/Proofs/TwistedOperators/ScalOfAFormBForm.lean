import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma pos_of_isLval {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} {c : Eig D} {z : ℝ} (h : IsLval R i t c z) : 0 < z := by
  obtain ⟨_, _, hL⟩ := h
  exact hL.2.1

private lemma galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one {p q r : Prop} (f : p → q) (k₁ : ¬p → r) (k₂ : q → r) : r := by
  by_cases hp : p
  · exact k₂ (f hp)
  · exact k₁ hp

theorem scal_of_aForm_bForm {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (SF)
    (hA : AForm R SF) (hB : BForm R SF) (hM : MatchUp R SF) : Scal R SF := by
  obtain ⟨a, ha, hA⟩ := hA
  obtain ⟨κ₀, hκ₀, hB⟩ := hB
  have hPa : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i

  have hA' : ∀ i t c, ∃ l : ℝ, 0 < l ∧
      (∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((l : ℝ) : ℂ) • x) ∧
      ((∃ z, IsLval R i t c z ∧ l = a i * z) ∨ ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, x = 0) := by
    intro i t c
    refine galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one (hA i t c) (fun h => ?_) (fun hq => ?_)
    · have h0 : ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, x = 0 := by
        intro x hx
        by_contra hne
        exact h fun hb => hne (by rw [hb] at hx; exact (Submodule.mem_bot _).mp hx)
      refine ⟨1, one_pos, fun x hx => ?_, Or.inr h0⟩
      rw [h0 x hx]
      simp only [map_zero, smul_zero]
    · obtain ⟨z, hz, hx⟩ := hq
      exact ⟨a i * z, mul_pos (ha i) (pos_of_isLval hz), hx, Or.inl ⟨z, hz, rfl⟩⟩
  choose lam hlpos hlW hlz using hA'
  refine ⟨lam, κ₀ / (∏ i, a i), div_pos hκ₀ hPa, hlpos, hlW, ?_⟩
  intro t c x hx
  refine galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one (hM c) (fun h => ?_) (fun hW => ?_)
  ·
    have hx0 : x = 0 := by
      by_contra hne
      exact h fun hb => hne (by rw [hb] at hx; exact (Submodule.mem_bot _).mp hx)
    rw [hx0]
    simp only [map_zero, smul_zero]
  ·
    have hz' : ∀ i, ∃ z, IsLval R i t c z ∧ lam i t c = a i * z := fun i =>
      (hlz i t c).resolve_right fun h0 => hW i ((Submodule.eq_bot_iff _).mpr h0)
    choose z hz hlz' using hz'
    have key : κ₀ / (∏ i, a i) * ∏ i, lam i t c = κ₀ * ∏ i, z i := by
      rw [Finset.prod_congr rfl fun i _ => hlz' i, Finset.prod_mul_distrib, ← mul_assoc,
        div_mul_cancel₀ κ₀ hPa.ne']
    rw [key]
    exact hB t c z hz x hx

end GlobalTheory.LiftRows

end
