import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactTermAfterTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTermsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.TorsionUnit
open GlobalTheory.TorusExt

theorem eq_zero_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (q0 : 0 < q) (i₀ : Ix) (h₀ : v (x i₀) = 0)
    (hq : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (x i)) : v s = 0 := by
  classical
  obtain ⟨S, hS⟩ := h q
  have a := v.map_le_add (hS (insert i₀ S) (Finset.subset_insert _ _))
    (v.map_le_sum (s := (insert i₀ S).erase i₀) (f := x) fun i hi => hq i (Finset.ne_of_mem_erase hi))
  have e : s = x i₀ + (s - ∑ i ∈ insert i₀ S, x i + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by
    rw [← Finset.add_sum_erase _ x (Finset.mem_insert_self i₀ S)]; ring
  have lt : v (x i₀) < v (s - ∑ i ∈ insert i₀ S, x i + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by
    rw [h₀]
    exact lt_of_lt_of_le (by exact_mod_cast q0) a
  rw [e, v.map_add_eq_of_lt_left lt, h₀]

attribute [local instance] gtGroup

theorem unit_value : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th₀ : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th₀ ϑ → Prim D Q v ϑ → ∀ (k : ℕ), 2 ≤ k → IsUnit (k : V) → ∃ pk : QkPt D.toPre F k, pk.y = 0 ∧ ∀ x, QkToAkU U.toUnifPre F k pk x → ∀ e : FrAt x, IsTorsFrame A ρ k x e → ∀ c : F, ValAt th₀ x e c → v c = 0 := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP k hk hu
  have hB := D.tau_bimult
  have k1 : 1 ≤ k := by omega
  obtain ⟨h, o, g₂, ho, hh, hg₂, hv₂⟩ := GlobalTheory.UT.ExactTerm.exact_term_after_torsion hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv
    ϑ hP k hk hu 0 0
  rw [isZero_iff_eq] at ho
  rw [isNsmul_iff_eq] at hh
  rw [isAdd_iff_eq, zero_add] at hg₂
  subst hg₂
  have z : k • g₂ = iota hB F 0 := by rw [map_zero, ← hh, ho]
  refine ⟨qkMk hB 0 g₂ z, rfl, fun x hx e he c hval => ?_⟩
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN k k1 _ x hx e he
  have hS : SumV v (coef ϑ g₂ w₁) c := hsum 1 le_rfl w₁ ⟨hw₁, fun z J _ => (pow_one _).symm⟩ th ϑ c hE hval
  obtain ⟨-, -, -, -, hqk, -, hterm⟩ := GlobalTheory.UT.CoefVal.main hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv g₂
  have hl := hqk k k1 (qkMk hB 0 g₂ z)
  have q0 : Q 0 = 0 := QForm.Q_zero hϖ D hQ
  have b0 : ∀ χ, QForm.bOf D.toPre Q 0 χ = 0 := fun χ => by
    rw [QForm.bOf, zero_add, q0]; ring
  have hv₁ : GenV hϖ hv w₁ 0 := by
    have e0 : ((Q (qkMk hB 0 g₂ z).y : ℚ) / (k : ℚ) ^ 2) = 0 := by rw [qkMk_y, q0]; simp
    rwa [e0] at hv₁
  have hl : GtV hϖ hv g₂ fun _ => 0 := by
    intro χ
    have a := hl χ
    have e0 : ((QForm.bOf D.toPre Q (qkMk hB 0 g₂ z).y χ : ℚ) / (k : ℚ)) = 0 := by rw [qkMk_y, b0]; simp
    simp only [e0] at a
    exact a
  refine eq_zero_of_sumV hS one_pos 0 ?_ fun χ hχ => ?_
  · rw [hv₂ w₁ _ _ hw₁ hl hv₁, q0]
    simp
  · refine le_trans (WithTop.coe_le_coe.2 ?_) ((hterm 1 le_rfl w₁ ϑ hw₁).2 _ 0 0 hl hv₁ hP.1 χ)
    have b : (1 : ℚ) ≤ (Q χ : ℚ) := by exact_mod_cast QForm.Q_pos hϖ D hQ hχ
    simpa using b

end GlobalTheory.ZH.TorsionUnit
end
