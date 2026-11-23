import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTermsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionValueInFrameLinearUniqueExists
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.ThetaBound

theorem le_of_sum {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (hq : ∀ i, (q : WithTop ℚ) ≤ v (x i)) : (q : WithTop ℚ) ≤ v s := by
  obtain ⟨T, hT⟩ := h q
  have := v.map_le_add (hT T le_rfl) (v.map_le_sum (s := T) fun i _ => hq i)
  rwa [sub_add_cancel] at this

theorem square_nonneg {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    {D : DegData V (IsLocalRing.maximalIdeal V)} {Q : D.toPre.X → ℤ} (hϖ : Irreducible ϖ)
    (hQ : QForm.IsQ D.toPre ϖ Q) (n : ℕ) (hn : 1 ≤ n) (y χ : D.toPre.X) :
    (0 : ℚ) ≤ 0 + (Q χ : ℚ) / (1 : ℕ) + (QForm.bOf D.toPre Q y χ : ℚ) / n + (Q y : ℚ) / (n : ℚ) ^ 2 := by
  have h0 : 0 ≤ Q (n • χ + y) := by
    by_cases h : n • χ + y = 0
    · rw [h, QForm.Q_zero hϖ D hQ]
    · exact le_trans zero_le_one (QForm.Q_pos hϖ D hQ h)
  have e : Q (n • χ + y) = n ^ 2 * Q χ + n * QForm.bOf D.toPre Q y χ + Q y := by
    have e₁ : Q (n • χ + y) = Q (n • χ) + Q y + QForm.bOf D.toPre Q (n • χ) y := by
      simp only [QForm.bOf]; ring
    have e₂ : QForm.bOf D.toPre Q χ y = QForm.bOf D.toPre Q y χ := by
      simp only [QForm.bOf, add_comm χ y]; ring
    rw [e₁, DVR.Q_nsmul hϖ hQ, DVR.bOf_nsmul_left hϖ hQ, e₂]; ring
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have h1 : (0 : ℚ) ≤ (n : ℚ) ^ 2 * Q χ + n * (QForm.bOf D.toPre Q y χ : ℚ) + Q y := by
    rw [e] at h0; exact_mod_cast h0
  have e₃ : 0 + (Q χ : ℚ) / (1 : ℕ) + (QForm.bOf D.toPre Q y χ : ℚ) / n + (Q y : ℚ) / (n : ℚ) ^ 2 =
      ((n : ℚ) ^ 2 * Q χ + n * (QForm.bOf D.toPre Q y χ : ℚ) + Q y) / (n : ℚ) ^ 2 := by
    field_simp
    push_cast
    ring
  rw [e₃]
  positivity

theorem norm_theta_le : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → ∀ a, ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ ‖c‖ := by
  intro hL hL₂ hT o Ω _ _ _ _ S ρ p _ y₀ u l _ x rig e th s _ hS ϖ Q v lam hϖ hv hN w₀ th' ϑ c hW hE hP hc a
  obtain ⟨-, htf, hth, -⟩ := hS
  obtain ⟨-, hQ, -, hle, -⟩ := hN
  obtain ⟨hLL, h₁, h₂, h₃, h₄⟩ := laws_all hL hL₂
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hn : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (le_trans one_le_two S.N_ge)
  obtain ⟨f, hf, hsurj, -⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn
  obtain ⟨q, hq⟩ := hsurj (x a) (htf a).1
  have hqx := (hf q (x a)).2 hq.symm
  obtain ⟨-, hmul, huniq, hex⟩ := GlobalTheory.TestFibre.CombValue.valIs_linear hL u.V u.A (PadicAlgCl p) 1 (x a) (e a)
  obtain ⟨c', hc'⟩ := hex (htf a).2.1 th'
  have hval : y₀ ⟨S.th a, S.th_mem a⟩ = c * c' := huniq th _ _ (hth a) (hmul th' th c c' hc hc')
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hLL h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ (PadicAlgCl p) v hv
    u.A u.G u.semi u.U w₀ rig hW (S.r * S.N) hn q (x a) hqx (e a) (htf a)
  obtain ⟨-, -, -, -, hqk, -, hterm⟩ := GlobalTheory.UT.CoefVal.main hLL h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ
    (PadicAlgCl p) v hv q.g
  have hsv := hsum 1 le_rfl w₁ ⟨hw₁, fun z J _ => (pow_one _).symm⟩ th' ϑ c' hE hc'
  have h0 : ((0 : ℚ) : WithTop ℚ) ≤ v c' := le_of_sum hsv fun χ =>
    le_trans (WithTop.coe_le_coe.2 (square_nonneg hϖ hQ (S.r * S.N) hn q.y χ))
      ((hterm 1 le_rfl w₁ ϑ hw₁).2 _ _ 0 (hqk _ hn q) hv₁ hP.1 χ)
  have h1 : ‖c'‖ ≤ 1 := by simpa using (hle c' 0).1 h0
  rw [hval, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) h1

end GlobalTheory.ThetaBound
end
