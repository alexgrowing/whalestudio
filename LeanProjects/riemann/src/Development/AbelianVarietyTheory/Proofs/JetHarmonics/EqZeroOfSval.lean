import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullComp

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem sval_of_heq {m n : ℕ} (h : m = n) (s : Fam D.toPre F m) (t : Fam D.toPre F n) (e : HEq s t)
    {α β : D.toPre.X} (hα : α = β) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J) :
    sval (t.s α) r z J = sval (s.s β) r z J := by
  subst h hα
  cases e
  rfl

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h (fun k => J (r ≫ φ k)))).trans ?_
  unfold gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem eq_zero_of_sval {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j) : s.f j = 0 :=
  sec_ext_val hL (s' := SectionArithmetic.secZero _) (fun y J hJ => (h y J hJ).trans
    (sval_eq_zero _ (fun _ => rfl) _ _ _).symm) j

theorem aF_comp (oa : D.toPre.OAct O) (a a' : O) : aF D F oa a ≫ aF D F oa a' = aF D F oa (a' * a) := by
  have : oa.onB.act (a' * a) = oa.onB.act a ≫ oa.onB.act a' := by
    first
      | exact oa.onB.map_mul _ _
      | (rw [mul_comm]; exact oa.onB.map_mul _ _)
  simp [aF, DegPre.prB, this]

theorem zF_aF (oa : D.toPre.OAct O) (a : O) : DegPre.zF D.toPre F ≫ aF D F oa a = DegPre.zF D.toPre F := by
  have := oa.onB.hom a
  have z₁ : DegPre.zF D.toPre F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  apply CartesianMonoidalCategory.hom_ext
  · rw [aF, Category.assoc, lift_fst]
  · rw [aF, Category.assoc, lift_snd, ← Category.assoc, z₂, MonObj.one_comp]
    first | done | exact z₂.symm

end GlobalTheory.PullComp

namespace GlobalTheory

open PullComp in

theorem pullAl_comp : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a a' : O) (N N' k : ℕ), 1 ≤ N → 1 ≤ N' → 1 ≤ k → a * star a = (N : O) → a' * star a' = (N' : O) → ∀ (s : Fam D.toPre F k) (s₁ : Fam D.toPre F (k * N')) (s₂ : Fam D.toPre F (k * N' * N)) (s₃ : Fam D.toPre F (k * (N' * N))), PullAl D F oa a' k N' s s₁ → PullAl D F oa a (k * N') N s₁ s₂ → HEq s₂ s₃ → PullAl D F oa (a' * a) k (N' * N) s s₃ := by
  intro _ V _ _ _ D F _ _ O _ _ _ oa w0 _ a a' N N' k hN hN' _ _ _ s s₁ s₂ s₃ h₁ h₂ he
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  have hst : ∀ χ : D.toPre.X, star (a' * a) • χ = star a • star a' • χ := fun χ => by
    rw [star_mul, mul_smul]
  have hcl : (aF D F oa a).left ≫ (aF D F oa a').left = (aF D F oa (a' * a)).left :=
    congrArg (fun q => q.left) (aF_comp D F oa a a')
  have hzl : (DegPre.zF D.toPre F).left ≫ (aF D F oa a).left = (DegPre.zF D.toPre F).left :=
    congrArg (fun q => q.left) (zF_aF D F oa a)
  refine ⟨fun χ => ?_, fun β hβ => ?_⟩
  · obtain ⟨u₁, hu₁, c₁, r₁⟩ := h₁.1 χ
    obtain ⟨u₂, hu₂, c₂, r₂⟩ := h₂.1 (star a' • χ)
    obtain ⟨u, hu, vu⟩ := exists_gen hL (φ' := pullφ D F oa (a' * a) χ) (ε' := pullε k (N' * N)) (fun U _ h => by
        simp only [pullφ, pullε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hst, ← hcl, Category.assoc,
          zpow_neg, Finset.prod_inv_distrib, Nat.mul_assoc]
        group)
      (LB.mulGen D.toPre.P.L _ _ _ _ u₂ (LB.pullGen D.toPre.P.L _ _ u₁ (aF D F oa a).left))
      (mulGen_isGen _ _ _ _ _ _ _ hu₂ (pullGen_isGen _ _ _ _ hu₁ _))
    refine ⟨u, hu, corr_of_val hL fun y J hJ => ?_, (secRel_iff hL _ _ _ _ _ _ _ _ _ _).2 fun y J hJ => ?_⟩
    · have e₁ := val_corr hJ c₁ (𝟙 _)
      have e₂ := val_corr hJ c₂ (𝟙 _)
      rw [val_pull hJ, val_pull hJ, val_pow] at e₁ e₂
      rw [val_pull hJ, val_pull hJ, val_pow, vu _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, hzl, e₁, e₂,
        ← pow_add]
      congr 1
      obtain ⟨N, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      obtain ⟨N', rfl⟩ : ∃ n, N' = n + 1 := ⟨N' - 1, by omega⟩
      have : (N' + 1) * (N + 1) - 1 = (N' + 1) * N + N' := by
        rw [Nat.sub_eq_iff_eq_add (Nat.succ_le_of_lt (by positivity))]; ring
      rw [this, Nat.add_sub_cancel, Nat.add_sub_cancel]
      ring
    · rw [sval_of_heq D F (Nat.mul_assoc k N' N) s₂ s₃ he (hst χ),
        (secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 r₂ _ _ y J hJ, (secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 r₁ _ _ y J hJ,
        vu _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, hcl, Units.val_mul]
      ring
  · refine eq_zero_of_sval hL _ fun y J hJ => ?_
    rw [sval_of_heq D F (Nat.mul_assoc k N' N) s₂ s₃ he rfl]
    by_cases hb : ∃ χ', β = star a • χ'
    · obtain ⟨χ', rfl⟩ := hb
      obtain ⟨u₂, -, -, r₂⟩ := h₂.1 χ'
      rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 r₂ _ _ y J hJ,
        sval_eq_zero _ (h₁.2 χ' fun χ e => hβ χ (by rw [hst, e])), zero_mul]
    · exact sval_eq_zero _ (h₂.2 β fun χ e => hb ⟨χ, e⟩) _ _ _

end GlobalTheory
