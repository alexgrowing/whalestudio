import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pullAl_value_integral_point :
    Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)), PullAl D F oa a k N s s' → ∀ (χ : D.toPre.X) (m : TWM.TO hϖ hv ⟶ D.toPre.P.A) (r : ℚ), (∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => (m ≫ oa.onB.act a).left ≫ DegPre.famφB D.toPre (χ) i) (DegPre.famε (k))), G₀.IsGen ∧ ∃ x : F, v x = ((r : ℚ) : WithTop ℚ) ∧ ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J → sval (s.s χ) (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m ≫ oa.onB.act a)).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) * (val G₀ (TWM.ιS hϖ hv).left z J).val) → (∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => (m).left ≫ DegPre.famφB D.toPre (star a • χ) i) (DegPre.famε (k * N))), G₀.IsGen ∧ ∃ x : F, v x = ((r : ℚ) : WithTop ℚ) ∧ ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J → sval (s'.s (star a • χ)) (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) * (val G₀ (TWM.ιS hϖ hv).left z J).val) := by
  intro hLaws V _ _ _ ϖ hϖ D Q _ F _ _ _ v hv O _ _ _ oa w0 hw a N k hN _ haa s s' hpull χ m r ⟨G₀, hG₀, x, hx, hval⟩
  have hL := D.toPre.P.isLB
  obtain ⟨u, hu, hcorr, hrel⟩ := hpull.1 χ
  obtain ⟨n, ψ, δ, eB, heB, hform, ve⟩ :=
    pullGen_one hLaws.globalFns D F oa w0 hw a N hN (by rw [mul_comm]; exact haa) k χ u hu hcorr
  have hform' : FormEq (Sum.elim (fun i => (m ≫ oa.onB.act a).left ≫ DegPre.famφB D.toPre χ i)
      (fun i => m.left ≫ ψ i)) (Sum.elim (DegPre.famε k) δ)
      (fun i => m.left ≫ DegPre.famφB D.toPre (star a • χ) i) (DegPre.famε (k * N)) := fun U _ h => by
    refine Eq.trans ?_ (hform U (fun q => h (m.left ≫ q)))
    refine Finset.prod_congr rfl ?_
    rintro (i | i) -
    · simp only [Sum.elim_inl, Over.comp_left, Category.assoc]
    · rfl
  obtain ⟨G₁, hG₁, vG⟩ := exists_gen hL hform'
    (LB.mulGen D.toPre.P.L _ _ _ _ G₀ (LB.pullGen D.toPre.P.L _ _ eB m.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hG₀ (DVR.pullGen_isGen _ _ _ _ heB _))
  refine ⟨G₁, hG₁, x, hx, fun z J hJ => ?_⟩
  have H := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _
    (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left z J hJ
  have e₁ : (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left ≫ (aF D F oa a).left =
      (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m ≫ oa.onB.act a)).left := by
    rw [← Over.comp_left, aF, comp_lift, lift_fst, ← Category.assoc, lift_snd, Category.assoc]
  have e₂ : (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left ≫ (DegPre.prB D.toPre F).left =
      (TWM.ιS hϖ hv).left ≫ m.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  rw [H, e₁, hval z J hJ, ve _ _ z J hJ, e₂, vG _ _ z J hJ, val_mul hJ, val_pull hJ, Units.val_mul, _root_.mul_assoc]

end GlobalTheory
