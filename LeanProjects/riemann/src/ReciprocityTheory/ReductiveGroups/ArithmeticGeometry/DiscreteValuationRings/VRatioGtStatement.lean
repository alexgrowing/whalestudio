import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LiftOUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation QForm

def VRatioGtStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v)
      (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (m : TO hϖ hv ⟶ D.toPre.P.A), ιS hϖ hv ≫ m = p.g.b →
      ∀ (α : D.toPre.X) (G₀ : LB.Gen (LB.LinComb D.toPre.P.L (gtφO hϖ hv m α) DegPre.gtε)), G₀.IsGen → ∀ t : F,
      (∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
        (val (p.g.s α) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
          (val G₀ (r ≫ (ιS hϖ hv).left) z J).val) →
      ∃ q : ℚ, v t = (q : WithTop ℚ) ∧ (k : ℚ) * q = bOf D.toPre Q p.y α

section Ratio

variable {V : Type} [CommRing V] [IsDomain V] {F : Type} [Field F] [Algebra (FractionRing V) F] {X : Scheme.{0}}
  {L : LB X}

theorem exists_ratio (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Spec (CommRingCat.of F) ⟶ X)}
    {ε : K → ℤ} {φ' : K' → (Spec (CommRingCat.of F) ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb L φ' ε')) (ht' : t'.IsGen) (hf : FormEq φ ε φ' ε') :
    ∃ c : F, c ≠ 0 ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (J), Good L z J →
      (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * (val t' r z J).val := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of F)))) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (Spec (CommRingCat.of F))) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const L hL (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ t')) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ ht'))
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hf U h, mul_inv_cancel])
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (J), Good L z J →
      (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * (val t' r z J).val := by
    intro Z r z J hJ
    have e := ha Z r z J hJ
    rw [val_mul hJ, val_inv, Category.comp_id, ← hc] at e
    rw [← e, Units.val_mul, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]
  refine ⟨c, ?_, key⟩
  rintro rfl
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  choose I hI' using fun χ : Spec (CommRingCat.of F) ⟶ X => exists_chart hL (χ z)
  have e := key _ (𝟙 _) z I hI'
  have g0 : gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom 0) = 0 := by
    rw [map_zero]
    have := gs_add (𝟙 (Spec (CommRingCat.of F))) z ⊤ trivial (0 : Γ(Spec (CommRingCat.of F), ⊤)) 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  rw [g0, MulZeroClass.zero_mul] at e
  exact Units.ne_zero _ e

end Ratio

section Main

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem trO_one : trO hϖ hv (D := D) 1 = 𝟙 _ := by
  unfold trO
  rw [MonObj.comp_one, padd, ← Hom.mul_def, _root_.mul_one, lift_fst_snd]

theorem trO_mul (m m' : TO hϖ hv ⟶ D.toPre.P.A) : trO hϖ hv m ≫ trO hϖ hv m' = trO hϖ hv (m * m') := by
  unfold trO
  simp only [padd, ← Hom.mul_def, comp_lift, lift_fst, lift_snd, MonObj.comp_mul, lift_fst_assoc]
  rw [_root_.mul_assoc]

theorem wt_coe_of_ne {x : F} (hx : x ≠ 0) : ∃ q : ℚ, v x = (q : WithTop ℚ) := by
  have h : v x ≠ ⊤ := fun h => hx ((AddValuation.top_iff v).mp h)
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp h
  exact ⟨q, hq.symm⟩

theorem v_inv_coe {x : F} (hx : x ≠ 0) {q : ℚ} (hq : v x = q) : v x⁻¹ = ((-q : ℚ) : WithTop ℚ) := by
  rw [AddValuation.map_inv, hq]
  rfl

end Main

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
