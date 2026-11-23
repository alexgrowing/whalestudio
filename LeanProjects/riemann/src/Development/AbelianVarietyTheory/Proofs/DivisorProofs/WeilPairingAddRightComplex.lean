import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionGeneratorsRational
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.WeilEqAdd

theorem weilIs_mul_right {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S} (x y y' : T ⟶ P.A)
    (c c' : Γ(T.left, ⊤)ˣ) (h : Out.WeilIs P.A P.L k x y c) (h' : Out.WeilIs P.A P.L k x y' c') :
    Out.WeilIs P.A P.L k x (y * y') (c * c') := by
  have h₁ := GlobalTheory.CommPairing.weilIs_symm P.isLB h
  have h₂ := GlobalTheory.CommPairing.weilIs_symm P.isLB h'
  have h₃ := GlobalTheory.CommPairing.weilIs_symm P.isLB
    (GlobalTheory.weilIs_mul_left GlobalTheory.globalFns_holds S P k T y y' x _ _ h₁ h₂)
  have e : (c⁻¹ * c'⁻¹)⁻¹ = c * c' := by rw [mul_inv, inv_inv, inv_inv, mul_comm]
  rwa [e] at h₃

end GlobalTheory.WeilEqAdd

namespace GlobalTheory

open WeilEqAdd in

theorem weilEq_mul_right_add : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f g₁ g₂ : A.t.G ⟶ B.t.G), IsMonHom f → IsMonHom g₁ →
    IsMonHom g₂ → ∀ r₁ r₂ : 𝓞 E,
    WeilEq B.t.PP.L f g₁ A.t.PP.L (A.t.act.act r₁) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f g₂ A.t.PP.L (A.t.act.act r₂) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f (g₁ * g₂) A.t.PP.L (A.t.act.act (r₁ + r₂)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ σ₁ A B f g₁ g₂ _ _ _ r₁ r₂ h₁ h₂ n x y c hn hx hy
  haveI : IsCommMonObj A.pol.A := A.ab.comm
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have ex : ∀ r : 𝓞 E, ∃ u : ℂˣ,
      Out.WeilIs A.t.G A.t.PP.L n (x ≫ A.t.act.act r) (y ≫ 𝟙 _) (unitOn u) := by
    intro r
    haveI := A.t.act.hom r
    have hxr : (x ≫ A.t.act.act r) ^ n = 1 := by
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    have hy' : (y ≫ 𝟙 _) ^ n = 1 := by rw [Category.comp_id]; exact hy
    exact GlobalTheory.TorsionGenerators.exists_weilIs hL A.pol (σ₁.comp (algebraMap (𝓞 K) K)) hxr hy'
  have um : ∀ a b : ℂˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul (Units.map _) a b
  obtain ⟨c₁, e₁⟩ := ex r₁
  obtain ⟨c₂, e₂⟩ := ex r₂
  have hA : Out.WeilIs A.t.G A.t.PP.L n (x ≫ A.t.act.act (r₁ + r₂)) (y ≫ 𝟙 _) (unitOn (c₁ * c₂)) := by
    rw [A.t.act.add, MonObj.comp_mul, um]
    exact GlobalTheory.weilIs_mul_left GlobalTheory.globalFns_holds _ A.pol n _ _ _ _ _ _ e₁ e₂
  have hB : Out.WeilIs B.t.G B.t.PP.L n (x ≫ f) (y ≫ (g₁ * g₂)) (unitOn (c₁ * c₂)) := by
    rw [MonObj.comp_mul, um]
    exact weilIs_mul_right B.pol n _ _ _ _ _ ((h₁ n x y c₁ hn hx hy).2 e₁) ((h₂ n x y c₂ hn hx hy).2 e₂)
  constructor
  · intro h
    obtain rfl := GlobalTheory.weilIs_unique_fieldPoint _ _ _ B.t.PP.isLB _ _ _ _ _ _ _ h hB
    exact hA
  · intro h
    obtain rfl := GlobalTheory.weilIs_unique_fieldPoint _ _ _ A.t.PP.isLB _ _ _ _ _ _ _ h hA
    exact hB

end GlobalTheory
