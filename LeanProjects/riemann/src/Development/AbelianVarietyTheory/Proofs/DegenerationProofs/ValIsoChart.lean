import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex.Arch
open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

theorem val_iso_chart {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} (hL' : L'.IsLB) {F : X' ⟶ X}
    {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (x : Sp ℂ ⟶ X') (j j' : L.ι) (i : L'.ι)
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j') (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) :
    valAt' x _ (w.s (fun _ => j, i)).val =
      valAt' (x ≫ F) (L.U j ⊓ L.U j') (L.g j j').val * valAt' x _ (w.s (fun _ => j', i)).val := by
  have a : ⊤ ≤ x ⁻¹ᵁ L.wchart (fun _ : PUnit => F) (fun _ => j) := (le_preimage_wchart x L _ _).2 fun _ => hj
  have a' : ⊤ ≤ x ⁻¹ᵁ L.wchart (fun _ : PUnit => F) (fun _ => j') := (le_preimage_wchart x L _ _).2 fun _ => hj'
  have b := (le_preimage_inf x _ _).2 ⟨a, hi⟩
  have b' := (le_preimage_inf x _ _).2 ⟨a', hi⟩
  have c := (le_preimage_inf x _ _).2 ⟨b, b'⟩
  refine (val_sec x (genSec w hw) (fun _ => j, i) (fun _ => j', i) b b').trans (congrArg₂ (· * ·) ?_ rfl)
  have e₁ := val_linComb x valueRules L (fun _ : PUnit => F) (fun _ => 1) (fun _ => j) (fun _ => j') a a'
  rw [Fintype.prod_unique, zpow_one] at e₁
  have e₂ : valAt' x (L'.U i ⊓ L'.U i) (L'.g i i).val = 1 := by
    obtain ⟨e, he⟩ := (valueRules X' x).2.1 _ hi
    rw [← val_res x valueRules (le_inf le_rfl le_rfl) hi, hL'.g_self i, he]
    exact map_one e
  obtain ⟨e, he⟩ := (valueRules X' x).2.1 _ c
  refine (val_unit_mul x valueRules c _ _).trans ?_
  refine (congrArg₂ (· * ·) ((val_res x valueRules _ c _).trans e₁) ((he _).trans ((map_units_inv e _).trans
    (congrArg (·⁻¹) ((he _).symm.trans ((val_res x valueRules _ c _).trans e₂)))))).trans ?_
  simp

theorem fibSec : FibSecSt := by
  intro R _ _ _ D J g Λ Hm χ ex fr h s
  obtain ⟨hJ, P', φ, w, u, hΛ, -, hw, -, -, -, -, hex, hfr⟩ := h
  refine ⟨fun z => sF s (ex z).left J / fr z, fun z₀ => ?_, fun z => (div_mul_cancel₀ _ (fr z).ne_zero).symm⟩
  obtain ⟨i, hi⟩ : ∃ i, ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ P'.L.U i := ⟨_, le_chartAt P'.isLB _⟩
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ ((u.ex z₀).left ≫ φ) ⁻¹ᵁ D.P.L.U j := ⟨_, hJ _⟩
  have ch : ∀ (y : Sp ℂ ⟶ D.P.A.left) (k : D.P.L.ι), ⊤ ≤ y ⁻¹ᵁ D.P.L.U k →
      ⊤ ≤ y ⁻¹ᵁ D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => k) := fun y k hk =>
    (le_preimage_wchart y _ _ _).2 fun _ => by rwa [Category.comp_id]
  have a : ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ (D.P.L.wchart (fun _ : PUnit => φ) (fun _ => j) ⊓ P'.L.U i) :=
    (le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hj, hi⟩
  obtain ⟨o₁, d₁⟩ := u.hol (φ ⁻¹ᵁ D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => j))
    ((φ.app _).hom (s.f fun _ => j))
  obtain ⟨o₂, d₂⟩ := u.hol _ (w.s (fun _ => j, i)).val
  have n₂ := o₂.mem_nhds a
  have d := (d₁.differentiableAt (o₁.mem_nhds (ch _ j hj))).fun_mul (((d₂.differentiableAt n₂).fun_mul
    ((u.fr_hol i).differentiableAt ((u.hol _ 0).1.mem_nhds hi))).fun_inv
    (mul_ne_zero (val_unit_ne_zero _ valueRules a _) (u.fr_ne i _ hi)))
  refine d.congr_of_eventuallyEq ?_
  filter_upwards [n₂] with z hz
  obtain ⟨h₁, h₂⟩ := (le_preimage_inf _ _ _).1 hz
  have h₃ := (le_preimage_wchart _ _ _ _).1 h₁ PUnit.unit
  have e₀ : sF s (ex z).left J = valAt' (ex z).left _ (s.f fun _ => J (ex z).left) := by
    rfl
  have e₁ := val_sec (ex z).left s (fun _ => J (ex z).left) (fun _ => j) (ch _ _ (hJ _)) (ch _ _ (hex z ▸ h₃))
  have e₂ := val_linComb (ex z).left valueRules D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => ((1 : ℕ) : ℤ))
    (fun _ => J (ex z).left) (fun _ => j) (ch _ _ (hJ _)) (ch _ _ (hex z ▸ h₃))
  rw [Fintype.prod_unique, Nat.cast_one, zpow_one, Category.comp_id] at e₂
  have e₃ := val_iso_chart P'.isLB hw (u.ex z).left (J (ex z).left) j i (hex z ▸ hJ _) h₃ h₂
  have n := val_unit_ne_zero (ex z).left valueRules ((le_preimage_inf _ _ _).2 ⟨hJ _, hex z ▸ h₃⟩)
    (D.P.L.g (J (ex z).left) j)
  have e₄ := (valueRules _ (u.ex z).left).2.2.2.1 _ φ _ (s.f fun _ => j)
  rw [← hex z] at e₃ e₄
  rw [e₀, e₁, hfr z i h₂, e₃, _root_.mul_assoc]
  exact (congrArg (fun q => q * _ / _) e₂).trans ((mul_div_mul_left _ _ n).trans ((div_eq_mul_inv _ _).trans
    (congrArg₂ (· * ·) e₄.symm rfl)))

end GlobalTheory.Ex.Arch
end
