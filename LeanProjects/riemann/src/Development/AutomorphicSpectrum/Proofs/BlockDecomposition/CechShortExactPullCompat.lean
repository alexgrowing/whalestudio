import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCechDelta

theorem app_res_nat {X : TopCat.{0}} {Q Q₂ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (a : Q ⟶ Q₂)
    {A B : Opens X} (h : A ≤ B) (x : Q.obj (op B)) :
    a.app (op A) (res Q h x) = res Q₂ h (a.app (op B) x) := by
  exact NatTrans.naturality_apply a (homOfLE h).op x

theorem push_pullCoch {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X)
    (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {P P₂ : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}} {Q Q₂ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    (a : P ⟶ P₂) (a' : Q ⟶ Q₂) (φ : P ⟶ (Opens.map f).op ⋙ Q) (φ₂ : P₂ ⟶ (Opens.map f).op ⋙ Q₂)
    (h : ∀ W x, φ₂.app W (a.app W x) = a'.app _ (φ.app W x)) (n : ℕ) (σ : Cochain P V n) :
    push U a' n (pullCoch f φ V U τ hτ n σ) = pullCoch f φ₂ V U τ hτ n (push V a n σ) := by
  funext t
  exact (app_res_nat a' _ _).trans (congrArg (res Q₂ _) (h _ _).symm)

theorem cechPullH_delta : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {F I Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {F' I' Q' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} {g₁ : F ⟶ I} {g₂ : I ⟶ Q} {g₁' : F' ⟶ I'} {g₂' : I' ⟶ Q'}
    (hC : IsCechShortExact V g₁ g₂) (hC' : IsCechShortExact U g₁' g₂') (φ₁ : F ⟶ (Opens.map f).op ⋙ F')
    (φ₂ : I ⟶ (Opens.map f).op ⋙ I') (φ₃ : Q ⟶ (Opens.map f).op ⋙ Q')
    (h₁₂ : ∀ W x, φ₂.app W (g₁.app W x) = g₁'.app _ (φ₁.app W x))
    (h₂₃ : ∀ W x, φ₃.app W (g₂.app W x) = g₂'.app _ (φ₂.app W x)) (n : ℕ) (σ : cocycles Q V n),
    cechPullH f φ₁ V U τ hτ (n + 1) (hC.delta n σ) =
      hC'.delta n ⟨pullCoch f φ₃ V U τ hτ n σ.1, pullCoch_mem_cocycles f φ₃ V U τ hτ σ.2⟩ := by
  intro X Y f κ ι V U τ hτ F I Q F' I' Q' g₁ g₂ g₁' g₂' hC hC' φ₁ φ₂ φ₃ h₁₂ h₂₃ n σ
  obtain ⟨t, ρ, hρ, ht, hρt, hc⟩ := hC.delta_spec n σ
  have h1 : push U g₂' n (pullCoch f φ₂ V U τ hτ n t) = pullCoch f φ₃ V U τ hτ n σ.1 := by
    rw [push_pullCoch f V U τ hτ g₂ g₂' φ₂ φ₃ h₂₃ n t, ht]
  have h2 : push U g₁' (n + 1) (pullCoch f φ₁ V U τ hτ (n + 1) ρ) =
      d I' U n (pullCoch f φ₂ V U τ hτ n t) := by
    rw [push_pullCoch f V U τ hτ g₁ g₁' φ₁ φ₂ h₁₂ (n + 1) ρ, hρt, pullCoch_d]
  have h3 : d F' U (n + 1) (pullCoch f φ₁ V U τ hτ (n + 1) ρ) = 0 := by
    rw [← pullCoch_d, hρ, map_zero]
  rw [hc, cechPullH_cls]
  exact hC'.deltaRel_unique ⟨pullCoch f φ₂ V U τ hτ n t, pullCoch f φ₁ V U τ hτ (n + 1) ρ, h3, h1, h2, rfl⟩
    (hC'.delta_spec n ⟨pullCoch f φ₃ V U τ hτ n σ.1, pullCoch_mem_cocycles f φ₃ V U τ hτ σ.2⟩)

end GlobalTheory.CompanionTheory.OmCechDelta
