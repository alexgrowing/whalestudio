import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

lemma restrictTop_top_self {X : Scheme.{0}} (r : Γ(X, ⊤)) : restrictTop (⊤ : X.Opens) r = r := by
  change (X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op).hom r = r
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, X.presheaf.map_id]
  rfl

lemma twist_map_comp_app {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {F G K : X.Modules}
    (φ : F ⟶ G) (ψ : G ⟶ K) (V : X.Opens) (s : Γ(GlobalTheory.twist F L, V)) :
    (GlobalTheory.Twist.map L (φ ≫ ψ)).app V s = (GlobalTheory.Twist.map L ψ).app V ((GlobalTheory.Twist.map L φ).app V s) := by
  rw [GlobalTheory.Twist.map_comp]
  rfl

lemma smul_mem_twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (e : ℕ) {a : A} (ha : a ∈ I)
    {m : Γ(GlobalTheory.twistZ P H n, ⊤)} (hm : m ∈ twPow I H n P e) :
    toFunctions (X := X) (A := A) ⊤ a • m ∈ twPow I H n P (e + 1) := by
  have hm' : m ∈ (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ e) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) := hm
  change _ ∈ (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤))
  have hmem : toFunctions (X := X) (A := A) ⊤ a ∈ Ideal.map (toFunctions (X := X) (A := A) ⊤) I :=
    Ideal.mem_map_of_mem _ ha
  rw [pow_succ', Ideal.map_mul, mul_smul]
  exact Submodule.smul_mem_smul hmem hm'

theorem lifts_succ : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A), (∀ i, g i ∈ I) → ∀ (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (n : ℤ) (e : ℕ), Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) = ⊤ → Lifts I H hS n e → Lifts I H hS n (e + 1) := by
  intro A _ _ I X _ H P S hS k g hg hr n e hspan hL y
  have hy : y ∈ Submodule.span Γ(X, ⊤) (⋃ i, Set.range
      ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) := by
    rw [hspan]; trivial
  have hsub : ∀ m : ℕ, ∀ a b : Γ(GlobalTheory.twistZ P H n, ⊤), a ∈ twPow I H n P m → b ∈ twPow I H n P m →
      a + b ∈ twPow I H n P m := fun m a b ha hb =>
    Submodule.add_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) ha hb
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, y', rfl⟩ := Set.mem_iUnion.1 hy
    obtain ⟨c', rfl, hc'⟩ := hL y'
    refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (mulLvl (hr i) e)).app ⊤ c', ?_, ?_⟩
    · rw [← twist_map_comp_app, ← twist_map_comp_app, grπ_grT]
    · rw [← twist_map_comp_app, mulLvl_arrow, twist_map_comp_app, twist_smulHom_app,
        restrictTop_top_self]
      exact smul_mem_twPow I H n P e (hg i) hc'
  | zero =>
    refine ⟨0, map_zero _, ?_⟩
    rw [map_zero]
    exact Submodule.zero_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤))
  | add x y _ _ hx hy =>
    obtain ⟨c₁, rfl, h₁⟩ := hx
    obtain ⟨c₂, rfl, h₂⟩ := hy
    refine ⟨c₁ + c₂, map_add _ _ _, ?_⟩
    rw [map_add]
    exact hsub _ _ _ h₁ h₂
  | smul a x _ hx =>
    obtain ⟨c, rfl, h⟩ := hx
    refine ⟨a • c, Scheme.Modules.Hom.app_smul _ _ _, ?_⟩
    rw [Scheme.Modules.Hom.app_smul]
    exact Submodule.smul_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) a h

end GlobalTheory.CompanionTheory.GE.Step
