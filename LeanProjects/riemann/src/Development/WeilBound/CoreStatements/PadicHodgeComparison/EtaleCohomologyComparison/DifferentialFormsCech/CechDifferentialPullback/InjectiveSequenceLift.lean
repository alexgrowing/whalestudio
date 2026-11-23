import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

theorem cechOmAdd_smul (h : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a)))
    (a j : ℕ) (r : K) (x : CO q U a j), cechOmAdd q U hU hUaff a j (r • x) = r • cechOmAdd q U hU hUaff a j x) : type_of% @h := @h

theorem cechOm_pull (h : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q) {κ ι : Type} (V : κ → Y.Opens) (hV : iSup V = ⊤)
    (hVaff : ∀ (n : ℕ) (i : Fin (n + 1) → κ), IsAffineOpen (⨅ a, V (i a))) (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i))
    (a j : ℕ) (x : CO p V a j),
    cechOmAdd q U hU hUaff a j (cechPull hu V U τ hτ a j x) = pullC u hu a j (cechOmAdd p V hV hVaff a j x)) : type_of% @h := @h

theorem formToCO_bijective (h : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a j : ℕ),
    Function.Bijective (formToCO q U a j)) : type_of% @h := @h

theorem formToCO_smul (h : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (a j : ℕ) (r : K) (x : (Glob.formCos q U a).cx.H j),
    formToCO q U a j (r • x) = r • formToCO q U a j x) : type_of% @h := @h

theorem formCoch_pull (h : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
    {p : Y ⟶ Spec (CommRingCat.of K)} {u : X ⟶ Y} (hu : u ≫ p = q) {κ ι : Type} (V : κ → Y.Opens) (U : ι → X.Opens)
    (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i))
    (hle : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Pb.capO U i ≤ u ⁻¹ᵁ Pb.capO V (τ ∘ i)) (a n : ℕ)
    (c : (Glob.formCos p V a).X n),
    pullCoch u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom V U τ hτ n (formCoch p V a n c) =
      formCoch q U a n (fun i => GlobalTheory.HodgeCoh.formRes q (hle i) a
        (GlobalTheory.HodgeCoh.formPull hu (Pb.capO V (τ ∘ i)) a (c (τ ∘ i))))) : type_of% @h := @h

end CrystallineSemistableComparison.Om.Cech
