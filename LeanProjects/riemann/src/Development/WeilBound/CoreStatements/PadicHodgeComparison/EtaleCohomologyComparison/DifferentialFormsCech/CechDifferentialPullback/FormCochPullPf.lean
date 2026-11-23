import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

theorem formCoch_pull_pf : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
    {p : Y ⟶ Spec (CommRingCat.of K)} {u : X ⟶ Y} (hu : u ≫ p = q) {κ ι : Type} (V : κ → Y.Opens) (U : ι → X.Opens)
    (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i))
    (hle : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Pb.capO U i ≤ u ⁻¹ᵁ Pb.capO V (τ ∘ i)) (a n : ℕ)
    (c : (Glob.formCos p V a).X n),
    pullCoch u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom V U τ hτ n (formCoch p V a n c) =
      formCoch q U a n (fun i => GlobalTheory.HodgeCoh.formRes q (hle i) a
        (GlobalTheory.HodgeCoh.formPull hu (Pb.capO V (τ ∘ i)) a (c (τ ∘ i)))) := by
  intro K _ X Y q p u hu κ ι V U τ hτ hle a n c
  funext i
  have key : ∀ (W : Y.Opens) (x : GlobalTheory.CechDR.OmU p W a),
      (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom.app (op W) (toOm p a W x) =
        toOm q a (u ⁻¹ᵁ W) (GlobalTheory.HodgeCoh.formPull hu W a x) :=
    fun W x => GlobalTheory.HodgeCoh.omegaPull_toOmega hu a W x
  change res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_map u.base V U τ hτ i) ((GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom.app _
      (res (modulesAb (GlobalTheory.HodgeCoh.Omega p a)).obj (inter_le_capO V (τ ∘ i)) (toOm p a (Pb.capO V (τ ∘ i)) (c (τ ∘ i))))) =
    res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_capO U i) (toOm q a (Pb.capO U i)
      (GlobalTheory.HodgeCoh.formRes q (hle i) a (GlobalTheory.HodgeCoh.formPull hu (Pb.capO V (τ ∘ i)) a (c (τ ∘ i)))))
  have e1 := app_res_map u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom (inter_le_capO V (τ ∘ i))
    (toOm p a (Pb.capO V (τ ∘ i)) (c (τ ∘ i)))
  have e2 := key (Pb.capO V (τ ∘ i)) (c (τ ∘ i))
  have e3 := toOm_formRes q a (hle i) (GlobalTheory.HodgeCoh.formPull hu (Pb.capO V (τ ∘ i)) a (c (τ ∘ i)))
  refine (congrArg (res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_map u.base V U τ hτ i))
    (e1.trans (congrArg (res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj _) e2))).trans
      (Eq.trans ?_ (congrArg (res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_capO U i)) e3).symm)
  exact (res_res _ _ _ _).trans (res_res _ _ _ _).symm

end CrystallineSemistableComparison.Om.Cech
