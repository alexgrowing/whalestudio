import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveResolutionLiftPushforward
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechH0PullCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechConnectingPullNaturalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechSheafCohomologyPullCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechLerayPull

theorem cechHEquiv_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) : ∀ (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : GroundTheory.Arith.SchemeCoh.cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : GroundTheory.Arith.SchemeCoh.cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : GroundTheory.Arith.SchemeCoh.cechH G.obj V n ≃+ Sheaf.H.{0} G n) x)
  | 0, G, G', _, _, φ, x => GlobalTheory.T.cech_h0_pull_compat f V hV U hU τ hτ φ x
  | 1, G, G', hG, hG', φ, x => by
      obtain ⟨α, rfl⟩ := GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift f φ
      exact GlobalTheory.T.cech_connecting_pull_natural f V hV U hU τ hτ (S := injectiveSequence G) (S' := injectiveSequence G')
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact hCY V hVB G hG)
        (injectiveSequence_cechAcyclic G V) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact hCX U hUB G' hG') (injectiveSequence_cechAcyclic G' U) α x
  | m + 2, G, G', hG, hG', φ, x => by
      obtain ⟨α, rfl⟩ := GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift f φ
      exact GlobalTheory.T.cech_sheaf_cohomology_pull_compat f V U τ hτ (S := injectiveSequence G) (S' := injectiveSequence G')
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact hCY V hVB G hG)
        (injectiveSequence_cechAcyclic G V) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact hCX U hUB G' hG') (injectiveSequence_cechAcyclic G' U) α m _ _
        (fun y => cechHEquiv_pull f hCY hCX V hV hVB U hU hUB τ hτ (m + 1) _ _ α.τ₃ y) x

end GlobalTheory.CompanionTheory.CechLerayPull
