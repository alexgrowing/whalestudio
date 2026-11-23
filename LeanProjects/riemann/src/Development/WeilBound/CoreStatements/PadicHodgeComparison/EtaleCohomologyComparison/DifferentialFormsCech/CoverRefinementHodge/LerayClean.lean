import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.ZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveResolutionLiftPushforwardStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.CechHStepPull

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Nt2

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison.Om.Cech

theorem cechHEquiv_pull_compat {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) :
    ∀ (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : cechH G.obj V n ≃+ Sheaf.H.{0} G n) x)
  | 0, G, G', hG, hG', φ, x => CrystallineSemistableComparison.Om.Nt2.cechHZero_pull' f V hV U hU τ hτ φ x
  | 1, G, G', hG, hG', φ, x => by
    obtain ⟨α, rfl⟩ := GlobalTheory.T.injective_resolution_lift_pushforward f φ
    exact CrystallineSemistableComparison.Om.Nt2.cechHOne_pull' f V hV U hU τ hτ (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact hCY V hVB G hG) (injectiveSequence_cechAcyclic G V)
      (injectiveSequence_shortExact G') (injectiveSequence_isCechShortExact hCX U hUB G' hG')
      (injectiveSequence_cechAcyclic G' U) α x
  | m + 2, G, G', hG, hG', φ, x => by
    obtain ⟨α, rfl⟩ := GlobalTheory.T.injective_resolution_lift_pushforward f φ
    exact CrystallineSemistableComparison.Om.Nt2.cechHStep_pull' f V U τ hτ (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact hCY V hVB G hG) (injectiveSequence_cechAcyclic G V)
      (injectiveSequence_shortExact G') (injectiveSequence_isCechShortExact hCX U hUB G' hG')
      (injectiveSequence_cechAcyclic G' U) α m _ _
      (fun y => cechHEquiv_pull_compat f hCY hCX V hV hVB U hU hUB τ hτ (m + 1)
        (injectiveSequence_goodAcyclic hCY G hG) (injectiveSequence_goodAcyclic hCX G' hG') α.τ₃ y) x

theorem cechHEquiv_pullC : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : cechH G.obj V n ≃+ Sheaf.H.{0} G n) x) := by
  intro X Y f BY GoodY BX GoodX hCY hCX κ ι V hV hVB U hU hUB τ hτ n G G' hG hG' φ x
  exact cechHEquiv_pull_compat f hCY hCX V hV hVB U hU hUB τ hτ n hG hG' φ x

end CrystallineSemistableComparison.Om.Nt2
