import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechShortExactPullCompat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_short_exact_pull_compat : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {F I Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {F' I' Q' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} {g₁ : F ⟶ I} {g₂ : I ⟶ Q} {g₁' : F' ⟶ I'} {g₂' : I' ⟶ Q'}
    (hC : IsCechShortExact V g₁ g₂) (hC' : IsCechShortExact U g₁' g₂') (φ₁ : F ⟶ (Opens.map f).op ⋙ F')
    (φ₂ : I ⟶ (Opens.map f).op ⋙ I') (φ₃ : Q ⟶ (Opens.map f).op ⋙ Q')
    (h₁₂ : ∀ W x, φ₂.app W (g₁.app W x) = g₁'.app _ (φ₁.app W x))
    (h₂₃ : ∀ W x, φ₃.app W (g₂.app W x) = g₂'.app _ (φ₂.app W x)) (n : ℕ) (σ : cocycles Q V n),
    cechPullH f φ₁ V U τ hτ (n + 1) (hC.delta n σ) =
      hC'.delta n ⟨pullCoch f φ₃ V U τ hτ n σ.1, pullCoch_mem_cocycles f φ₃ V U τ hτ σ.2⟩ := by
  first | exact @GlobalTheory.CompanionTheory.OmCechDelta.cechPullH_delta | exact GlobalTheory.CompanionTheory.OmCechDelta.cechPullH_delta | (intros; apply GlobalTheory.CompanionTheory.OmCechDelta.cechPullH_delta <;> assumption)
