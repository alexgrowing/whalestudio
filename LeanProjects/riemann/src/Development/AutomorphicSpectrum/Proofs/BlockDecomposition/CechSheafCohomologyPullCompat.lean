import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechShortExactPullCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafPullConnectingCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechStep

theorem cechHEquivStep_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) [Injective S.X₂] (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : GroundTheory.Arith.SchemeCoh.CechAcyclic S.X₂.obj V)
    (hS' : S'.ShortExact) [Injective S'.X₂] (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : GroundTheory.Arith.SchemeCoh.CechAcyclic S'.X₂.obj U)
    (α : S ⟶ S'.map (push f)) (m : ℕ) (e : GroundTheory.Arith.SchemeCoh.cechH S.X₃.obj V (m + 1) ≃+ Sheaf.H.{0} S.X₃ (m + 1))
    (e' : GroundTheory.Arith.SchemeCoh.cechH S'.X₃.obj U (m + 1) ≃+ Sheaf.H.{0} S'.X₃ (m + 1))
    (he : ∀ y, e' (cechPullH f α.τ₃.hom V U τ hτ (m + 1) y) = hPull f α.τ₃ (m + 1) (e y))
    (x : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V (m + 2)) :
    cechHEquivStep U hS' hC' hI' m e' (cechPullH f α.τ₁.hom V U τ hτ (m + 2) x) =
      hPull f α.τ₁ (m + 2) (cechHEquivStep V hS hC hI m e x) := by
  have h₁₂ : ∀ W z, α.τ₂.hom.app W (S.f.hom.app W z) =
      S'.f.hom.app ((Opens.map f).op.obj W) (α.τ₁.hom.app W z) := fun W z => by
    have h := congrArg (fun k => k.hom.app W) α.comm₁₂
    exact (ConcreteCategory.congr_hom h z).symm
  have h₂₃ : ∀ W z, α.τ₃.hom.app W (S.g.hom.app W z) =
      S'.g.hom.app ((Opens.map f).op.obj W) (α.τ₂.hom.app W z) := fun W z => by
    have h := congrArg (fun k => k.hom.app W) α.comm₂₃
    exact (ConcreteCategory.congr_hom h z).symm
  obtain ⟨y, rfl⟩ := (hC.deltaEquiv hI m).surjective x
  have hδ : (hC'.deltaEquiv hI' m).symm (cechPullH f α.τ₁.hom V U τ hτ (m + 2) (hC.deltaEquiv hI m y)) =
      cechPullH f α.τ₃.hom V U τ hτ (m + 1) y := by
    rw [AddEquiv.symm_apply_eq]
    obtain ⟨σ, hσ, rfl⟩ := GroundTheory.Arith.SchemeCoh.exists_cls y
    exact (GlobalTheory.T.cech_short_exact_pull_compat f V U τ hτ hC hC' α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃ (m + 1)
      ⟨σ, (GroundTheory.Arith.SchemeCoh.mem_cocycles σ).2 hσ⟩).trans rfl
  simp only [cechHEquivStep, AddEquiv.trans_apply, AddEquiv.symm_apply_apply, hδ, he]
  exact (GlobalTheory.T.sheaf_pull_connecting_compat f hS hS' α (m + 1) (e y)).symm

end GlobalTheory.CompanionTheory.CechStep
