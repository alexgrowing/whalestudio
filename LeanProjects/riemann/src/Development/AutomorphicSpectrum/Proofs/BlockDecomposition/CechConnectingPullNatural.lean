import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechShortExactPullCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafPullConnectingCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

noncomputable section

namespace GlobalTheory.CompanionTheory.CechOne

theorem hPull_zero {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G') (s : G.obj.obj (op ⊤)) :
    hPull f φ 0 ((Sheaf.H.equiv₀ G isTerminalTop).symm s) =
      (Sheaf.H.equiv₀ G' isTerminalTop).symm
        (G'.obj.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op (φ.hom.app (op ⊤) s)) := by
  have hx : (Sheaf.H.equiv₀ G isTerminalTop).symm s =
      GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop ((GlobalTheory.SheafLES.equivZero.{0} G ⊤).symm s) := by
    rw [AddEquiv.symm_apply_eq]
    refine Eq.symm ((GlobalTheory.SiteCoh.equiv₀_terminalEquiv G isTerminalTop _).trans ?_)
    exact (GlobalTheory.SheafLES.equivZero.{0} G ⊤).apply_symm_apply s
  rw [hx, AddEquiv.eq_symm_apply]
  have h1 : hPull f φ 0 (GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop ((GlobalTheory.SheafLES.equivZero.{0} G ⊤).symm s)) =
      GlobalTheory.SiteCoh.terminalEquiv G' 0 isTerminalTop
        (pull.{0, 0} f φ 0 (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤)
          ((GlobalTheory.SheafLES.equivZero.{0} G ⊤).symm s)) := by
    simp only [hPull, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
  rw [h1]
  refine (GlobalTheory.SiteCoh.equiv₀_terminalEquiv G' isTerminalTop _).trans ?_
  refine (SheafPull.equivZero_pull f φ (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤) _).trans ?_
  rw [AddEquiv.apply_symm_apply]

theorem pullCoch_globalCocycle {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q)
    {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (s : P.obj (op ⊤)) :
    pullCoch f φ V U τ hτ 0 (globalCocycle P V s).1 =
      (globalCocycle Q U (Q.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op
        (φ.app (op ⊤) s))).1 := by
  funext t
  change res Q (inter_le_map f V U τ hτ t) (φ.app (op (inter V (τ ∘ t))) (res P _ s)) =
    res Q _ (Q.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op (φ.app (op ⊤) s))
  rw [app_res_map, res_res]
  change _ = res Q _ (res Q _ (φ.app (op ⊤) s))
  rw [res_res]

theorem cechHOneEquiv_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)} (hS : S.ShortExact) [Injective S.X₂]
    (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : GroundTheory.Arith.SchemeCoh.CechAcyclic S.X₂.obj V) (hS' : S'.ShortExact) [Injective S'.X₂]
    (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : GroundTheory.Arith.SchemeCoh.CechAcyclic S'.X₂.obj U) (α : S ⟶ S'.map (push f))
    (x : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V 1) :
    (cechHOneEquiv U hU hS' hC' hI' : GroundTheory.Arith.SchemeCoh.cechH S'.X₁.obj U 1 ≃+ Sheaf.H.{0} S'.X₁ 1) (cechPullH f α.τ₁.hom V U τ hτ 1 x) =
      hPull f α.τ₁ 1 ((cechHOneEquiv V hV hS hC hI : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V 1 ≃+ Sheaf.H.{0} S.X₁ 1) x) := by
  obtain ⟨s, rfl⟩ := cechOneProj_surjective V hV hC hI x
  have h₁₂ : ∀ W y, α.τ₂.hom.app W (S.f.hom.app W y) = S'.f.hom.app _ (α.τ₁.hom.app W y) := fun W y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun g => g.hom) α.comm₁₂.symm) W) y
  have h₂₃ : ∀ W y, α.τ₃.hom.app W (S.g.hom.app W y) = S'.g.hom.app _ (α.τ₂.hom.app W y) := fun W y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun g => g.hom) α.comm₂₃.symm) W) y
  have hmap : cechPullH f α.τ₁.hom V U τ hτ 1 (cechOneProj V hC s) =
      cechOneProj U hC' (S'.X₃.obj.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op
        (α.τ₃.hom.app (op ⊤) s)) := by
    change cechPullH f α.τ₁.hom V U τ hτ (0 + 1) (hC.delta 0 (globalCocycle S.X₃.obj V s)) =
      hC'.delta 0 (globalCocycle S'.X₃.obj U _)
    refine (GlobalTheory.T.cech_short_exact_pull_compat f V U τ hτ hC hC' α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃ 0 _).trans ?_
    exact congrArg (hC'.delta 0) (Subtype.ext (pullCoch_globalCocycle f α.τ₃.hom V U τ hτ s))
  rw [hmap, cechHOneEquiv_cechOneProj, cechHOneEquiv_cechOneProj]
  change H.δ hS' 0 1 rfl ((Sheaf.H.equiv₀ S'.X₃ isTerminalTop).symm _) =
    hPull f α.τ₁ 1 (H.δ hS 0 1 rfl ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm s))
  rw [GlobalTheory.T.sheaf_pull_connecting_compat f hS hS' α 0 _]
  exact congrArg (H.δ hS' 0 1 rfl) (hPull_zero f α.τ₃ s).symm

end GlobalTheory.CompanionTheory.CechOne
