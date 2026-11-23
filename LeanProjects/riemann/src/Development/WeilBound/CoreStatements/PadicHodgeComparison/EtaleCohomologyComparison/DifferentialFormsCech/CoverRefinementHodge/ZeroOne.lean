import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafPullConnectingCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechShortExactPullCompatStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Nt2

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison.Om.Cech

theorem top_le_map {X Y : TopCat.{0}} (f : X ⟶ Y) : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤ := le_top

theorem zeroEquiv_eq_equivZero {X : TopCat.{0}} (F : AbSheaf X) (W : Opens X) (x : Sheaf.H'.{0} F 0 W) :
    GlobalTheory.SiteCoh.zeroEquiv F W x = GlobalTheory.SheafLES.equivZero.{0} F W x := by
  obtain ⟨g, rfl⟩ := (Abelian.Ext.mk₀_bijective _ F).surjective x
  rw [GlobalTheory.SheafLES.equivZero_mk₀]
  exact GlobalTheory.SiteCoh.zeroEquiv_mk₀ F W g

theorem hPull_zero {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X} (φ : G ⟶ (push f).obj G')
    (s : G.obj.obj (op ⊤)) :
    hPull f φ 0 ((Sheaf.H.equiv₀ G isTerminalTop).symm s) =
      (Sheaf.H.equiv₀ G' isTerminalTop).symm (GroundTheory.Arith.SchemeCoh.res G'.obj (top_le_map f) (φ.hom.app (op ⊤) s)) := by
  rw [AddEquiv.eq_symm_apply]
  simp only [hPull, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [GlobalTheory.SiteCoh.equiv₀_terminalEquiv, zeroEquiv_eq_equivZero, GlobalTheory.SheafPull.equivZero_sitePull,
    ← zeroEquiv_eq_equivZero, ← GlobalTheory.SiteCoh.equiv₀_terminalEquiv, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rfl

theorem pullCoch_globalCocycle {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q) {κ ι : Type} (V : κ → Opens Y)
    (U : ι → Opens X) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (s : P.obj (op ⊤)) :
    pullCoch f φ V U τ hτ 0 (globalCocycle P V s).1 =
      (globalCocycle Q U (GroundTheory.Arith.SchemeCoh.res Q (top_le_map f) (φ.app (op ⊤) s))).1 := by
  funext j
  change GroundTheory.Arith.SchemeCoh.res Q _ (φ.app _ (GroundTheory.Arith.SchemeCoh.res P _ s)) =
    GroundTheory.Arith.SchemeCoh.res Q _ (GroundTheory.Arith.SchemeCoh.res Q _ (φ.app (op ⊤) s))
  rw [app_res_map, GroundTheory.Arith.SchemeCoh.res_res, GroundTheory.Arith.SchemeCoh.res_res]

theorem cechHZeroEquiv_mk {X : TopCat.{0}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) {ι : Type} (U : ι → Opens X)
    (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P) (hU : iSup U = ⊤) (s : P.obj (op ⊤)) :
    cechHZeroEquiv P U hP hU (QuotientAddGroup.mk (globalCocycle P U s)) = s := by
  change (globalCocycleEquiv P U hP hU).symm (globalCocycle P U s) = s
  exact (globalCocycleEquiv P U hP hU).symm_apply_apply s

theorem cechHZero_pull' : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {G : AbSheaf Y} {G' : AbSheaf X} (φ : G ⟶ (push f).obj G') (x : cechH G.obj V 0),
    (cechHZeroEquivH G' U hU : cechH G'.obj U 0 ≃+ Sheaf.H.{0} G' 0) (cechPullH f φ.hom V U τ hτ 0 x) =
      hPull f φ 0 ((cechHZeroEquivH G V hV : cechH G.obj V 0 ≃+ Sheaf.H.{0} G 0) x) := by
  intro X Y f κ ι V hV U hU τ hτ G G' φ x
  obtain ⟨s, rfl⟩ := (cechHZeroEquiv G.obj V G.property hV).symm.surjective x
  have h1 : (cechHZeroEquiv G.obj V G.property hV).symm s = QuotientAddGroup.mk (globalCocycle G.obj V s) := by
    rw [AddEquiv.symm_apply_eq, cechHZeroEquiv_mk]
  have h3 : (⟨pullCoch f φ.hom V U τ hτ 0 (globalCocycle G.obj V s).1,
      pullCoch_mem_cocycles f φ.hom V U τ hτ (globalCocycle G.obj V s).2⟩ : cocycles G'.obj U 0) =
      globalCocycle G'.obj U (GroundTheory.Arith.SchemeCoh.res G'.obj (top_le_map f) (φ.hom.app (op ⊤) s)) :=
    Subtype.ext (pullCoch_globalCocycle f φ.hom V U τ hτ s)
  have h2 : cechPullH f φ.hom V U τ hτ 0 (QuotientAddGroup.mk (globalCocycle G.obj V s)) =
      QuotientAddGroup.mk (globalCocycle G'.obj U
        (GroundTheory.Arith.SchemeCoh.res G'.obj (top_le_map f) (φ.hom.app (op ⊤) s))) := by
    rw [← h3]
    rfl
  simp only [cechHZeroEquivH, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [h1, h2, cechHZeroEquiv_mk, hPull_zero]

theorem cechHOne_pull' : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)} (hS : S.ShortExact) [Injective S.X₂]
    (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : CechAcyclic S.X₂.obj V) (hS' : S'.ShortExact) [Injective S'.X₂]
    (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : CechAcyclic S'.X₂.obj U) (α : S ⟶ S'.map (push f))
    (x : cechH S.X₁.obj V 1),
    (cechHOneEquiv U hU hS' hC' hI' : cechH S'.X₁.obj U 1 ≃+ Sheaf.H.{0} S'.X₁ 1) (cechPullH f α.τ₁.hom V U τ hτ 1 x) =
      hPull f α.τ₁ 1 ((cechHOneEquiv V hV hS hC hI : cechH S.X₁.obj V 1 ≃+ Sheaf.H.{0} S.X₁ 1) x) := by
  intro X Y f κ ι V hV U hU τ hτ S S' hS _ hC hI hS' _ hC' hI' α x
  have h₁₂ : ∀ (W : (Opens Y)ᵒᵖ) (z : S.X₁.obj.obj W),
      α.τ₂.hom.app W (S.f.hom.app W z) = S'.f.hom.app _ (α.τ₁.hom.app W z) := fun W z => by
    have h := congrArg (fun g : S.X₁ ⟶ (S'.map (push f)).X₂ => g.hom.app W z) α.comm₁₂
    exact h.symm
  have h₂₃ : ∀ (W : (Opens Y)ᵒᵖ) (z : S.X₂.obj.obj W),
      α.τ₃.hom.app W (S.g.hom.app W z) = S'.g.hom.app _ (α.τ₂.hom.app W z) := fun W z => by
    have h := congrArg (fun g : S.X₂ ⟶ (S'.map (push f)).X₃ => g.hom.app W z) α.comm₂₃
    exact h.symm
  obtain ⟨s, rfl⟩ := cechOneProj_surjective V hV hC hI x
  have hL : cechPullH f α.τ₁.hom V U τ hτ 1 (cechOneProj V hC s) =
      cechOneProj U hC' (GroundTheory.Arith.SchemeCoh.res S'.X₃.obj (top_le_map f) (α.τ₃.hom.app (op ⊤) s)) := by
    change cechPullH f α.τ₁.hom V U τ hτ (0 + 1) (hC.delta 0 (globalCocycle S.X₃.obj V s)) =
      hC'.delta 0 (globalCocycle S'.X₃.obj U _)
    refine (GlobalTheory.T.cech_short_exact_pull_compat f V U τ hτ hC hC' α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃ 0
      (globalCocycle S.X₃.obj V s)).trans ?_
    congr 1
    exact Subtype.ext (pullCoch_globalCocycle f α.τ₃.hom V U τ hτ s)
  rw [hL, cechHOneEquiv_cechOneProj, cechHOneEquiv_cechOneProj]
  change H.δ hS' 0 1 rfl ((Sheaf.H.equiv₀ S'.X₃ isTerminalTop).symm _) =
    hPull f α.τ₁ 1 (H.δ hS 0 1 rfl ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm s))
  rw [GlobalTheory.T.sheaf_pull_connecting_compat f hS hS' α 0, hPull_zero]
  rfl

end CrystallineSemistableComparison.Om.Nt2
