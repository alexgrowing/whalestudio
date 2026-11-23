import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull

theorem exists_pre_below : Laws → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K) (P₀ : PolAV (Sp K₀)) (Φ : D.P.A.left ⟶ P₀.A.left), IsGrpPullback D.P.A P₀.A (spMap i) Φ → LBIso D.P.L (P₀.L.pull Φ) → ∀ c₀ : D.X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) → (∀ y, (D.c y).left ≫ Φ = spMap i ≫ (c₀ y).left) → ∃ (D₀ : DegPre K₀) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (hD : IsPullDeg i D₀ (TauTwist.withPsi D ψ hψ)), D₀.P = P₀ ∧ HEq (PsiEvenPull.proj hD) Φ := by
  intro hL K₀ K _ _ i D P₀ Φ gp ⟨w₀, hw₀⟩ c₀ cadd hc
  obtain ⟨rig, hrig⟩ := P₀.rigid
  obtain ⟨cub⟩ := (hL.cube _ P₀ ⟨P₀.L, rig, P₀.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := SelfUnif.exists_sym P₀
  choose psi hpsi using fun χ : D.X => DVR.exists_gen_of_local (V := FractionRing K₀) P₀.L P₀.isLB (K := PUnit)
    (fun _ => ptK (c₀ χ)) (fun _ => -1)
  let D₀ : DegPre K₀ :=
    { P := P₀, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X,
      c := c₀, c_add := cadd, psi := psi, psi_gen := hpsi }
  obtain ⟨w, hw, hr⟩ := TripleMap.exists_rigidified P₀.isLB D.P.isLB w₀ ((isGen_iff w₀).1 hw₀) (eSec P₀.A)
    (eSec D.P.A) D.P.A.hom (Over.w η[D.P.A]) (spMap i) (cubeMapOf gp).e_comm rig hrig D.rig D.rig_gen
  have hx : ∀ χ, D.xK χ ≫ Φ = genMap i.injective ≫ ptK (c₀ χ) := fun χ => by
    show (jK K ≫ (D.c χ).left) ≫ Φ = genMap i.injective ≫ jK K₀ ≫ (c₀ χ).left
    rw [Category.assoc, hc, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _) ((Category.id_comp _).symm.trans (fracMap_sq i.injective))
  choose ψ hψ vψ using fun χ : D.X => exists_down_om ((isGen_iff w).2 hw) P₀.isLB D.P.isLB (K := PUnit)
    (φ' := fun _ => D.xK χ) (genMap i.injective) (fun _ => hx χ) (psi χ) (hpsi χ)
  obtain ⟨hD, e, -, -⟩ := exists_isPullDeg_of_val i D₀ (TauTwist.withPsi D ψ hψ) gp w hw hr (AddEquiv.refl _) hc
    (fun x z J J' hJ hJ' => by
      have v := vψ x _ (𝟙 _) z J J' hJ hJ'
      rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp] at v
      exact v)
  exact ⟨D₀, ψ, hψ, hD, rfl, heq_of_eq e⟩

end GlobalTheory.FieldPull
end
