import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenFibre

theorem jK_comp_eq {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ξ : Sp V ⟶ M.Z) (emb : Ω →+* FractionRing V)
    (hemb : ∀ (W : M.Z.Opens) (f : Γ(M.Z, W)), ξ (IsLocalRing.closedPoint V) ∈ W →
      emb (valF M.pt W f) = algebraMap V (FractionRing V) (valR ξ W f)) :
    jK V ≫ ξ = spMap emb ≫ M.pt := by
  obtain ⟨W, hW, hξ, -⟩ := GlobalTheory.Points.exists_isAffineOpen_le ξ (GlobalTheory.Points.le_preimage_top ξ)
  have hz : ξ (IsLocalRing.closedPoint V) ∈ W := hξ (x := IsLocalRing.closedPoint V) trivial
  have hpt : ⊤ ≤ M.pt ⁻¹ᵁ W := M.top_le_preimage_pt ⟨_, hz⟩
  refine GlobalTheory.Points.ext_of_valR hW (GlobalTheory.Points.le_preimage_comp (V := ⊤) (jK V) ξ hξ le_rfl)
    (GlobalTheory.Points.le_preimage_comp (V := ⊤) (spMap emb) M.pt hpt le_rfl) fun f => ?_
  calc valR (jK V ≫ ξ) W f = algebraMap V (FractionRing V) (valR ξ W f) :=
        GlobalTheory.Points.valR_spMap_comp (algebraMap V (FractionRing V)) ξ W hξ f
    _ = emb (valF M.pt W f) := (hemb W f hz).symm
    _ = valR (spMap emb ≫ M.pt) W f := (GlobalTheory.Points.valR_spMap_comp emb M.pt W hpt f).symm

theorem genFibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ξ : Sp V ⟶ M.Z), (∃ w, ξ w = genericPoint M.Z) → ∀ [IsCommMonObj ((Over.pullback ξ).obj Zh.G)] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (IsLocalRing.maximalIdeal V) D A ((Over.pullback ξ).obj Zh.G)), LBIso U.LG.L (Zh.L.L.pull (pullback.fst Zh.G.hom ξ)) → ∀ (emb : Ω →+* FractionRing V), (∀ (W : M.Z.Opens) (f : Γ(M.Z, W)), ξ (IsLocalRing.closedPoint V) ∈ W → emb (valF M.pt W f) = algebraMap V (FractionRing V) (valR ξ W f)) → ∃ φ : A.A.left ⟶ ρ.P.A.left, IsGrpPullback A.A ρ.P.A (spMap (emb.comp (algebraMap S.R Ω))) φ ∧ LBIso A.L (ρ.P.L.pull φ) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh hO V _ _ _ ξ _ _ D A U hLG emb hemb
  have e₁ := jK_comp_eq M ξ emb hemb
  have hpt : Set.range M.pt ⊆ (U₀ : Set M.Z) := fun _ ⟨w, hw⟩ => hw ▸ M.top_le_preimage_pt hO.ne (x := w) trivial
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt (by rw [Scheme.Opens.range_ι]; exact hpt)
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x ≫ Zh.u₀ = spMap S.R.val.toRingHom := Zh.u₀_gen x hx
  let y : Sp (FractionRing V) ⟶ U₀.toScheme := spMap emb ≫ x
  have e₂ : (𝟙 _ ≫ jK V) ≫ ξ = y ≫ U₀.ι := by
    rw [Category.id_comp, e₁, Category.assoc, hx]
  have e₃ : 𝟙 _ ≫ y ≫ Zh.u₀ = spMap (emb.comp (algebraMap S.R Ω)) := by
    rw [Category.id_comp, Category.assoc, hxu]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
  have hA := ((isGrpPullback_of_iso U.gen.symm).comp
    (isGrpPullback_pullback ((Over.pullback ξ).obj Zh.G) (jK V))).comp (isGrpPullback_pullback Zh.G ξ)
  have hB := (isGrpPullback_pullback ((Over.pullback Zh.u₀).obj ρ.P.A) y).comp Zh.cart
  obtain ⟨e, he, hφ⟩ := grpPullback_iso (hA.congr e₂ rfl) hB
  haveI := he
  have hC := (isGrpPullback_of_iso e).comp ((isGrpPullback_pullback ((Over.pullback Zh.u₀).obj ρ.P.A) y).comp
    (isGrpPullback_pullback ρ.P.A Zh.u₀))
  refine ⟨_, hC.congr e₃ rfl, ?_⟩
  have H1 := U.ext
  have H2 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hLG (pullback.fst ((Over.pullback ξ).obj Zh.G).hom (jK V)) rfl
  have H3 := LBIso.trans (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _) (pull_isLB Zh.L.isLB _) H1 H2
  have H4 : LBIso (A.L.pull (𝟙 _)) (Zh.L.L.pull (U.gen.inv.left ≫
      pullback.fst ((Over.pullback ξ).obj Zh.G).hom (jK V) ≫ pullback.fst Zh.G.hom ξ)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp U.gen.inv.left
      (by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]) rfl H3
  have H5 := LBIso.chartPull (chartPullUnpull A.L (𝟙 _) rfl) (chartPullId _) H4
  have H6 : LBIso (Zh.L.L.pull (U.gen.inv.left ≫ pullback.fst ((Over.pullback ξ).obj Zh.G).hom (jK V) ≫
      pullback.fst Zh.G.hom ξ)) (ρ.P.L.pull (e.hom.left ≫ pullback.fst ((Over.pullback Zh.u₀).obj ρ.P.A).hom y ≫
      pullback.fst ρ.P.A.hom Zh.u₀)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp (e.hom.left ≫ pullback.fst ((Over.pullback Zh.u₀).obj ρ.P.A).hom y)
      (a := Zh.φ) (b := pullback.fst ρ.P.A.hom Zh.u₀) (by rw [Category.assoc, hφ, Category.assoc]; rfl)
      (Category.assoc _ _ _).symm ⟨Zh.w, Zh.w_gen⟩
  exact LBIso.trans A.isLB (pull_isLB Zh.L.isLB _) (pull_isLB ρ.P.isLB _) H5 H6

end GlobalTheory.GenFibre
