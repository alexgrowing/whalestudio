import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem gm_comp_stalkMap {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)ˣ) : gm (f ≫ g) z U a = Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U a) := by
  apply Units.ext
  rw [gm_val (f ≫ g) z U h, Units.coe_map, gm_val g (f z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f (g ⁻¹ᵁ U) z h ((g.app U).hom a.val)).symm

theorem val_comp_stalkMap {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (f : Z ⟶ W) (r : W ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    val t (f ≫ r) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val t r (f z) (fun ψ => J (f ≫ ψ))) := by
  rw [val_of t (f ≫ r) z J (fun k => J (f ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_comp_stalkMap f r z _ (Set.mem_iInter.2 fun k => hJ (f ≫ r ≫ φ k)) _

theorem good_comp {X Z W : Scheme.{0}} {L : LB X} (f : Z ⟶ W) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (f z) (fun ψ => J (f ≫ ψ)) := fun ψ => hJ (f ≫ ψ)

end GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem txFrame_frTw (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀)
    (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) : GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p₀ (frTw D τ h w) := by
  rintro ⟨hg, h2, hN⟩
  set f : (TF (R := R) (Kb R)).left ⟶ (TF (R := R) (Kb R)).left := spMap τ.toRingHom with hf
  have hfr : ∀ (z : (TF (R := R) (Kb R)).left) (J), Good D.P.L z J →
      val (frTw D τ h w) (𝟙 _) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val w (𝟙 _) (f z) (fun ψ => J (f ≫ ψ))) := by
    intro z J hJ
    rw [frTw, val_genCast, val_pull hJ, Category.id_comp, ← Category.comp_id f]
    exact val_comp_stalkMap w f (𝟙 _) z J hJ
  have hsy : ∀ (z : (TF (R := R) (Kb R)).left) (J), Good D.P.L z J →
      val (p₀.g.s p₀.y) (𝟙 _) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val (p.g.s p.y) (𝟙 _) (f z) (fun ψ => J (f ≫ ψ))) := by
    intro z J hJ
    rw [h.1, val_corr hJ (h.2.2 p.y), val_pull hJ, Category.id_comp, ← Category.comp_id f]
    exact val_comp_stalkMap _ f (𝟙 _) z J hJ
  refine ⟨genCast_isGen _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen D.P.L _ _ w hg _), ?_, ?_⟩
  · intro ν hν z J hJ
    rw [hfr z J hJ, hsy z J hJ, h.2.1, val_comp_stalkMap ν f _ z J hJ, ← map_pow, ← map_mul,
      h2 ν hν (f z) _ (good_comp f hJ)]
  · intro κ hκ z J hJ
    have hpsi : val (D.psi p₀.y) (jFK (R := R) (Kb R)) z J =
        Units.map (f.stalkMap z).hom.toMonoidHom (val (D.psi p.y) (jFK (R := R) (Kb R)) (f z) (fun ψ => J (f ≫ ψ))) := by
      have e := val_comp_stalkMap (D.psi p.y) f (jFK (R := R) (Kb R)) z J hJ
      rw [h.1]
      refine Eq.trans ?_ e
      exact congrArg (fun r => val (D.psi p.y) r z J) (spMap_jFK τ).symm
    have hrig : GlobalTheory.UT.rigV D (TF (R := R) (Kb R)).hom z J =
        Units.map (f.stalkMap z).hom.toMonoidHom (GlobalTheory.UT.rigV D (TF (R := R) (Kb R)).hom (f z) (fun ψ => J (f ≫ ψ))) := by
      unfold GlobalTheory.UT.rigV
      rw [← val_comp_stalkMap _ f _ z J hJ]
      exact congrArg (fun r => val D.rig r z J) (spMap_jFKR τ).symm
    rw [id_eq, hfr z J hJ, hpsi, hrig, h.2.1, val_comp_stalkMap κ f _ z J hJ, ← map_pow, ← map_mul, ← map_mul,
]
    exact congrArg _ (hN κ hκ (f z) _ (good_comp f hJ))

end GlobalTheory.Mum.Conj

end
