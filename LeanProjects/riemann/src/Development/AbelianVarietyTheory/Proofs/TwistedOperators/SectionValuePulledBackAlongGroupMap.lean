import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeEx.SvPull

theorem sv_pull_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x₁ : Sp T ⟶ Xo.X} (pm : Gx x₁ ⟶ Gx x) {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)}, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x₁) Xo.univ.t.G).left → (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (hi : (PPx x₁).U i ≤ pm ⁻¹ᵁ (PPx x).U i), (pm.appLE _ _ hi).hom (s.f i) = s'.f i) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J := by
  intro E _ _ _ H Dw l Xo S T _ _ x x₁ pm s s' hsnd hf Z r z J hJ
  have hi0 : (PPx x₁).U (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) ≤
      pm ⁻¹ᵁ (PPx x).U (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) := by
    intro y hy
    have h1 := Set.mem_iInter.1 hy 0
    change pm.base y ∈ (⋂ k : Fin 1, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹'
      (Xo.univ.t.PP.L.U (J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) : Set _))
    refine Set.mem_iInter.2 fun _ => ?_
    simp only [Set.mem_preimage] at h1 ⊢
    rw [← Scheme.Hom.comp_apply, hsnd]
    exact h1
  have hz : r z ∈ (PPx x₁).U (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) :=
    hJ.mem (fun _ : Fin 1 => (snd (Over.mk x₁) Xo.univ.t.G).left) r
  dsimp only [sv]
  rw [sval_of s (r ≫ pm) z J (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left))
    (fun _ => by rw [Category.assoc, hsnd])]
  show gs r z ((PPx x₁).U _) (s'.f _) = _
  rw [← hf _ hi0, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, gs_res r z hi0 hz,
    gs_pull r pm z _ (hi0 hz)]
  rfl

end GlobalTheory.HeckeEx.SvPull
