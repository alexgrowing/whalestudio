import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem htAt_embV_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c')
      (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]),
      HTAt Y r ν yb yy P π ψ y → ∀ β : c'.V W →+* 𝓞_ℂ_[p], yb ≫ Y.s = spMap β →
      ∀ σ : E →+* ℂ, β.comp (embV c' W σ) = embInt c P.integers σ := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hov p _ _ _ yb yy P π ψ y hHT β hβ σ
  obtain ⟨⟨h1, -⟩, -, hF, -⟩ := hHT

  set g : Sp ℂ_[p] ⟶ Sp c'.F := yy ≫ pullback.snd _ _ with hg
  have hgm : spMap (Spec.preimage g).hom = g := by
    simp [spMap]
  set gm : c'.F →+* ℂ_[p] := (Spec.preimage g).hom
  have inj : ∀ {A B : Type} [CommRing A] [CommRing B] (f f' : A →+* B), spMap f = spMap f' → f = f' := by
    intro A B _ _ f f' h
    have := Spec.map_injective h
    exact congrArg CommRingCat.Hom.hom this
  have e1 : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp β = gm.comp (c'.V W).subtype := by
    apply inj
    have := congrArg (fun t => spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ t) hβ
    rw [← Category.assoc, h1, Category.assoc, Model.j_s, ← Category.assoc] at this
    rw [← spMap_spMap, ← spMap_spMap, ← this, hgm]
  have e2 : gm.comp (IntermediateField.inclusion hle).toRingHom = algebraMap c.F ℂ_[p] := by
    apply inj
    rw [← spMap_spMap, hgm, hg, Category.assoc, ← hov, ← Category.assoc, ← hF]
    exact pullback.lift_snd _ _ _
  refine RingHom.ext fun a => P.integers.hom_inj ?_
  rw [algebraMap_embInt]
  have := congrArg (fun f => f (embV c' W σ a)) e1
  simp only [RingHom.comp_apply] at this
  rw [RingHom.comp_apply, this, ← e2, RingHom.comp_apply]
  exact congrArg gm (Subtype.ext rfl)

end GlobalTheory.FlatModel
