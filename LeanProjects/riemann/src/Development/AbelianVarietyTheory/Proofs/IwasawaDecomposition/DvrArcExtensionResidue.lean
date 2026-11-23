import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmIdempotentAddStarEqOne
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory
open scoped Classical

noncomputable section
namespace GlobalTheory.LieTrait

theorem lieMult_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp β → y ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y → ∀ (t : SAB H (Sp T.V)) (m : SABMap t Y.t y) (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] (r : O), ((β r : c.F) : ℂ) = H.rt0 → ∀ τ : 𝓞 E →+* F, LieMult t.act (spMap ((algebraMap T.Fr F).comp (algebraMap T.V T.Fr))) τ (if τ H.rt = algebraMap T.Fr F (algebraMap T.V T.Fr (b r)) then D.p else D.q) := by
  intro E _ _ _ H D l Xo c O _ β Y T io b y z h₁ h₂ h₃ h₄ t m F _ _ _ r hr τ
  let β' : KA l →+* F := ((algebraMap T.Fr F).comp io).comp (IntermediateField.inclusion c.le).toRingHom
  let x : Sp F ⟶ Xo.XF c := spMap (algebraMap T.Fr F) ≫ z
  have hx : x ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β' := by
    change (spMap (algebraMap T.Fr F) ≫ z) ≫ pullback.fst _ _ ≫ Xo.s = _
    rw [pullback.condition, Category.assoc, reassoc_of% h₃]
    simp only [spMap, β', ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hρ : β' (baseKA l).ρ = algebraMap T.Fr F (algebraMap T.V T.Fr (b r)) := by
    have e : (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ = β r :=
      Subtype.ext (by simpa [baseKA] using hr.symm)
    have e₂ : io (β r) = algebraMap T.V T.Fr (b r) := (RingHom.congr_fun h₁ r).symm
    simp only [β', RingHom.comp_apply, e, e₂]
  have hdet := (Y.oF.geom F x β' hx).1 τ
  have hw : spMap ((algebraMap T.Fr F).comp (algebraMap T.V T.Fr)) ≫ y = x ≫ Y.jQ ≫ pullback.fst _ _ := by
    have : spMap ((algebraMap T.Fr F).comp (algebraMap T.V T.Fr)) =
        spMap (algebraMap T.Fr F) ≫ spMap (algebraMap T.V T.Fr) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h₄' : z ≫ Y.jQ ≫ pullback.fst _ _ = spMap (algebraMap T.V T.Fr) ≫ y := h₄
    rw [this, Category.assoc, ← h₄', Category.assoc]
  have key : ∀ n, LieMult Y.oF.t.act x τ n →
      LieMult t.act (spMap ((algebraMap T.Fr F).comp (algebraMap T.V T.Fr))) τ n := by
    intro n hn
    have h₅ := (lieMult_iff_of_isGrpPullback Y.m.cart Y.oF.t.act Y.t.act Y.m.act x τ n).1 hn
    rw [← hw] at h₅
    exact (lieMult_iff_of_isGrpPullback m.cart t.act Y.t.act m.act _ τ n).2 h₅
  split_ifs with hτ
  · exact key _ (hdet.1 (hτ.trans hρ.symm))
  · exact key _ (hdet.2 (fun e => hτ (e.trans hρ)))

end GlobalTheory.LieTrait
