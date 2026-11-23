import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam.Pad
open MonObj

noncomputable section

namespace GlobalTheory.ShFam.Pad

attribute [local instance] Over.cartesianMonoidalCategory

theorem dualMap_comp_epsMul_ring {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (c : S) :
    (dualMap φ).comp (epsMul c) = (epsMul (φ c)).comp (dualMap φ) := by
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, dualMap, _root_.mul_comm]

theorem dualMap_comp_algebraMap_ring {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    (dualMap φ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp φ := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem latDR_comb_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X) (w : Sp (DualNumber C) ⟶ t.G.left), IsTanAtG t x w → w ∈ latDR t x → ∀ (n : ℕ) (a : Fin n → 𝓞 E) (c : Fin n → C), (∀ j, ‖c j‖ ≤ 1) → ∀ W : Sp (DualNumber C) ⟶ t.G.left, IsCombAtG t x (fun j => w ≫ (t.act.act (a j)).left) c W → W ∈ latDR t x := by
  intro E _ _ _ H X t C _ _ x w hw hlat n a c hc W hW
  obtain ⟨xO, hx, vO, hvO, hv⟩ := hlat
  let φ := (Formalism.MainNotions.DIV.Cons.intO C).subtype
  let cO : Fin n → Formalism.MainNotions.DIV.Cons.intO C := fun j => ⟨c j, hc j⟩
  let v : Fin n → (tEpsG xO ⟶ t.G) := fun j => ovT hvO ≫ t.act.act (a j)
  have hv0 : ∀ j, smT xO 0 (v j) = 1 := fun j => by
    have := t.act.hom (a j)
    show smT xO 0 (ovT hvO ≫ t.act.act (a j)) = 1
    rw [smT_post, smT_zero_ovT]
    exact MonObj.one_comp _
  refine ⟨xO, hx, (combT xO v cO).left, isTanAtG_of _ (combT_tan xO v hv0 cO), ?_⟩
  let f : tEpsG x ⟶ tEpsG xO := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap _ _) ≫ xO = spMap (algebraMap C (DualNumber C)) ≫ x
    rw [← hx, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_algebraMap_ring])
  have hW' := (isCombAtG_iff t x (fun j => ovT hw ≫ t.act.act (a j)) c W).1 hW
  rw [← hW']
  have key : f ≫ combT xO v cO = combT x (fun j => ovT hw ≫ t.act.act (a j)) c := by
    unfold combT
    rw [comp_prodT]
    refine Finset.prod_congr rfl fun j _ => ?_
    apply Over.OverMorphism.ext
    show spMap (dualMap φ) ≫ spMap (epsMul (cO j)) ≫ vO ≫ (t.act.act (a j)).left =
      spMap (epsMul (c j)) ≫ w ≫ (t.act.act (a j)).left
    rw [← hv, ← Category.assoc, spMap_comp', dualMap_comp_epsMul_ring, ← spMap_comp']
    simp only [Category.assoc]
    rfl
  exact congrArg (fun g => g.left) key

end GlobalTheory.ShFam.Pad
