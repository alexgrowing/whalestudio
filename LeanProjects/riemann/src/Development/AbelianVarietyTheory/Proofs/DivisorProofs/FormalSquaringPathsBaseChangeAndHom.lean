import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalkStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem path_bc_ring {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] {R' : Type} [CommRing R']
    (φ : R →+* R') (c : R) (u : R') (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left) (h : IsPath G c b ξ) :
    IsPath G (φ c) (spMap φ ≫ b) (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) := by
  have hC : ((PowerSeries.rescale u).comp (PowerSeries.map φ)).comp (PowerSeries.C (R := R)) =
      (PowerSeries.C (R := R')).comp φ := by
    ext a n
    simp [PowerSeries.coeff_C]
    split_ifs <;> simp_all
  have h0 : (PowerSeries.constantCoeff (R := R')).comp ((PowerSeries.rescale u).comp (PowerSeries.map φ)) =
      φ.comp (PowerSeries.constantCoeff (R := R)) := by
    ext p
    simp only [RingHom.comp_apply]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, PowerSeries.coeff_map]
    simp
  have hs : (PowerSeries.rescale (φ c)).comp ((PowerSeries.rescale u).comp (PowerSeries.map φ)) =
      ((PowerSeries.rescale u).comp (PowerSeries.map φ)).comp (PowerSeries.rescale c) := by
    ext p n
    simp [PowerSeries.coeff_rescale, PowerSeries.coeff_map]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [Category.assoc, h.base, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hC,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h0, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, h.zero, Category.assoc]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, h.scale, Category.assoc]

theorem unitSec_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] :
    unitSec G ≫ q.left = unitSec H := by
  show (η[G]).left ≫ q.left = (η[H]).left
  rw [← Over.comp_left, IsMonHom.one_hom]

theorem sqr_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] :
    sqr G ≫ q.left = q.left ≫ sqr H := by
  unfold sqr
  rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id]

end GlobalTheory.Nef

theorem GlobalTheory.Nef.paths_bc : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (c : R) (u : R') (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G (φ c) (spMap φ ≫ b) (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ∧ ∀ [IsLocalRing R] (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), ⊤ ≤ b ⁻¹ᵁ V → ∀ (U : G.left.Opens) (hU : ⊤ ≤ ξ ⁻¹ᵁ U), HasTan G b ξ τ w → ∀ (hU' : ⊤ ≤ (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V') (f : Γ(G.left, U)), PowerSeries.coeff 1 (evAt (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) hU' f) = ∑ i, u * φ (w i) * φ (evAt b hb (dualApp (τ i) hV (dUnit G he f)))) ∧ (∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] (R : Type) [CommRing R] (c : R) (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), (IsPath G c b ξ → IsPath H c b (ξ ≫ q.left)) ∧ triv G b ≫ q.left = triv H b ∧ sqr G ≫ q.left = q.left ≫ sqr H) := by
  refine ⟨?_, ?_⟩
  · intro S G _ R _ R' _ φ c u b ξ h
    refine ⟨path_bc_ring G φ c u b ξ h, ?_⟩
    intro _ n V τ w _ U hU ht hU' V' hV he hb f
    rw [(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).1 (PowerSeries R) (PowerSeries R') G.left ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ξ U hU hU' f]
    rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_map, ht U hU V' hV he hb f, map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, pow_one, ← _root_.mul_assoc]
  · intro S G H _ _ q _ R _ c b ξ
    refine ⟨fun h => ⟨?_, ?_, ?_⟩, ?_, sqr_comp q⟩
    · rw [Category.assoc, Over.w q, h.base]
    · rw [← Category.assoc, h.zero, Category.assoc, unitSec_comp]
    · rw [← Category.assoc, h.scale, Category.assoc, Category.assoc, sqr_comp]
    · rw [triv, Category.assoc, Category.assoc, unitSec_comp, triv]
