import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.CardTors

theorem card_tors_eq : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ∀ (G₀ : Over (Sp K)) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (spMap (algebraMap R K)) F → ∀ (GG₀ : PDivGroup p K) (θ₀ : TorsionMap G₀ GG₀), (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra K B], Function.Bijective (θ₀.pt n B)) → ∀ n : ℕ, Nat.card (Tors G (p ^ n) K) = p ^ (n * GG₀.height) := by
  intro p _ R K _ _ _ _ _ _ _ _ G _ _ G₀ _ _ F h GG₀ θ₀ hθ n
  let f : Sp K ⟶ Sp R := spMap (algebraMap R K)
  let T : Over (Sp K) := SpAlg K K
  have hc : T.hom ≫ f = (SpAlg R K).hom := by
    show spMap (algebraMap K K) ≫ spMap (algebraMap R K) = spMap (algebraMap R K)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let ρ : SpAlg R K ⟶ Over.mk (T.hom ≫ f) := Over.homMk (𝟙 _) ((Category.id_comp _).trans hc)
  let Φ : (T ⟶ G₀) →* (SpAlg R K ⟶ G) := (preHom ρ).comp (pushHom h T)
  have hΦ : ∀ x, (Φ x).left = x.left ≫ F := fun x => Category.id_comp _
  have hb : Function.Bijective Φ := by
    refine ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm)), fun a => ?_⟩
    · rw [← hΦ, ← hΦ, e]
    · exact ⟨Over.homMk (h.1.lift a.left T.hom ((Over.w a).trans hc.symm)) (h.1.lift_snd _ _ _),
        Over.OverMorphism.ext ((hΦ _).trans (h.1.lift_fst _ _ _))⟩
  let e := MulEquiv.ofBijective Φ hb
  have e1 : Tors G₀ (p ^ n) K ≃ Tors G (p ^ n) K := e.toEquiv.subtypeEquiv fun x => by
    show _ ↔ e x ^ (p ^ n) = 1
    rw [← map_pow, EmbeddingLike.map_eq_one_iff]
  rw [← Nat.card_congr e1, Nat.card_congr (Equiv.ofBijective _ (hθ n K))]
  exact GG₀.natCard_pts_eq K n

end GlobalTheory.GroupBplus.Aff.CardTors
