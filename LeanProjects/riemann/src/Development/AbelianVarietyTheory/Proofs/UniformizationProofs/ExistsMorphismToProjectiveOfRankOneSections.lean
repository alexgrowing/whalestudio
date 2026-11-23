import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfProportional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRankOneBundle
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RankMap

theorem exists_hom_of_rank_one : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (f : Z ⟶ Spec (CommRingCat.of R)) (H : LB Z) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X : Scheme.{0}) (f' : X ⟶ Spec (CommRingCat.of R)) (N : LB X) (m : ℕ) (w : Fin (n + 1) → Fin (m + 1) → LB.Sec N), N.IsLB → (⨆ i, ⨆ j, nonzeroLocus (w i j) = ⊤) → (∀ i i' j j' k, (w i j).f k * (w i' j').f k = (w i j').f k * (w i' j).f k) → (∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ k, MvPolynomial.eval₂Hom (cst f (H.U k)) (fun i => (s i).f k) F = 0) → ∀ j k, MvPolynomial.eval₂Hom (cst f' (N.U k)) (fun i => (w i j).f k) F = 0) → ∃ φ : X ⟶ Z, φ ≫ f = f' ∧ ∀ (T : Scheme.{0}) (r : T ⟶ X) (ψ : T ⟶ Z), ψ ≫ f = r ≫ f' → (∀ z k k' i i' j, ψ z ∈ H.U k → r z ∈ N.U k' → gs ψ z (H.U k) ((s i).f k) * gs r z (N.U k') ((w i' j).f k') = gs ψ z (H.U k) ((s i').f k) * gs r z (N.U k') ((w i j).f k')) → r ≫ φ = ψ := by
  intro R _ Z f H n s hH hs X f' N m w hN hw hr he
  obtain ⟨H', s', hH', hs', hv⟩ := GlobalTheory.RankBundle.exists_rank_one_bundle X N n m w hN hw hr
  obtain ⟨φ, u, hφ, -, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy R Z f H n s hH hs X f' H' s' hH' hs'
    fun t F hF h0 c => by
      refine fn_ext fun x hx => ?_
      obtain ⟨j, hj⟩ := hv x c hx
      obtain ⟨k, hk⟩ := exists_chart hN x
      obtain ⟨v, hvi⟩ := hj k hk
      have e := congrArg (gs (𝟙 X) x _) (he t F hF h0 j k)
      rw [MorAlg.gs_eval f' (𝟙 X) x _ hk, gs_eq (𝟙 X) x _ hk 0, map_zero, map_zero] at e
      simp only [hvi] at e
      rw [MorAlg.eval₂_scale _ _ _ hF] at e
      rw [MorAlg.gs_eval f' (𝟙 X) x _ hx, gs_eq (𝟙 X) x _ hx 0, map_zero, map_zero]
      exact ((Units.isUnit _).pow t).mul_right_eq_zero.1 e
  refine ⟨φ, hφ, fun T r ψ hψ hp => ?_⟩
  refine GlobalTheory.ProjUniq.hom_eq_of_proportional R Z f H n s hH hs T _ _
    (by rw [Category.assoc, hφ, hψ]) fun z k k' i i' hk hk' => ?_
  obtain ⟨c, hc⟩ := exists_chart hH' (r z)
  obtain ⟨d, hd⟩ := exists_chart hN (r z)
  obtain ⟨j, hj⟩ := hv (r z) c hc
  obtain ⟨v, hvi⟩ := hj d hd
  have hu : IsUnit ((r.stalkMap z).hom v.val) := v.isUnit.map _
  have e : ∀ l, gs r z (N.U d) ((w l j).f d) =
      (r.stalkMap z).hom v.val * gs r z (H'.U c) ((s' l).f c) := fun l => by
    have e := congrArg (r.stalkMap z).hom (hvi l)
    rwa [map_mul, MorAlg.gs_stalk r (𝟙 X) z _ hd, MorAlg.gs_stalk r (𝟙 X) z _ hc, Category.comp_id] at e
  have q := hp z k' d i i' j hk' hd
  rw [e, e] at q
  rw [MorAlg.Carries.at (w := u) cu r i z k c hk hc, MorAlg.Carries.at (w := u) cu r i' z k c hk hc]
  refine hu.mul_left_cancel ?_
  linear_combination (-(Geo.Tor.gw u r z k c).val) * q

end GlobalTheory.RankMap
