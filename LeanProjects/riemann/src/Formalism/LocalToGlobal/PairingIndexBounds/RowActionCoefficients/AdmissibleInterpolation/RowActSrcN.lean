import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.WeylComplementDetCoeffSpan

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem evX_gX {K : Type} [CommRing K] {n : ℕ} (x : ℕ × Fin n → K) (a : Fin n) (i : ℕ) : evX x (gX K n a i) = C (x (i, a)) := by
  unfold evX gX
  rw [coe_eval₂Hom, eval₂_X]

theorem evX_gY {K : Type} [CommRing K] {n : ℕ} (x : ℕ × Fin n → K) : (gY K n).map (evX x) = yV K n := by
  ext a t
  rw [Matrix.map_apply]
  unfold evX gY yV
  rw [coe_eval₂Hom, eval₂_C]
  rfl

theorem evX_HgX (j : ℕ) (b : BX X) (x : ℕ × Fin (NJ X j) → X.G.Kf) :
    evX x (HgX X X.G.Kf j b) = srcN X j b fun a i => x (i, a) := by
  unfold HgX srcN
  split_ifs with ho
  · rw [map_hvO, evX_gY]
    simp only [evX_gX]
  · rw [map_mul, map_pow, RingHom.map_det, map_hvE, evX_gY, map_pow, RingHom.map_det]
    simp only [evX_gX]
    congr 3
    ext a i
    simp [evX_gX]

theorem HgX_map (O K : Type) [CommRing O] [CommRing K] (f : O →+* K) (j : ℕ) (b : BX X) :
    map (map f) (HgX X O j b) = HgX X K j b := by
  have hx : ∀ a i, (map (map f) : GenR O (NJ X j) →+* GenR K (NJ X j)) (gX O (NJ X j) a i) = gX K (NJ X j) a i := by
    intro a i
    unfold gX
    rw [map_X]
  have hy : (gY O (NJ X j)).map (map (map f) : GenR O (NJ X j) →+* GenR K (NJ X j)) = gY K (NJ X j) := by
    ext a t
    rw [Matrix.map_apply]
    unfold gY
    rw [map_C, map_X]
  unfold HgX
  split_ifs with ho
  · rw [map_hvO, hy]
    simp only [hx]
  · rw [map_mul, map_pow, RingHom.map_det, map_hvE, hy]
    simp only [hx]
    congr 3
    ext a i
    simp [hx]

theorem hQX (hS : XShape) (j : ℕ) (b : BX X) :
    (weyl X.G.O (NJ X j) (NJ X j) le_rfl (nuM X j b)).map (toK X.G.O X.G.Kf) ≤
      Submodule.span X.G.O (Set.range fun m => coeff m (HgX X X.G.Kf j b)) := by
  obtain ⟨h1, -, hanti, hle, -, -, -, -, -, -⟩ := hS p X j b
  rw [h1]
  have key : weyl X.G.O (NJ X j) (NJ X j) le_rfl (nuS X j b) ≤
      Submodule.span X.G.O (Set.range fun m => coeff m (HgX X X.G.O j b)) := by
    by_cases ho : IsOddPos b.2
    · have hn : nuS X j b = fun t => cX X j b - muX X j (NJ X j) b t.rev := if_pos ho
      unfold HgX
      rw [if_pos ho, hn]
      exact weyl_complement_det_coeff_span X.G.O (NJ X j) _ (hanti _) _ (hle _)
    · have hn : nuS X j b = fun t => muX X j (NJ X j) b t - eX X j b := if_neg ho
      unfold HgX
      rw [if_neg ho]
      refine weyl_lattice_det_coeff_span X.G.O (NJ X j) (nuS X j b) ?_ _ _ ?_
      · rw [hn]
        exact fun a c hac => Nat.sub_le_sub_right (hanti _ hac) _
      · rw [hn]
        exact fun t => (Nat.sub_le _ _).trans (hle _ t)
  refine (Submodule.map_mono key).trans ?_
  rw [Submodule.map_span, ← Set.range_comp]
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  refine ⟨m, ?_⟩
  show _ = map (algebraMap X.G.O X.G.Kf) (coeff m (HgX X X.G.O j b))
  rw [← HgX_map X X.G.O X.G.Kf (algebraMap X.G.O X.G.Kf) j b]
  exact coeff_map _ _ _

end Formalism.L2.PairingIndexBounds.Ent
