import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowGat
import Formalism.SharpRestriction.InertJacobiLevels.ExtraNum

noncomputable section

namespace Formalism.MainNotions.Gaps.FR

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.Inhab Formalism.BasicNotions.Examples₂.NZ

section LevelValuationRings

variable {R : Ranks} (H : Host R) {W : Type} (hcW : W → Tau2 R → HCParam R) (K : W → ClsPkg) (T : W → ℕ)
  (rOf : W → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : W → ℕ → Set ↥(R.Psi)) (n : ℕ)

def localDataAtPlace : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w) := fun u w h =>
  gatNZ (served_of h) (bs u ((@placesOf H.E _ _ H.cmStar).resChar w)) (rOf u ((@placesOf H.E _ _ H.cmStar).resChar w))
    (fun ψ => lamOf (hcW u ψ) 0) ((K u).cls 0 × Fin n) (eOf ((@placesOf H.E _ _ H.cmStar).resChar w))

theorem local_data_dimension_eq : ∀ u w h, (localDataAtPlace H hcW K T rOf eOf bs n u w h).d = Fintype.card ((K u).cls 0) * n := fun _ _ _ => by
  classical
  rw [localDataAtPlace, gatNZ_d, Fintype.card_prod, Fintype.card_fin]

end LevelValuationRings

section Dim

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R)

def fibreDim : ℕ := ∏ ρ, (dimV_hc (hc ρ)).choose

theorem fibreDim_pos : 0 < fibreDim hc := Finset.prod_pos fun ρ _ => (dimV_hc (hc ρ)).choose_spec.1

theorem fibreDim_eq : (fibreDim hc : ℝ) = ∏ ρ, Formalism.MainNotions.StandardLattice.dimV (fun i => (((hc ρ).u i : ℚ) : ℝ)) := by
  unfold fibreDim
  push_cast
  exact Finset.prod_congr rfl fun ρ _ => (dimV_hc (hc ρ)).choose_spec.2

end Dim

end Formalism.MainNotions.Gaps.FR
