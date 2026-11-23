import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallGenTwist
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def IsAmpleOnModel (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Prop :=
  ∀ e : K → ℤ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ (q : ℕ) (w : Fin q → Ω),
    (∀ j, w j ∈ chartLat y (e + (n : ℤ) • a) 1) ∧ KH.GeneratesOn y (e + (n : ℤ) • a) w

end Objects

def ArithNakaiMoishezon.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) L → IsConjInvariantH L →
    IsAmpleOnModel y L.a →
    (∀ (W : Ideal (MRing ι)) (e : ℕ), IsArithVar W (e + 1) → mCoordIdeal y ≤ W →
      0 < II K ι W (e + 1) (fun _ => L)) →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ (q : ℕ) (w : Fin q → Ω),
      (∀ j, w j ∈ chartLat y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n).a 1) ∧
      KH.GeneratesOn y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n).a w ∧
      ∃ c : ℝ, c < 1 ∧
        ∀ j, IsBoundedH (mCoordIdeal y) y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n) 1 c (w j)

section Inhabitants

open ProjLine

theorem isAmpleOnModel_projLine : IsAmpleOnModel (ι := GlobalTheory (Fin 2)) y fsLine1.a := by
  intro e
  refine ⟨(-e ()).toNat, fun n hn => ?_⟩
  obtain ⟨q, w, hw, hg, -⟩ := SmallGenTwist.smallGen_zcomb (ι := GlobalTheory (Fin 2)) y (fsH (GlobalTheory (Fin 2)))
    (SmallGenTwist.smallGen_fsH _) 0 (e () + n).toNat
  have ha : (HermLine.zcomb (fsH (GlobalTheory (Fin 2))) (fsH (GlobalTheory (Fin 2))) ((0 : ℕ) : ℤ)
      (((e () + n).toNat : ℕ) : ℤ)).a = e + (n : ℤ) • fsLine1.a := by
    funext k
    obtain rfl : k = () := rfl
    have h1 : fsLine1.a () = 1 := rfl
    have h2 : (fsH (GlobalTheory (Fin 2))).a () = 1 := by rw [SmallGenTwist.fsH_a]
    simp only [HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
    omega
  exact ⟨q, w, fun j => ha ▸ hw j, ha ▸ hg⟩

theorem ArithNakaiMoishezon.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ (⊥ : Ideal (MRing (GlobalTheory (Fin 2)))) ≤ mCoordIdeal y ∧
      IsSemipositiveRel ⊥ (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1 ∧ IsConjInvariantH fsLine1 ∧
      IsAmpleOnModel (ι := GlobalTheory (Fin 2)) y fsLine1.a :=
  ⟨G1.hyps_inhabited.1, bot_le, G1.hyps_inhabited.2.2.2.1, G1.hyps_inhabited.2.2.2.2.2,
    isAmpleOnModel_projLine⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Targets
