import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

namespace GlobalTheory.CompanionTheory.VeryAmpleUnion

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def ChartBy (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (a : LB.Sec H) {m : ℕ}
    (s : Fin (m + 1) → LB.Sec H) : Prop :=
  IsAffineOpen (nonzeroLocus a) ∧
    ∃ r : Fin (m + 1) → Γ(X, nonzeroLocus a),
      (∀ j k, rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) ((s j).f k) =
        rs X (inf_le_left : nonzeroLocus a ⊓ H.U k ≤ nonzeroLocus a) (r j) *
          rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) (a.f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (cst f (nonzeroLocus a)) r)

theorem ChartBy.of_sub {f : X ⟶ Spec (CommRingCat.of R)} {H : LB X} {a : LB.Sec H} {m n : ℕ}
    {w : Fin (n + 1) → LB.Sec H} {z : Fin (m + 1) → LB.Sec H} (ι : Fin (n + 1) → Fin (m + 1))
    (hι : ∀ l, z (ι l) = w l) (h : ChartBy f H a w) : ChartBy f H a z := by
  obtain ⟨ha, r, hr, hs⟩ := h
  refine ⟨ha, fun j => secRatio a (z j), fun j k => secRatio_spec a (z j) k, fun g => ?_⟩
  obtain ⟨p, rfl⟩ := hs g
  refine ⟨MvPolynomial.rename ι p, ?_⟩
  have hrr : (fun j => secRatio a (z j)) ∘ ι = r := by
    funext l
    refine (eq_secRatio a (z (ι l)) ?_).symm
    intro k
    rw [hι l]
    exact hr l k
  simp only [MvPolynomial.coe_eval₂Hom]
  rw [MvPolynomial.eval₂_rename, hrr]

theorem veryAmpleBy_union : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X), H.IsLB → ∀ (m₁ m₂ m : ℕ) (x : Fin (m₁ + 1) → LB.Sec H) (y : Fin (m₂ + 1) → LB.Sec H) (e : Fin (m + 1) ≃ Fin (m₁ + 1) ⊕ Fin (m₂ + 1)), VeryAmpleBy f H x → VeryAmpleBy f H y → VeryAmpleBy f H (fun j => Sum.elim x y (e j)) := by
  intro R _ X f H _ m₁ m₂ m x y e hx hy
  have key : ∀ (z : Fin (m + 1) → LB.Sec H), (∀ j, z j = Sum.elim x y (e j)) →
      (⨆ j, nonzeroLocus (z j) = ⊤) ∧ ∀ j, ChartBy f H (z j) z := by
    intro z hz
    have hl : ∀ i, z (e.symm (Sum.inl i)) = x i := fun i => by simp [hz]
    have hr : ∀ i, z (e.symm (Sum.inr i)) = y i := fun i => by simp [hz]
    refine ⟨eq_top_iff.2 ?_, fun j => ?_⟩
    · rw [← hx.1]
      exact iSup_le fun i => le_iSup_of_le (e.symm (Sum.inl i)) (by rw [hl])
    · rcases he : e j with i | i
      · have hj : z j = x i := by rw [hz, he]; rfl
        rw [hj]
        exact ChartBy.of_sub (fun l => e.symm (Sum.inl l)) hl (hx.2 i)
      · have hj : z j = y i := by rw [hz, he]; rfl
        rw [hj]
        exact ChartBy.of_sub (fun l => e.symm (Sum.inr l)) hr (hy.2 i)
  exact key _ fun _ => rfl

end GlobalTheory.CompanionTheory.VeryAmpleUnion
