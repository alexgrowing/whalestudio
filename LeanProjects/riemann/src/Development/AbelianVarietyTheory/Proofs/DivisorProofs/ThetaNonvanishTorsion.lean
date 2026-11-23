import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem theta_nonvanish_coset (k : Type) [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (N : ℕ) (hN : 2 ≤ N) (hNk : (N : k) ≠ 0)
    (θ : LB.Sec (LPow P.A P.L 1 (baseOver (Spec (CommRingCat.of k)))))
    (hθ : SecM.ofSec P.A θ ≠ 0) (a : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) :
    ∃ x : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, x ^ N = 1 ∧
      ∃ (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Spec (CommRingCat.of k))).left) (K := Fin 1)
          (fun _ => (a * x).left) (fun _ => 1))) (v : Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤)),
        τ.IsGen ∧ IsValueAt P.A P.L 1 θ (a * x) τ v ∧ v ≠ 0 :=
  abelianSchemeLaws_all.1.goodPt k P N hN hNk θ hθ a

theorem theta_nonvanish_torsion (k : Type) [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (N : ℕ) (hN : 2 ≤ N) (hNk : (N : k) ≠ 0)
    (θ : LB.Sec (LPow P.A P.L 1 (baseOver (Spec (CommRingCat.of k)))))
    (hθ : SecM.ofSec P.A θ ≠ 0) :
    ∃ x : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, x ^ N = 1 ∧
      ∃ (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Spec (CommRingCat.of k))).left) (K := Fin 1)
          (fun _ => x.left) (fun _ => 1))) (v : Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤)),
        τ.IsGen ∧ IsValueAt P.A P.L 1 θ x τ v ∧ v ≠ 0 := by
  obtain ⟨x, hx, rest⟩ := theta_nonvanish_coset k P N hN hNk θ hθ 1
  exact ⟨1 * x, by rw [_root_.one_mul]; exact hx, rest⟩

end GlobalTheory.Poinc.Sep
