import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureHopfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureDivisibilityMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureDivisibilityCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureMultiplicationMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHopfPointsSeparateStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem exists_pDivGroup_isModel (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (h : ℕ) (hc : ∀ n, Nat.card (Tors G (p ^ n) K) = p ^ (n * h)) :
    ∃ (GG : PDivGroup p R) (θ : TorsionMap G GG), GG.height = h ∧ IsModel K θ := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hn : ∀ n : ℕ, p ^ n ≠ 0 := fun n => pow_ne_zero n hp
  choose A i1 i2 i3 i4 i5 θ hθ using fun n : ℕ => GlobalTheory.T.exists_level_structure_hopf R K G hG (p ^ n) (hn n)
  have hd : ∀ n : ℕ, p ^ n ∣ p ^ (n + 1) := fun n => Dvd.intro p rfl
  have hg := fun n : ℕ => (GlobalTheory.T.level_structure_divisibility_map R K G hG (p ^ n) (p ^ (n + 1)) (hn n) (hd n) (A n) (A (n + 1)) (θ n) (θ (n + 1))
    (hθ n) (hθ (n + 1)) (𝟙 G) inferInstance).exists
  choose g hg using hg
  have hg' : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] (z : Tors G (p ^ n) B),
      (θ (n + 1)).pt B (torsIncl (hd n) z) = ((θ n).pt B z).comp (g n : A (n + 1) →ₐ[R] A n) :=
    fun n B _ _ z => hg n B z _ (Category.comp_id _).symm
  let GG : PDivGroup p R :=
    { height := h
      A := A
      rank_eq := fun n q => by
        rw [(GlobalTheory.T.finite_hopf_points_separate R K (A n)).2.2 q, ← hc n]
        exact (Nat.card_eq_of_bijective _ (hθ n).gen).symm
      res := g
      res_surjective := fun n => GlobalTheory.T.level_structure_divisibility_compat R K G hG (p ^ n) (p ^ (n + 1)) (hd n) (hn n) (A n) (A (n + 1)) (θ n)
        (θ (n + 1)) (hθ n) (hθ (n + 1)) (g n) (hg' n)
      ker_res := fun n => GlobalTheory.T.level_structure_multiplication_map R K G hG (p ^ n) p (hn n) hp (A n) (A (n + 1)) (θ n)
        (θ (n + 1)) (hθ n) (hθ (n + 1)) (g n) (hg' n) }
  let Θ : TorsionMap G GG :=
    { pt := fun n B _ _ z => (θ n).pt B z
      nat := fun n B C _ _ _ _ φ z z' e => by
        obtain rfl : z' = torsMap φ z := Subtype.ext e
        exact (θ n).nat B C φ z
      mul := fun n B _ _ x y z e => by
        obtain rfl : z = x * y := Subtype.ext e
        exact (θ n).mul B x y
      res := fun n B _ _ z z' e => hg n B z z' (e.trans (Category.comp_id _).symm) }
  exact ⟨GG, Θ, rfl, fun n => ⟨(hθ n).opn, (hθ n).gen⟩⟩

end GlobalTheory.GroupBplus.Aff
