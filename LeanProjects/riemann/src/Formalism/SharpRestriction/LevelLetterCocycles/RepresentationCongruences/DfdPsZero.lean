import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AlgebraMapMemInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.PpLeHLD

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DFD

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem smul_sub_eq_smul_add {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Lk' Lk L0 Lκ0 Ls G X Ec Q U' P1 P2 FΛ S Φ Rr C1 C2 f₂ : R) (e1 e2 e3 n2v z : M)
    (hL0 : L0 = Lκ0 * Lk) (hG : G = P1 * P2 * FΛ) (hC1 : C1 = Lk' * Lk * FΛ * U' * P1)
    (hC2 : C2 = X * (P1 * P2 * Rr)) (hz : z = FΛ • e2)
    (h2 : Lk' • (Lk • e1 - Ls • e3) = Φ • e2) (h1 : n2v = S • e1)
    (h4 : P1 * (Lκ0 * f₂ - Ec * X) = Ec * Q * U') (h5 : P1 * S = P2)
    (h6 : Ec • e1 = e1) (h7 : Φ = Q * Rr) :
    (Lk' * G) • (L0 • (f₂ • e1) - Ls • (X • e3)) = Q • (C1 • n2v + C2 • z) := by
  subst hL0 hG hC1 hC2 hz h1 h7
  have h4v := congrArg (fun t : R => t • ((P2 * FΛ * Lk' * Lk) • e1)) h4
  have h5v := congrArg (fun t : R => t • ((FΛ * Lk' * Lk * Ec * Q * U') • e1)) h5
  linear_combination (norm := module) (P1 * P2 * FΛ * X) • h2 +
    (P1 * P2 * FΛ * Lk' * Lk * X + FΛ * Lk' * Lk * Q * U' * P1 * S) • h6 + h4v - h5v

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem dfd_ps_succ (k : ℕ) : ps W (k + 1) = W.φA (ps W k) := by
  unfold ps
  rw [pow_succ', AlgHom.mul_apply]

theorem dfd_ps_zero : ps W 0 = qA W := by
  unfold ps
  rw [pow_zero, AlgHom.one_apply]

theorem dfd_φLam_mem (A : ArcP n) (a : ZMod n) (e : ℕ) :
    W.φA (abelian₂ W A a e) ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k} := by
  unfold abelian₂
  rw [map_prod]
  refine Submonoid.prod_mem _ fun s _ => ?_
  rw [map_pow, ← dfd_ps_succ]
  exact Submonoid.pow_mem _ (Submonoid.subset_closure
    (show ps W (s + 1) ∈ {x : LetA O n | ∃ k ≥ 1, x = ps W k} from ⟨s + 1, by omega, rfl⟩)) _

theorem dfd_φD_three (T : LocLat G Qp LL O) (x : W.DD T) :
    ((W.φD T) ^ 3) x = W.φD T (((W.φD T) ^ 2) x) := by
  rw [pow_succ']
  rfl

theorem dfd_φA_lA (k : ℕ) : W.φA (lA W ^ k) = lA W ^ k := by
  simp only [lA, map_pow, map_natCast]

theorem dfd_alg_lA (k : ℕ) : algebraMap (LetA O n) W.EE (lA W ^ k) = lE W k := by
  simp only [lA, lE, map_pow, map_natCast]

theorem dfd_closure_AΔ {x : LetA O n}
    (hx : x ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}) : x ∈ W.AΔ := by
  have key : Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k} ≤ W.AΔ.toSubmonoid := by
    rw [Submonoid.closure_le]
    rintro _ ⟨k, -, rfl⟩
    exact TypesA.ps_mem W k
  exact key hx

end Local

end Formalism.MainNotions.N.FrobeniusPowerSeries.DFD

end
