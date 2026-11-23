import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfA
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3upPfFilCAnti

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

theorem serC_mul {LL V' : Type} [Field LL] [AddCommGroup V'] [Module LL V'] (f g : PowerSeries LL)
    (d : V') (i : ℤ) :
    serC (f * g) d i = ∑ k ∈ Finset.range (i.toNat + 1), PowerSeries.coeff k f • serC g d (i - k) := by
  by_cases hi : 0 ≤ i
  · have hsum : ∀ k ∈ Finset.range (i.toNat + 1),
        PowerSeries.coeff k f • serC g d (i - k) =
          (PowerSeries.coeff k f * PowerSeries.coeff (i.toNat - k) g) • d := by
      intro k hk
      rw [Finset.mem_range] at hk
      have h1 : 0 ≤ i - (k : ℤ) := by omega
      have h2 : (i - (k : ℤ)).toNat = i.toNat - k := by omega
      simp only [serC, if_pos h1, h2, mul_smul]
    rw [Finset.sum_congr rfl hsum, ← Finset.sum_smul]
    simp only [serC, if_pos hi]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  · have h0 : i.toNat = 0 := by omega
    simp only [serC, if_neg hi, h0, zero_add, Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero,
      sub_zero, smul_zero]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem expS_mul (c : ZMod n) (ζ : LL) (f : LetA O n) {m : ℕ} (a : Fin m → LetA O n)
    (y : Fin m → W.DD T) (i : ℤ) :
    expS W T c ζ (fun j => f * a j) y i =
      ∑ k ∈ Finset.range (i.toNat + 1), PowerSeries.coeff k (W.lev c ζ f) • expS W T c ζ a y (i - k) := by
  simp only [expS, map_mul, serC_mul, Finset.smul_sum]
  exact Finset.sum_comm

def GoodF (τ : K →ₐ[Qp] LL) (h' : ℕ) (F : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  ∀ i : ℤ, F i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (h' - i)

theorem goodF_mul (c : ZMod n) (ζ : LL) (τ : K →ₐ[Qp] LL) (h' : ℕ) (f : LetA O n) {m : ℕ}
    (a : Fin m → LetA O n) (y : Fin m → W.DD T) (hg : GoodF (PD := PD) T τ h' (expS W T c ζ a y)) :
    GoodF (PD := PD) T τ h' (expS W T c ζ (fun j => f * a j) y) := by
  intro i
  rw [expS_mul]
  refine Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ ?_)
  exact u3upPf_FilC_anti (PD := PD) T τ (by omega) (hg (i - k))

end Generic

end Formalism.MainNotions.N.Ln34.MLB

end
