import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopRankPowers
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

variable {K : Type} [Field K] [NumberField K]

theorem monoDeg_succ_split {ι : Type} [Fintype ι] {a : ℕ} (β : MonoDeg ι (a + 1)) :
    ∃ (i : ι) (α : MonoDeg ι a), β.1 = α.1 + Finsupp.single i 1 := by
  have hne : β.1 ≠ 0 := fun h0 => by
    have := β.2
    rw [h0, Finsupp.degree_eq_sum] at this
    simp at this
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hne
  have hle : Finsupp.single i 1 ≤ β.1 := by
    rw [Finsupp.single_le_iff]
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
    omega
  have e : β.1 = (β.1 - Finsupp.single i 1) + Finsupp.single i 1 := (tsub_add_cancel_of_le hle).symm
  refine ⟨i, ⟨β.1 - Finsupp.single i 1, ?_⟩, e⟩
  have h2 := β.2
  rw [e, Finsupp.degree_eq_sum, Finset.sum_congr rfl (fun x _ => Finsupp.add_apply _ _ x),
    Finset.sum_add_distrib, ← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum, Finsupp.degree_single] at h2
  omega

theorem mulPow_mem (X : Data K) (s : Fin X.D → Fin X.N → K) (hX : X.MulStable) :
    ∀ (a j l : ℕ) (h : j + a = l), l ≤ X.T → ∀ (α : MonoDeg (Fin X.D) a), ∀ m ∈ X.V j,
      mulPow X.toGeo s h α m ∈ X.V l := by
  intro a
  induction a with
  | zero =>
    intro j l h _ α m hm
    subst h
    have : mulPow X.toGeo s (rfl : j + 0 = j + 0) α m = m := by
      unfold mulPow
      exact mulMono_zero _ _ _ _ _ _
    rw [this]
    exact hm
  | succ a ih =>
    intro j l h hl β m hm
    subst h
    obtain ⟨i, α, e⟩ := monoDeg_succ_split β
    have hk : j + a < X.T := by omega
    have key : mulPow X.toGeo s (rfl : j + (a + 1) = j + (a + 1)) β m =
        X.mulW (j + a) (s i) (mulPow X.toGeo s (rfl : j + a = j + a) α m) := by
      unfold mulPow
      rw [Geo.mulW_apply]
      exact mulMono_succ _ _ _ α β i e _ _ _ m
    rw [key]
    exact hX.mem hk (s i) ⟨_, ih j (j + a) rfl (by omega) α m hm⟩

theorem mulPow_mem_and_spaceV_le : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K),
    X.MulStable → (∀ (a j l : ℕ) (h : j + a = l), l ≤ X.T → ∀ (α : MonoDeg (Fin X.D) a), ∀ m ∈ X.V j,
      mulPow X.toGeo s h α m ∈ X.V l) ∧ spaceV X s ≤ X.V X.T := by
  intro K _ _ X s hX
  refine ⟨mulPow_mem X s hX, ?_⟩
  refine sup_le (X.global_le X.T le_rfl) (iSup_le fun α => ?_)
  rintro _ ⟨m, hm, rfl⟩
  exact mulPow_mem X s hX _ _ _ _ le_rfl α m hm

end GlobalTheory.HSCore
