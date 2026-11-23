import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesD

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

def LocalSymmStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (j : Fin A.n) (χ w : X → ℝ), A.Smooth χ → A.Smooth w →
    tsupport χ ⊆ (A.chart j).source → ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun w) Φ) χ = mInt A (Fin.cons (LocPot.ofFun χ) Φ) w

theorem localSymm : LocalSymmStatement := by
  intro e X _ _ _ A _ χ w hχ hw _ Φ hΦ
  exact st_byPartsSymm_of ReciprocityTheory.AnForm.A.parts_thm A χ w hχ hw Φ hΦ

def MIntConstPotStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X) (c : ℝ)
    (Φ : Fin e → LocPot X) (g : X → ℝ), mInt A (Fin.cons (LocPot.ofFun fun _ => c) Φ) g = 0

private lemma sum_neg_one_pow_det_sum_eq_zero_of_eq_zero {ι m : Type} [Fintype ι] [DecidableEq ι] [Fintype m]
    [DecidableEq m] (M : ι → Matrix m m ℂ) (a : ι) (ha : M a = 0) (N : ℕ)
    (hN : Fintype.card ι ≤ N) :
    ∑ S : Finset ι, (-1 : ℂ) ^ (N - S.card) * (∑ k ∈ S, M k).det = 0 := by
  have hU : (Finset.univ : Finset (Finset ι)) = (Finset.univ : Finset ι).powerset :=
    Finset.powerset_univ.symm
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨a⟩
  rw [hU, ← Finset.insert_erase (Finset.mem_univ a),
    Finset.sum_powerset_insert (by simp : a ∉ (Finset.univ : Finset ι).erase a),
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro t ht
  rw [Finset.mem_powerset] at ht
  have hat : a ∉ t := fun h => by simpa using ht h
  have hc : t.card + 1 ≤ N := by
    have h1 := Finset.card_le_card ht
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ] at h1
    omega
  rw [Finset.sum_insert hat, ha, zero_add, Finset.card_insert_of_notMem hat]
  obtain ⟨d, hd⟩ : ∃ d, N - t.card = d + 1 := ⟨N - (t.card + 1), by omega⟩
  have hd' : N - (t.card + 1) = d := by omega
  rw [hd, hd', pow_succ]
  ring

private lemma mdisc_eq_zero_of_eq_zero' {n : ℕ} (M : Fin n → Matrix (Fin n) (Fin n) ℂ) (a : Fin n)
    (ha : M a = 0) : mdisc M = 0 := by
  unfold mdisc
  rw [sum_neg_one_pow_det_sum_eq_zero_of_eq_zero M a ha n (by simp)]
  simp

theorem mIntConstPot : MIntConstPotStatement := by
  intro e X _ A c Φ g
  unfold mInt
  split_ifs with h
  · simp only [integralWith, locDens]
    apply Finset.sum_eq_zero
    intro j _
    have h0 : ∀ y : Fin (e + 1) → ℂ, hessC (fun _ : Fin (e + 1) → ℂ => c) y = 0 := by
      intro y
      unfold hessC
      simp
      funext i k
      rfl
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun y _ => ?_)
    unfold maDens
    rw [mdisc_eq_zero_of_eq_zero' _ 0]
    · simp
    · simp only [Fin.cons_zero]
      exact h0 y
  · rfl

theorem stokes : StokesStatement := st_stokes_of ReciprocityTheory.AnForm.A.parts_thm
theorem byPartsSymm : ByPartsSymmStatement := st_byPartsSymm_of ReciprocityTheory.AnForm.A.parts_thm
theorem byPartsNonpos : ByPartsNonposStatement :=
  st_byPartsNonpos_of ReciprocityTheory.AnForm.A.parts_thm ReciprocityTheory.AnForm.A.gradDensNonneg_thm
theorem massIndep : MassIndepStatement := st_massIndep_of ReciprocityTheory.AnForm.A.parts_thm

end

end ReciprocityTheory.AnForm.M
