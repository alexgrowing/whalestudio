import Formalism.SuccessiveMinima.DefsMink

open MeasureTheory Module Metric Set ZSpan
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN.LowerVolumeBound

lemma cross_mem {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E} (hK : Convex ℝ K)
    (hs : ∀ x ∈ K, -x ∈ K) (h0 : (0 : E) ∈ K) {n : ℕ} (w : Fin n → E) (hw : ∀ i, w i ∈ K)
    (c : Fin n → ℝ) (hc : ∑ i, |c i| ≤ 1) : ∑ i, c i • w i ∈ K := by
  classical
  set s := ∑ i, |c i| with hsdef
  let p : Fin n → E := fun i => if 0 ≤ c i then w i else -w i
  have hp : ∀ i, p i ∈ K := fun i => by
    dsimp only [p]; split_ifs
    · exact hw i
    · exact hs _ (hw i)
  have hcp : ∀ i, c i • w i = |c i| • p i := fun i => by
    dsimp only [p]; split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h), neg_smul, smul_neg, neg_neg]
  have hs_nonneg : 0 ≤ s := Finset.sum_nonneg (fun i _ => abs_nonneg (c i))
  rcases hs_nonneg.eq_or_lt with hs0 | hs0
  · have hz : ∀ i, c i = 0 := fun i => abs_eq_zero.mp (le_antisymm
      ((Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)).trans hs0.symm.le)
      (abs_nonneg _))
    simpa [hz] using h0
  · have hx : ∑ i, (|c i| / s) • p i ∈ K :=
      hK.sum_mem (fun i _ => div_nonneg (abs_nonneg _) hs0.le)
        (by rw [← Finset.sum_div, div_self hs0.ne']) (fun i _ => hp i)
    have h2 := hK.smul_mem_of_zero_mem h0 hx ⟨hs0.le, hc⟩
    convert h2 using 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_div_cancel₀ _ hs0.ne', hcp]

lemma covol_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (bv : Basis (Fin (finrank ℝ E)) ℝ E) (hv : ∀ i, bv i ∈ L) :
    ZLattice.covolume L μ ≤ μ.real (parallelepiped bv) := by
  classical
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ L) = Fintype.card (Fin (finrank ℝ E)) := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L, Fintype.card_fin]
  let bz : Basis (Fin (finrank ℝ E)) ℤ L :=
    (Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq hcard)
  let b' : Basis (Fin (finrank ℝ E)) ℝ E := bz.ofZLatticeBasis ℝ L
  have hb' : ((↑) : L → E) ∘ bz = ⇑b' := by
    funext i; simp [b']
  have hk : ∃ k : ℤ, b'.det bv = k := by
    refine ⟨(Matrix.of fun i j => bz.repr ⟨bv j, hv j⟩ i).det, ?_⟩
    rw [Basis.det_apply, Int.cast_det]
    congr 1
    ext i j
    rw [Basis.toMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact bz.ofZLatticeBasis_repr_apply ℝ L ⟨bv j, hv j⟩ i
  obtain ⟨k, hk⟩ := hk
  have hprod : bv.det b' * b'.det bv = 1 := by
    rw [Basis.det_mul_det, Basis.det_self]
  have hk0 : k ≠ 0 := by
    rintro rfl; simp [hk] at hprod
  have hdet : |bv.det b'| ≤ 1 := by
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
    have h2 : |bv.det b'| * |(k : ℝ)| = 1 := by rw [← abs_mul, ← hk, hprod, abs_one]
    nlinarith [abs_nonneg (bv.det b')]
  rw [ZLattice.covolume_eq_det_mul_measureReal L μ bz bv, hb',
    measureReal_congr (fundamentalDomain_ae_parallelepiped bv μ)]
  calc |bv.det b'| * μ.real (parallelepiped bv) ≤ 1 * μ.real (parallelepiped bv) := by
        gcongr
    _ = μ.real (parallelepiped bv) := one_mul _

end Formalism.FN.LowerVolumeBound
