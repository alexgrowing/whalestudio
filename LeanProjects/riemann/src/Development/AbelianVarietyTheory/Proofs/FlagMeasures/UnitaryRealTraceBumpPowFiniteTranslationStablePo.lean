import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg.PeakPoly

def coord (n : ℕ) : Option ((Fin n × Fin n) × Bool) → Matrix (Fin n) (Fin n) ℂ → ℂ
  | none, _ => 1
  | some ((i, j), false), g => g i j
  | some ((i, j), true), g => star (g i j)

theorem continuous_coord (n : ℕ) (d : Option ((Fin n × Fin n) × Bool)) : Continuous (coord n d) := by
  rcases d with _ | ⟨⟨i, j⟩, _ | _⟩
  · exact continuous_const
  · exact continuous_id.matrix_elem i j
  · exact (continuous_id.matrix_elem i j).star

theorem prod_expand {ι D X : Type*} [Fintype ι] [DecidableEq ι] [Fintype D]
    (x : D → X → ℂ) (c : ι → D → ℂ) (g : X) :
    ∏ j, ∑ e, c j e * x e g = ∑ t : ι → D, (∏ j, c j (t j)) * ∏ j, x (t j) g := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_mul_distrib]

theorem coord_translate (n : ℕ) (a : Matrix (Fin n) (Fin n) ℂ) (d : Option ((Fin n × Fin n) × Bool)) :
    ∃ T : Option ((Fin n × Fin n) × Bool) → ℂ, ∀ g, coord n d (a * g) = ∑ e, T e * coord n e g := by
  have hmem : (fun g => coord n d (a * g)) ∈ Submodule.span ℂ (Set.range (coord n)) := by
    rcases d with _ | ⟨⟨i, j⟩, _ | _⟩
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n none (a * g)) = coord n none := by
        funext g; rfl
      rw [this]; exact Submodule.subset_span ⟨none, rfl⟩
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n (some ((i, j), false)) (a * g)) =
          ∑ l, a i l • coord n (some ((l, j), false)) := by
        funext g; simp [coord, Matrix.mul_apply, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n (some ((i, j), true)) (a * g)) =
          ∑ l, star (a i l) • coord n (some ((l, j), true)) := by
        funext g; simp [coord, Matrix.mul_apply, Finset.sum_apply, star_sum, mul_comm]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  obtain ⟨T, hT⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨T, fun g => ?_⟩
  have := congrFun hT g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

theorem peak_expand (n : ℕ) :
    ∃ c : Option ((Fin n × Fin n) × Bool) → ℂ, ∀ g, ((peak n g : ℝ) : ℂ) = ∑ e, c e * coord n e g := by
  have hmem : (fun g => ((peak n g : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range (coord n)) := by
    have : (fun g => ((peak n g : ℝ) : ℂ)) = (1 / 2 : ℂ) • coord n none +
        ∑ i, (1 / (4 * (n : ℂ))) • (coord n (some ((i, i), false)) + coord n (some ((i, i), true))) := by
      funext g
      simp only [peak, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, coord]
      push_cast
      rw [Complex.re_eq_add_conj, ← Finset.mul_sum, Finset.sum_add_distrib, Matrix.trace,
        map_sum]
      simp only [Matrix.diag, Complex.star_def]
      ring
    rw [this]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)) ?_
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨c, fun g => ?_⟩
  have := congrFun hc g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

end GlobalTheory.KFinAvg.PeakPoly

namespace GlobalTheory.KFinAvg
open PeakPoly

theorem peak_pow_polynomial : ∀ n m : ℕ, ∃ (N : ℕ) (b : Fin N → Matrix (Fin n) (Fin n) ℂ → ℂ) (c : Fin N → ℂ),
    (∀ j, Continuous (b j)) ∧ (∀ g, ((GlobalTheory.KFinAvg.peak n g ^ m : ℝ) : ℂ) = ∑ j, c j * b j g) ∧
    ∀ (a : Matrix (Fin n) (Fin n) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g := by
  intro n m
  classical
  let e := Fintype.equivFin (Fin m → Option ((Fin n × Fin n) × Bool))
  let bS : (Fin m → Option ((Fin n × Fin n) × Bool)) → Matrix (Fin n) (Fin n) ℂ → ℂ :=
    fun s g => ∏ j, coord n (s j) g
  obtain ⟨c0, hc0⟩ := peak_expand n
  refine ⟨Fintype.card (Fin m → Option ((Fin n × Fin n) × Bool)), fun i => bS (e.symm i),
    fun i => ∏ j, c0 (e.symm i j), ?_, ?_, ?_⟩
  · intro i
    exact continuous_finset_prod _ fun j _ => continuous_coord n _
  · intro g
    have h1 : ((peak n g ^ m : ℝ) : ℂ) = ∏ _j : Fin m, ∑ d, c0 d * coord n d g := by
      rw [Complex.ofReal_pow, hc0 g, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [h1, prod_expand (fun d g => coord n d g) (fun _ => c0) g]
    exact (Equiv.sum_comp e.symm (fun t => (∏ j, c0 (t j)) * ∏ j, coord n (t j) g)).symm
  · intro a i
    choose T hT using fun j => coord_translate n a (e.symm i j)
    refine ⟨fun k => ∏ j, T j (e.symm k j), fun g => ?_⟩
    show ∏ j, coord n (e.symm i j) (a * g) = _
    simp_rw [hT]
    rw [prod_expand (fun d g => coord n d g) T g]
    exact (Equiv.sum_comp e.symm (fun t => (∏ j, T j (t j)) * ∏ j, coord n (t j) g)).symm

end GlobalTheory.KFinAvg
