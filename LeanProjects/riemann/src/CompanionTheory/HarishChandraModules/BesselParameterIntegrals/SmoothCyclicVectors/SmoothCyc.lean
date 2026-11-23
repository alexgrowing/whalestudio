import Mathlib
import Formalism.PeriodIntegrals.LowCyc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LowSmooth
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.IntegralMemOfIsClosed
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas

open Matrix Filter Topology Set

noncomputable section

namespace CompanionTheory.D.Upq.Sm

open PI.UpqRep

theorem dsigW_eq' {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat (2 * r + k + 1) → (H →L[ℂ] H)) :
    ∀ (W : List (Mat (2 * r + k + 1))) (v : H), dsigW (k := k) (r := r) σ W v = dsW σ W v
  | [], _ => rfl
  | X :: W, v => by
    change dsig σ X (dsigW σ W v) = ds σ X (dsW σ W v)
    rw [dsigW_eq' σ W v]; rfl

theorem conj_facts {n : ℕ} {J Hm P : Mat n} (hP : IsUnit P) (hPJ : Pᴴ * J * P = Hm) :
    (∀ a : Mat n, aᴴ * Hm * a = Hm → ∃ b : Mat n, bᴴ * J * b = J ∧ P⁻¹ * b * P = a) ∧
      ∀ b : Mat n, bᴴ * J * b = J → (P⁻¹ * b * P)ᴴ * Hm * (P⁻¹ * b * P) = Hm := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).mp hP
  have e1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hdet
  have e2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have e3 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, e2, conjTranspose_one]
  refine ⟨fun a ha => ⟨P * a * P⁻¹, ?_, ?_⟩, fun b hb => ?_⟩
  · calc (P * a * P⁻¹)ᴴ * J * (P * a * P⁻¹) = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * J * P) * a) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = ((P⁻¹)ᴴ * Pᴴ) * J * (P * P⁻¹) := by
          rw [hPJ, ha, ← hPJ]; simp only [Matrix.mul_assoc]
      _ = J := by rw [e3, e2, Matrix.one_mul, Matrix.mul_one]
  · rw [show P⁻¹ * (P * a * P⁻¹) * P = (P⁻¹ * P) * a * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      e1, Matrix.one_mul, Matrix.mul_one]
  · calc (P⁻¹ * b * P)ᴴ * Hm * (P⁻¹ * b * P)
        = Pᴴ * (bᴴ * (((P⁻¹)ᴴ * Pᴴ) * J * (P * P⁻¹)) * b) * P := by
          rw [← hPJ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Hm := by rw [e3, e2, Matrix.one_mul, Matrix.mul_one, hb, hPJ]

theorem cyc_of_smooth (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat (2 * r + k + 1) → (H →L[ℂ] H)) (w : H) (hσ : IsDSHpk k r ε lam σ) (hw0 : w ≠ 0)
    (hw : w ∈ smoothVecs (k := k) (r := r) σ) :
    ∀ x ∈ smoothVecs (k := k) (r := r) σ, ∀ Ws : List (List (Mat (2 * r + k + 1))),
    (∀ w' ∈ Ws, ∀ Y ∈ w', InLieHpk k r Y) → ∀ δ : ℝ, 0 < δ →
    ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Mat (2 * r + k + 1)),
      (∀ i, g i ∈ UH (Hpk k r)) ∧
      (Ws.map fun w' => ‖dsigW (k := k) (r := r) σ w' (x - ∑ i, c i • σ (g i) w)‖).sum < δ := by
  intro x hx Ws hWs δ hδ
  obtain ⟨P, ⟨⟨hP, hPJ⟩, -⟩, -, -, ⟨⟨h1, hm⟩, hiso, -⟩, hirr, -⟩ := hσ
  obtain ⟨hc1, hc2⟩ := conj_facts hP hPJ
  have hG : PI.IsMatGroup (UH (Hpk k r)) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  have h : RepOn (UH (Hpk k r)) σ := repOn_of_conj hP hPJ h1 hm
  have hiso' : ∀ g ∈ UH (Hpk k r), ∀ v, ‖σ g v‖ = ‖v‖ := fun g hg v => by
    obtain ⟨b, hb, rfl⟩ := hc1 g hg
    exact hiso b hb v
  have hwm : w ∈ orbSpan (UH (Hpk k r)) σ w :=
    Submodule.subset_span ⟨1, h.one_mem, by simp [h.map_one]⟩
  have hd : Dense (orbSpan (UH (Hpk k r)) σ w : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    refine (hirr _ (Submodule.isClosed_topologicalClosure _) fun b hb v hv => ?_).resolve_left
      fun h0 => hw0 ?_
    · exact map_mem_closure (σ (P⁻¹ * b * P)).continuous hv
        fun y hy => apply_mem_orbSpan h (hc2 b hb) hy
    · have := Submodule.le_topologicalClosure _ hwm
      rwa [h0, Submodule.mem_bot] at this
  have hL : (0 : ℝ) < Ws.length + 1 := by positivity
  obtain ⟨y, hy, hxy⟩ := exists_approx hG h hiso' hw hd hx (ι := Fin Ws.length) (W := Ws.get)
    (fun i X hX t => ex_mem_of_lie (hWs _ (List.get_mem _ _) X hX) t) (div_pos hδ hL)
  obtain ⟨N, c, g, hcg⟩ := Submodule.mem_span_set'.1 hy
  choose a ha hag using fun i => (g i).2
  refine ⟨N, c, a, ha, ?_⟩
  have e : ∑ i, c i • σ (a i) w = y := by
    rw [← hcg]
    exact Finset.sum_congr rfl fun i _ => by rw [← hag i]
  rw [e]
  have hle := List.sum_le_card_nsmul
    (Ws.map fun w' => ‖dsigW (k := k) (r := r) σ w' (x - y)‖) (δ / (Ws.length + 1)) (by
      intro t ht
      obtain ⟨W, hW, rfl⟩ := List.mem_map.1 ht
      obtain ⟨i, rfl⟩ := List.get_of_mem hW
      rw [dsigW_eq']
      exact (hxy i).le)
  refine hle.trans_lt ?_
  rw [List.length_map, nsmul_eq_mul, ← mul_div_assoc, div_lt_iff₀ hL]
  nlinarith

theorem smoothCyc_of_lowSmooth (hL : PI.LowSmooth) : PI.SmoothCyc :=
  fun k r ε lam H _ _ _ σ w hlam hσ hw =>
    cyc_of_smooth k r ε lam H σ w hσ
      (by
        obtain ⟨P, -, h1, -⟩ := hw
        intro h0
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1)
      (hL k r ε lam H σ w hlam hσ hw)

theorem smoothCyc_of_kFinSmooth (hK : PI.KFinSmooth) : PI.SmoothCyc :=
  smoothCyc_of_lowSmooth (PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth hK)

end CompanionTheory.D.Upq.Sm

end
