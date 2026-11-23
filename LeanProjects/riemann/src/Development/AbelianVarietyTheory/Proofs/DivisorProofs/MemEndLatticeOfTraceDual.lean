import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

namespace GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def rankOneHerm (G : Matrix (Fin r) (Fin r) E) (l y : Fin r → E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b => l a * ∑ k, G b k * cc (y k)

theorem rankOneHerm_mulVec (G : Matrix (Fin r) (Fin r) E) (l y x : Fin r → E) :
    rankOneHerm G l y *ᵥ x = herm G x y • l := by
  ext a
  simp only [rankOneHerm, mulVec, dotProduct, of_apply, Pi.smul_apply, smul_eq_mul, herm]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem trace_mul_rankOneHerm (G Y : Matrix (Fin r) (Fin r) E) (l y : Fin r → E) :
    (Y * rankOneHerm G l y).trace = herm G (Y *ᵥ l) y := by
  simp only [trace, diag, mul_apply, rankOneHerm, of_apply, herm, mulVec, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem rankOneHerm_mem_endLat {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hΛ : SelfDualLat G Λ) {l y : Fin r → E} (hl : l ∈ Λ) (hy : y ∈ Λ) :
    rankOneHerm G l y ∈ endLat Λ := fun x hx => by
  rw [rankOneHerm_mulVec]
  exact smul_mem_of_isIntegral (((hΛ.2.2.2.2 x).mpr hx) y hy) hl

theorem mem_endLat_of_trace_integral (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E)
    (hΛ : SelfDualLat G Λ) (hY : ∀ Z ∈ endLat Λ, IsIntegral ℤ (Y * Z).trace) : Y ∈ endLat Λ := by
  intro l hl
  refine (hΛ.2.2.2.2 _).mp fun y hy => ?_
  rw [← trace_mul_rankOneHerm]
  exact hY _ (rankOneHerm_mem_endLat hΛ hl hy)

end GlobalTheory.LieDisc
