import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulEqSumVecMulVecSpanningFamily
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.SumSqFunctional

open Matrix

def quadR {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * (L i j : ℝ) * v j

lemma quadR_eq {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℝ) :
    star v ⬝ᵥ (L.map (Int.cast : ℤ → ℝ)) *ᵥ v = quadR L v := by
  simp [quadR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

lemma quadR_intCast {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (w : Fin r → ℤ) :
    quadR L (fun i => (w i : ℝ)) = ((w ⬝ᵥ L *ᵥ w : ℤ) : ℝ) := by
  simp [quadR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

lemma continuous_quadR {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) : Continuous (quadR L) := by
  unfold quadR; fun_prop

lemma exists_int_multiple {r : ℕ} (q : Fin r → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ w : Fin r → ℤ, ∀ i, (w i : ℚ) = d * q i := by
  refine ⟨∏ i, (q i).den, Finset.prod_pos (fun i _ => (q i).den_pos), ?_⟩
  have : ∀ i, ∃ z : ℤ, (z : ℚ) = ((∏ j, (q j).den : ℕ) : ℚ) * q i := by
    intro i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
    refine ⟨k * (q i).num, ?_⟩
    rw [hk]; push_cast
    rw [mul_comm ((q i).den : ℚ) (k : ℚ), mul_assoc, Rat.den_mul_eq_num]
  choose w hw using this
  exact ⟨w, hw⟩

lemma quadR_pos_rat {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ)
    (hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v) (q : Fin r → ℚ) (hq : q ≠ 0) :
    0 < quadR L (fun i => (q i : ℝ)) := by
  obtain ⟨d, hd, w, hw⟩ := exists_int_multiple q
  have hwR : ∀ i, (w i : ℝ) = d * (q i : ℝ) := by
    intro i; have := congrArg (Rat.cast : ℚ → ℝ) (hw i); push_cast at this; exact this
  have hw0 : w ≠ 0 := by
    intro h; apply hq; funext i
    have := hw i; rw [h] at this; simp at this
    rcases this with h1 | h1
    · exact absurd h1 (by exact_mod_cast hd.ne')
    · exact h1
  have h1 := hp w hw0
  have h2 : quadR L (fun i => (w i : ℝ)) = (d : ℝ) ^ 2 * quadR L (fun i => (q i : ℝ)) := by
    simp only [quadR, hwR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h3 : 0 < quadR L (fun i => (w i : ℝ)) := by
    rw [quadR_intCast]; exact_mod_cast h1
  rw [h2] at h3
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  exact pos_of_mul_pos_right h3 hd2.le

lemma quadR_nonneg {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ)
    (hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v) (x : Fin r → ℝ) : 0 ≤ quadR L x := by
  have hdense : DenseRange (Pi.map (fun (_ : Fin r) (t : ℚ) => (t : ℝ))) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hcl : IsClosed {x : Fin r → ℝ | 0 ≤ quadR L x} :=
    isClosed_le continuous_const (continuous_quadR L)
  have hsub : Set.range (Pi.map (fun (_ : Fin r) (t : ℚ) => (t : ℝ))) ⊆ {x | 0 ≤ quadR L x} := by
    rintro _ ⟨q, rfl⟩
    by_cases hq : q = 0
    · subst hq; simp [quadR]
    · exact (quadR_pos_rat L hp q hq).le
  have := hcl.closure_subset_iff.mpr hsub
  rw [hdense.closure_range] at this
  exact this (Set.mem_univ x)

theorem posDef_of_pos_int {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (hs : Lᵀ = L)
    (hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v) :
    (L.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hH : (L.map (Int.cast : ℤ → ℝ)).IsHermitian := by
    ext i j
    have := congrFun (congrFun hs j) i
    simp only [Matrix.transpose_apply] at this
    simp [Matrix.conjTranspose_apply, this]
  have hPSD : (L.map (Int.cast : ℤ → ℝ)).PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH (fun x => by
      rw [quadR_eq]; exact quadR_nonneg L hp x)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH (fun x hx => ?_)
  rw [quadR_eq]
  refine lt_of_le_of_ne (quadR_nonneg L hp x) (fun h0 => ?_)
  have hz : (L.map (Int.cast : ℤ → ℝ)) *ᵥ x = 0 := by
    rw [← hPSD.dotProduct_mulVec_zero_iff, quadR_eq]; exact h0.symm
  have hdetR : (L.map (Int.cast : ℤ → ℝ)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hz⟩
  have hdet : L.det = 0 := by
    have := (Int.castRingHom ℝ).map_det L
    rw [RingHom.mapMatrix_apply] at this
    simp only [eq_intCast] at this
    have h' : ((L.det : ℤ) : ℝ) = 0 := by rw [this]; exact hdetR
    exact_mod_cast h'
  obtain ⟨w, hw, hLw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have := hp w hw
  rw [hLw, dotProduct_zero] at this
  exact lt_irrefl _ this

end GlobalTheory.Poinc.SumSqFunctional

namespace GlobalTheory.Poinc.SumSqFunctional

open Matrix

theorem sumsq_functional : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), (∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → 0 < lam (GlobalTheory.PolFan.sqForm l)) → ∃ (D m : ℕ) (a : Fin m → X), 1 ≤ D ∧ Submodule.span ℤ (Set.range a) = ⊤ ∧ ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → ∑ i, β (a i) (a i) = (D : ℤ) * lam β := by
  intro X _ _ _ lam hpos
  let b : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ X))) ℤ X :=
    (Module.Free.chooseBasis ℤ X).reindex (Fintype.equivFin _)
  set r := Fintype.card (Module.Free.ChooseBasisIndex ℤ X)
  let C : Fin r → Fin r → LinearMap.BilinForm ℤ X := fun i j =>
    (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)
  have hexp : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (b i) (b j) • C i j := by
    intro β
    refine b.ext fun k => b.ext fun l => ?_
    simp [C, LinearMap.sum_apply, Finsupp.single_apply]
  have hbil : ∀ (β : LinearMap.BilinForm ℤ X) (c d : Fin r → ℤ),
      β (∑ i, c i • b i) (∑ j, d j • b j) = ∑ i, ∑ j, c i * d j * β (b i) (b j) := by
    intro β c d
    simp [map_sum, map_smul, LinearMap.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    rw [Finset.sum_comm]
  let L : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => lam (C i j) + lam (C j i)
  have hlam : ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) →
      2 * lam β = ∑ i, ∑ j, L i j * β (b i) (b j) := by
    intro β hβ
    have h1 : lam β = ∑ i, ∑ j, β (b i) (b j) * lam (C i j) := by
      conv_lhs => rw [hexp β]
      simp [map_sum, map_smul]
    have h2 : lam β = ∑ i, ∑ j, β (b i) (b j) * lam (C j i) := by
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hβ]
    calc 2 * lam β = lam β + lam β := by ring
      _ = _ := by
        nth_rewrite 1 [h1]
        rw [h2]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [L, Matrix.of_apply]; ring
  have hs : Lᵀ = L := by
    ext i j; simp [L, add_comm]
  have hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v := by
    intro v hv
    let l : X →ₗ[ℤ] ℤ := ∑ i, v i • b.coord i
    have hl : ∀ k, l (b k) = v k := by
      intro k; simp [l, Finsupp.single_apply]
    have hl0 : l ≠ 0 := by
      intro h; apply hv; funext k; rw [← hl k, h]; rfl
    have hsq : ∀ x y, GlobalTheory.PolFan.sqForm l x y = l x * l y := by
      intro x y; simp [GlobalTheory.PolFan.sqForm]
    have hsym : ∀ x y, GlobalTheory.PolFan.sqForm l x y = GlobalTheory.PolFan.sqForm l y x := by
      intro x y; rw [hsq, hsq, mul_comm]
    have h2 := hlam _ hsym
    have h3 : v ⬝ᵥ L *ᵥ v = 2 * lam (GlobalTheory.PolFan.sqForm l) := by
      rw [h2]
      simp only [hsq, hl, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h3]; have := hpos l hl0; omega
  have hPD := posDef_of_pos_int L hs hp
  obtain ⟨D, m, a', hD, hspan, hsum⟩ := GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span r L hPD
  have hentry : ∀ i j, (D : ℤ) * L i j = ∑ k, a' k i * a' k j := by
    intro i j
    have := congrFun (congrFun hsum i) j
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
  refine ⟨2 * D, m, fun k => ∑ i, a' k i • b i, by omega, ?_, ?_⟩
  · have hfun : (fun k => ∑ i, a' k i • b i) = ⇑b.equivFun.symm.toLinearMap ∘ a' := by
      funext k; simp [Module.Basis.equivFun_symm_apply]
    rw [hfun, Set.range_comp, Submodule.span_image, hspan, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr b.equivFun.symm.surjective
  · intro β hβ
    simp only [hbil]
    rw [Finset.sum_comm]
    have : ∀ i, (∑ y, ∑ x, a' y i * a' y x * β (b i) (b x)) = ∑ j, (D : ℤ) * L i j * β (b i) (b j) := by
      intro i
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hentry, Finset.sum_mul]
    simp only [this]
    have h2 := hlam β hβ
    push_cast
    rw [mul_comm 2 (D : ℤ), mul_assoc, h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.Poinc.SumSqFunctional
