import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix Polynomial PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.DenseAlg₂
open LateralTheory.DivDb

variable {C : Type} [Field C]

theorem pow_intertwine {N n : ℕ} (y : Mat C N) (z : Mat C n) (T : Matrix (Fin N) (Fin n) C)
    (h : y * T = T * z) : ∀ k : ℕ, y ^ k * T = T * z ^ k
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, pow_intertwine y z T h k,
      Matrix.mul_assoc]

theorem aeval_intertwine {N n : ℕ} (y : Mat C N) (z : Mat C n) (T : Matrix (Fin N) (Fin n) C)
    (h : y * T = T * z) (q : C[X]) : aeval y q * T = T * aeval z q := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, pow_intertwine y z T h k]

theorem sep_of_roots {n : ℕ} (q : C[X]) (hm : q.Monic) (hd : q.natDegree = n) (l : Fin n → C)
    (hl : Function.Injective l) (hr : ∀ j, q.IsRoot (l j)) : q.Separable := by
  classical
  have hq0 : q ≠ 0 := hm.ne_zero
  have hnd : ((Finset.univ : Finset (Fin n)).val.map l).Nodup := Multiset.Nodup.map hl Finset.univ.nodup
  have hle : (Finset.univ : Finset (Fin n)).val.map l ≤ q.roots := (Multiset.le_iff_subset hnd).2 fun a ha => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 ha
    exact (mem_roots hq0).2 (hr j)
  have hcs : Multiset.card ((Finset.univ : Finset (Fin n)).val.map l) = n := by simp
  have heq : (Finset.univ : Finset (Fin n)).val.map l = q.roots :=
    Multiset.eq_of_le_of_card_le hle (by rw [hcs, ← hd]; exact card_roots' q)
  have hcard : Multiset.card q.roots = q.natDegree := by rw [← heq, hcs, hd]
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard
  rw [← heq, Multiset.map_map] at hprod
  have e : (∏ j, (X - Polynomial.C (l j))) = q := by rw [← hprod, Finset.prod_eq_multiset_prod]; rfl
  exact e ▸ separable_prod_X_sub_C_iff.2 hl

theorem isRoot_of_aeval {N : ℕ} (y : Mat C N) (q : C[X]) (hq : aeval y q = 0) (l : C)
    (hl : y.charpoly.IsRoot l) : q.IsRoot l := by
  have h1 : l ∈ spectrum C y := Matrix.mem_spectrum_of_isRoot_charpoly hl
  have h2 := spectrum.subset_polynomial_aeval y q ⟨l, h1, rfl⟩
  rw [hq, spectrum.mem_iff, sub_zero] at h2
  by_contra hne
  exact h2 ((IsUnit.mk0 (q.eval l) hne).map (algebraMap C (Mat C N)))

theorem DenseAlg_of (hCh : Chain) (hSP : SepPoly) : DenseAlg := by
  intro Γ C _ _ _ N n ρ r A B hSub U g m hm hE
  obtain ⟨hBA, hint, hspan⟩ := hSub
  have hr : ∀ h : Γ, B * (ρ h : Mat C N) * A = (r h : Mat C n) := fun h => by
    rw [Matrix.mul_assoc, hint h, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
  have hgu : ∀ u : Γ, (ρ g : Mat C N) * (ρ u : Mat C N) = (ρ (g * u) : Mat C N) := fun u => by
    rw [map_mul, Units.val_mul]
  by_contra hno
  push Not at hno
  obtain ⟨f, hf⟩ := hSP C n
  let φ : Mat C N →ₗ[C] Mat C n :=
    { toFun := fun x => B * (ρ g : Mat C N) * x * A
      map_add' := fun x y => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  obtain ⟨f', hf', -⟩ := hCh C N n φ f
  have hz : ¬ (φ m).charpoly.Separable := by
    rw [hf, not_not, ← hf']
    refine hm f' fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.1 hx
    rw [hf']
    have hφu : φ (((Units.coeHom (Mat C N)).comp ρ) u) = (r (g * u) : Mat C n) := by
      show B * (ρ g : Mat C N) * (ρ u : Mat C N) * A = _
      rw [Matrix.mul_assoc B, hgu, hr]
    rw [hφu]
    by_contra h
    exact hno u hu ((hf _).2 h)
  have hyT : ∀ T : Matrix (Fin N) (Fin n) C, (∀ h, (ρ h : Mat C N) * T = T * (r h : Mat C n)) →
      ((ρ g : Mat C N) * m) * T = T * φ m := by
    intro T hT
    let ψ : Mat C N →ₗ[C] Mat C N :=
      { toFun := fun x => ((ρ g : Mat C N) * x * T - T * (B * (ρ g : Mat C N) * x * A)) * B
        map_add' := fun x y => by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul]; abel
        map_smul' := fun c x => by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, RingHom.id_apply, smul_sub] }
    have hψ : ψ m = 0 := by
      ext i j
      obtain ⟨f2, hf2, -⟩ := hCh C N N ψ (MvPolynomial.X (i, j))
      have h0 : ev m f2 = 0 := by
        refine hm f2 fun x hx => ?_
        obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.1 hx
        rw [hf2]
        have hψu : ψ (((Units.coeHom (Mat C N)).comp ρ) u) = 0 := by
          show (((ρ g : Mat C N) * (ρ u : Mat C N) * T -
            T * (B * (ρ g : Mat C N) * (ρ u : Mat C N) * A)) * B) = 0
          rw [Matrix.mul_assoc B, hgu, hr, hT, sub_self, Matrix.zero_mul]
        rw [hψu]; simp [ev]
      rw [hf2] at h0
      simpa [ev] using h0
    have h2 : ((ρ g : Mat C N) * m * T - T * φ m) * B * A = 0 := by
      have e : ψ m = ((ρ g : Mat C N) * m * T - T * φ m) * B := rfl
      rw [← e, hψ, Matrix.zero_mul]
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one] at h2
    exact sub_eq_zero.1 h2
  have hqy : aeval ((ρ g : Mat C N) * m) (φ m).charpoly = 0 := by
    apply hspan
    intro T hT
    rw [aeval_intertwine _ _ T (hyT T hT), Matrix.aeval_self_charpoly, Matrix.mul_zero]
  obtain ⟨l, hl, hlr⟩ := hE
  exact hz (sep_of_roots _ (Matrix.charpoly_monic _) (by simp [Matrix.charpoly_natDegree_eq_dim]) l hl
    fun j => isRoot_of_aeval _ _ hqy (l j) (hlr j))

end LateralTheory.DivDb.DenseAlg₂
