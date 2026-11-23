import Mathlib

noncomputable def UpperTheory.Reformulated.B.G8.kry :
    {R : Type} → [CommRing R] → {n : ℕ} → Matrix (Fin n) (Fin n) R → (Fin n → R) → Matrix (Fin n) (Fin n) R :=
    fun {R : Type} [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦ (g ^ (↑j : ℕ)).mulVec v i

open Polynomial in
private theorem UpperTheory.Reformulated.B.G8.eq_zero_of_aeval_eq_zero {K : Type} [Field K] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : g.charpoly.Separable) (p : K[X])
    (hp : p.degree < n) (h0 : aeval g p = 0) : p = 0 := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hp
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let L := AlgebraicClosure K
  let f : K →+* L := algebraMap K L
  let G : Matrix (Fin n) (Fin n) L := g.map f
  have hG : G.charpoly.Separable := by
    rw [Matrix.charpoly_map]
    exact hg.map
  have hG0 : aeval G (p.map f) = 0 := by
    have h1 := congrArg (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId K L)) h0
    rw [map_zero, ← aeval_algHom_apply] at h1
    rw [aeval_map_algebraMap]
    exact h1
  have hcard : G.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hG), ← (IsAlgClosed.splits G.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hz : p.map f = 0 := by
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero G.charpoly.roots.toFinset ?_ ?_
    · rw [hcard, degree_map]
      exact hp
    · intro x hx
      have hx' : x ∈ spectrum L G :=
        Matrix.mem_spectrum_of_isRoot_charpoly (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx))
      have h2 := spectrum.subset_polynomial_aeval G (p.map f) ⟨x, hx', rfl⟩
      rw [hG0, spectrum.zero_eq] at h2
      exact h2
  exact (Polynomial.map_eq_zero_iff f.injective).mp hz

open Polynomial in
private theorem UpperTheory.Reformulated.B.G8.exists_kry_field {K : Type} [Field K] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : g.charpoly.Separable) :
    ∃ v : Fin n → K, (UpperTheory.Reformulated.B.G8.kry g v).det ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X]
    (Module.AEval K (Fin n → K) g)
  obtain ⟨v, rfl⟩ := (Module.AEval.of K (Fin n → K) g).surjective x
  refine ⟨v, fun hdet => ?_⟩
  obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : K[X] := ∑ j : Fin n, C (c j) * X ^ (j : ℕ)
  have hdeg : p.degree < n := degree_sum_fin_lt c
  have hv : aeval g p • v = 0 := by
    rw [← hc0]
    ext i
    simp only [p, map_sum, map_mul, aeval_C, map_pow, aeval_X, Finset.sum_smul, Finset.sum_apply,
      ← Algebra.smul_def, smul_assoc, Pi.smul_apply, smul_eq_mul, Matrix.smul_eq_mulVec]
    simp only [UpperTheory.Reformulated.B.G8.kry, Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hker : p ∈ Module.annihilator K[X] (Module.AEval K (Fin n → K) g) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Module.AEval.of_aeval_smul,
      hv, map_zero]
  have hp0 : aeval g p = 0 := by
    refine Matrix.ext_iff_mulVec.mpr fun w => ?_
    have h1 := Module.mem_annihilator.mp hker (Module.AEval.of K (Fin n → K) g w)
    rw [← Module.AEval.of_aeval_smul, map_eq_zero_iff _ (LinearEquiv.injective _)] at h1
    rw [Matrix.zero_mulVec]
    exact h1
  have hp : p = 0 := UpperTheory.Reformulated.B.G8.eq_zero_of_aeval_eq_zero g hg p hdeg hp0
  apply hc
  ext j
  have h1 := congrArg (fun q => q.coeff j) hp
  simpa [p, finsetSum_coeff, coeff_X_pow, Fin.val_inj] using h1

private theorem UpperTheory.Reformulated.B.G8.kry_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S)
    (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    f (UpperTheory.Reformulated.B.G8.kry g v).det = (UpperTheory.Reformulated.B.G8.kry (g.map f) (f ∘ v)).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [UpperTheory.Reformulated.B.G8.kry, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec, Matrix.map_pow]

theorem UpperTheory.Reformulated.B.G8.exists_kry :
    ∀ {R : Type} [inst : CommRing R] [Finite (MaximalSpectrum R)] {n : ℕ} (g : Matrix (Fin n) (Fin n) R),
      g.charpoly.Separable → ∃ (v : Fin n → R), IsUnit (UpperTheory.Reformulated.B.G8.kry g v).det := by
  intro R _ _ n g hg
  have h1 : ∀ m : MaximalSpectrum R, ∃ w : Fin n → R ⧸ m.asIdeal,
      (UpperTheory.Reformulated.B.G8.kry (g.map (Ideal.Quotient.mk m.asIdeal)) w).det ≠ 0 := by
    intro m
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    refine UpperTheory.Reformulated.B.G8.exists_kry_field _ ?_
    rw [Matrix.charpoly_map]
    exact hg.map
  choose w hw using h1
  have hco : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum R => m.asIdeal) := by
    intro a b hab
    exact Ideal.isCoprime_iff_sup_eq.mpr
      (a.isMaximal.coprime_of_ne b.isMaximal fun h => hab (MaximalSpectrum.ext h))
  choose v hv using fun i : Fin n => Ideal.pi_quotient_surjective hco fun m => w m i
  refine ⟨v, ?_⟩
  by_contra hu
  obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  apply hw ⟨M, hM⟩
  have h2 : w ⟨M, hM⟩ = Ideal.Quotient.mk M ∘ v := funext fun i => (hv i ⟨M, hM⟩).symm
  rw [h2, ← UpperTheory.Reformulated.B.G8.kry_map]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
