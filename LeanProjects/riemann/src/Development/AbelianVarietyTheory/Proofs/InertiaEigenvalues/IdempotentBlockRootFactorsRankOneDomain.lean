import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockCharPolyEqCharpolyImage

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing Polynomial

namespace GlobalTheory.RootFactor

theorem aeval_sq {K : Type} [Field K] {t : ℕ} (D : Matrix (Fin t) (Fin t) K) (r : K) (q : K[X])
    (h : D.charpoly = (X - C r) * q) : aeval D q * aeval D q = q.eval r • aeval D q := by
  have hCH : aeval D (X - C r) * aeval D q = 0 := by
    rw [← map_mul, ← h, Matrix.aeval_self_charpoly]
  obtain ⟨s, hs⟩ : ∃ s : K[X], q = s * (X - C r) + C (q.eval r) :=
    ⟨q /ₘ (X - C r), by
      have hmd := Polynomial.modByMonic_add_div q (X - C r)
      rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at hmd
      rw [mul_comm, add_comm]
      exact hmd.symm⟩
  conv_lhs => arg 1; rw [hs]
  rw [map_add, map_mul, aeval_C, add_mul, Matrix.mul_assoc, hCH, Matrix.mul_zero, zero_add,
    Algebra.smul_def]

theorem aeval_rank {K : Type} [Field K] {t : ℕ} (D : Matrix (Fin t) (Fin t) K) (r : K) (q : K[X])
    (h : D.charpoly = (X - C r) * q) (hq : q.eval r ≠ 0) : (aeval D q).rank = 1 := by
  have hCH : aeval D (X - C r) * aeval D q = 0 := by
    rw [← map_mul, ← h, Matrix.aeval_self_charpoly]
  have hDP : D * aeval D q = r • aeval D q := by
    rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.sub_mul,
      sub_eq_zero, Matrix.smul_mul, Matrix.one_mul] at hCH
    exact hCH
  have hchar : LinearMap.charpoly (Matrix.toLinAlgEquiv' D) = (X - C r) * q := by
    rw [← h]; exact Matrix.charpoly_toLin' D
  have hmult : (LinearMap.charpoly (Matrix.toLinAlgEquiv' D)).rootMultiplicity r = 1 := by
    rw [hchar, Polynomial.rootMultiplicity_mul, Polynomial.rootMultiplicity_X_sub_C_self,
      Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hq)]
    rw [← h]; exact (Matrix.charpoly_monic D).ne_zero
  have hle : LinearMap.range (aeval D q).mulVecLin ≤
      Module.End.eigenspace (Matrix.toLinAlgEquiv' D) r := by
    rintro _ ⟨v, rfl⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLinAlgEquiv'_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, hDP, Matrix.smul_mulVec]
  have hEig : Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' D) r := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar]
    simp [Polynomial.IsRoot]
  obtain ⟨v, hv⟩ := hEig.exists_hasEigenvector
  have hPv : Matrix.mulVec (aeval D q) v = q.eval r • v := by
    rw [← Matrix.toLinAlgEquiv'_apply, ← Polynomial.aeval_algHom_apply]
    exact Module.End.aeval_apply_of_hasEigenvector hv
  show Module.finrank K (LinearMap.range (aeval D q).mulVecLin) = 1
  apply le_antisymm
  · exact (Submodule.finrank_mono hle).trans (hmult ▸ LinearMap.finrank_eigenspace_le _ r)
  · rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    have hmem : Matrix.mulVec (aeval D q) v ∈ LinearMap.range (aeval D q).mulVecLin := ⟨v, rfl⟩
    rw [h0, Submodule.mem_bot, hPv] at hmem
    exact smul_ne_zero hq hv.2 hmem

private theorem aeval_list_prod_X_sub_C_mul_comm {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (hba : b * a = 1) (D : Matrix (Fin t) (Fin t) K) (ρ : ℕ → K)
    (l : List ℕ) :
    b * (l.map fun c => a * D * b - ρ c • (a * b)).prod =
      aeval D (l.map fun c => X - C (ρ c)).prod * b := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have key : b * (a * D * b - ρ c • (a * b)) = (D - ρ c • 1) * b := by
      simp only [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hba, Matrix.one_mul,
        Matrix.sub_mul, Matrix.smul_mul]
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, map_mul, ← Matrix.mul_assoc,
      key, Matrix.mul_assoc, ih, ← Matrix.mul_assoc]
    congr 2
    simp [Algebra.algebraMap_eq_smul_one]

theorem prod_eq {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K)
    (hba : b * a = 1) (D : Matrix (Fin t) (Fin t) K) (ρ : ℕ → K) (l : List ℕ) :
    (a * b) * (l.map fun c => a * D * b - ρ c • (a * b)).prod =
      a * aeval D (l.map fun c => X - C (ρ c)).prod * b := by
  rw [Matrix.mul_assoc, aeval_list_prod_X_sub_C_mul_comm a b hba D ρ l, ← Matrix.mul_assoc]

private theorem prod_Ioc_one_eq_list_range'_prod {M : Type} [CommMonoid M] (f : ℕ → M) (t : ℕ) :
    ∏ c ∈ Finset.Ioc 1 t, f c = ((List.range' 2 (t - 1)).map f).prod := by
  rw [Finset.prod_eq_multiset_prod]
  rfl

theorem field_case {K : Type} [Field K] (n t : ℕ) (e X₀ : Matrix (Fin n) (Fin n) K) (ρ : ℕ → K) (ht : 2 ≤ t)
    (he : e * e = e) (h1 : e * X₀ = X₀) (h2 : X₀ * e = X₀) (hρ : Set.InjOn ρ (Finset.Icc 1 t : Set ℕ))
    (hP : ∏ c ∈ Finset.Icc 1 t, (X - C (ρ c)) = blockPol e X₀) :
    (((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).rank = 1 ∧
    ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod *
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      (∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
  obtain ⟨a, b, hba, hab, hM⟩ := GlobalTheory.BlockCharpoly.blockPol_eq_charpoly e he rfl
  have hX : e * X₀ * e = X₀ := by rw [h1, h2]
  have hX' : a * (b * X₀ * a) * b = X₀ := by
    conv_rhs => rw [← hX, ← hab]
    simp only [Matrix.mul_assoc]
  have hcp : (b * X₀ * a).charpoly =
      (X - C (ρ 1)) * ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod := by
    rw [← hM, hX, ← hP, Finset.Icc_eq_cons_Ioc (by omega : 1 ≤ t), Finset.prod_cons,
      prod_Ioc_one_eq_list_range'_prod]
  have hev : (((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod).eval (ρ 1) =
      ∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c) := by
    rw [prod_Ioc_one_eq_list_range'_prod, Polynomial.eval_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c _
    simp
  have hne : (((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod).eval (ρ 1) ≠ 0 := by
    rw [hev, Finset.prod_ne_zero_iff]
    intro c hc hzero
    rw [Finset.mem_Ioc] at hc
    have := hρ (by simp only [Finset.coe_Icc, Set.mem_Icc]; omega)
      (by simp only [Finset.coe_Icc, Set.mem_Icc]; omega) (sub_eq_zero.mp hzero)
    omega
  have heE : e * ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
    obtain ⟨k, hk⟩ : ∃ k, t - 1 = k + 1 := ⟨t - 2, by omega⟩
    rw [hk, List.range'_succ, List.map_cons, List.prod_cons, ← Matrix.mul_assoc, Matrix.mul_sub,
      Matrix.mul_smul, h1, he]
  have hE : ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      a * aeval (b * X₀ * a) ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod * b := by
    rw [← heE, ← prod_eq a b hba (b * X₀ * a) ρ, hab]
    congr 2
    apply List.map_congr_left
    intro c _
    rw [hX']
  have hsq := aeval_sq (b * X₀ * a) (ρ 1) _ hcp
  have hrk := aeval_rank (b * X₀ * a) (ρ 1) _ hcp hne
  rw [hE, ← hev]
  generalize aeval (b * X₀ * a) ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod = R at hsq hrk
  constructor
  · apply le_antisymm
    · exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hrk.le
    · have hR : R = b * (a * R * b) * a := by
        simp only [← Matrix.mul_assoc, hba, Matrix.one_mul]
        rw [Matrix.mul_assoc, hba, Matrix.mul_one]
      calc 1 = R.rank := hrk.symm
        _ = (b * (a * R * b) * a).rank := by rw [← hR]
        _ ≤ (b * (a * R * b)).rank := Matrix.rank_mul_le_left _ _
        _ ≤ (a * R * b).rank := Matrix.rank_mul_le_right _ _
  · calc a * R * b * (a * R * b) = a * (R * R) * b := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc b a, hba, Matrix.one_mul]
      _ = _ := by rw [hsq, Matrix.mul_smul, Matrix.smul_mul]

theorem blockPol_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (e M : Matrix (Fin n) (Fin n) A) : (blockPol e M).map f = blockPol (e.map f) (M.map f) := by
  unfold blockPol
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij]

private theorem map_list_prod' {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {n : ℕ}
    (e X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O) (l : List ℕ) :
    ((l.map fun c => X₀ - ρ c • e).prod).map f = (l.map fun c => X₀.map f - f (ρ c) • e.map f).prod := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.prod_cons, Matrix.map_mul, ih, List.map_cons, List.prod_cons]
    congr 1
    ext i j
    simp

private theorem map_smul_eq_smul_map {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {n : ℕ}
    (s : O) (M : Matrix (Fin n) (Fin n) O) : (s • M).map f = f s • M.map f := by
  ext i j
  simp

theorem rank_one_and_sq {O : Type} [CommRing O] [IsDomain O] (n t : ℕ) (e X₀ : Matrix (Fin n) (Fin n) O)
    (ρ : ℕ → O) (ht : 2 ≤ t)
    (he : e * e = e) (h1 : e * X₀ = X₀) (h2 : X₀ * e = X₀) (hρ : Set.InjOn ρ (Finset.Icc 1 t : Set ℕ))
    (hP : ∏ c ∈ Finset.Icc 1 t, (X - C (ρ c)) = blockPol e X₀) :
    ((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O)).rank = 1 ∧
    ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod *
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      (∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
  have hinj : Function.Injective (toFr O) := IsFractionRing.injective O (FractionRing O)
  obtain ⟨hr, hsq⟩ := field_case (K := FractionRing O) n t (e.map (toFr O)) (X₀.map (toFr O))
    (fun c => toFr O (ρ c)) ht (by rw [← Matrix.map_mul, he]) (by rw [← Matrix.map_mul, h1])
    (by rw [← Matrix.map_mul, h2]) (fun x hx y hy hxy => hρ hx hy (hinj hxy))
    (by rw [← blockPol_map, ← hP, Polynomial.map_prod]; simp)
  refine ⟨by rw [map_list_prod']; exact hr, ?_⟩
  have hmap : (((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod *
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O) =
      ((∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) •
        ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O) := by
    rw [Matrix.map_mul, map_smul_eq_smul_map, map_list_prod', hsq, map_prod]
    simp [map_sub]
  ext i j
  exact hinj (congrFun (congrFun hmap i) j)

end GlobalTheory.RootFactor
