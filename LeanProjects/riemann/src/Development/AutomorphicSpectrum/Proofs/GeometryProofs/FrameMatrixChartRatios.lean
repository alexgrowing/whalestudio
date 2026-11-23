import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem det_mul_eq_sum {R : Type*} [CommRing R] {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p]
    [DecidableEq p] (A : Matrix m p R) (C : Matrix p m R) :
    (A * C).det = ∑ f : m → p, (∏ i, A i (f i)) * (C.submatrix f id).det := by
  have h : (A * C) = fun i => ∑ j, A i j • C j := by
    ext i k
    simp [Matrix.mul_apply, Finset.sum_apply]
  calc (A * C).det = Matrix.detRowAlternating (fun i => ∑ j, A i j • C j) := by rw [h]; rfl
    _ = ∑ f : m → p, Matrix.detRowAlternating (fun i => A i (f i) • C (f i)) :=
        (Matrix.detRowAlternating (n := m) (R := R)).toMultilinearMap.map_sum _
    _ = _ := by
        refine Finset.sum_congr rfl fun f _ => ?_
        have := (Matrix.detRowAlternating (n := m) (R := R)).toMultilinearMap.map_smul_univ
          (fun i => A i (f i)) (fun i => C (f i))
        exact this.trans (by rw [smul_eq_mul]; rfl)

theorem adjoin_int_mem {K : Type*} [Field K] (L : Subfield K) {t : Set K} (ht : ∀ a ∈ t, a ∈ L) {g : K}
    (hg : g ∈ Algebra.adjoin ℤ t) : g ∈ L := by
  induction hg using Algebra.adjoin_induction with
  | mem a ha => exact ht a ha
  | algebraMap n => simpa using intCast_mem L n
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem exists_div_of_mem_closure {K : Type*} [Field K] [Algebra ℤ K] {t : Set K} {a : K} (ha : a ∈ Subfield.closure t) :
    ∃ g ∈ Algebra.adjoin ℤ t, ∃ h ∈ Algebra.adjoin ℤ t, h ≠ 0 ∧ a = g / h := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 ha
  have key : ∀ w ∈ Subring.closure t, w ∈ Algebra.adjoin ℤ t := by
    intro w hw
    induction hw using Subring.closure_induction with
    | mem a ha => exact Algebra.subset_adjoin ha
    | zero => exact zero_mem _
    | one => exact one_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | neg a _ ha => exact neg_mem ha
    | mul a b _ _ ha hb => exact mul_mem ha hb
  by_cases h0 : z = 0
  · exact ⟨0, zero_mem _, 1, one_mem _, one_ne_zero, by simp [h0]⟩
  · exact ⟨y, key y hy, z, key z hz, h0, rfl⟩

variable {Ω : Type} [Field Ω] {S : Type} {r : S → ℕ}

theorem genU_of_lt (s : S) {l k : Fin (r s)} (h : l < k) : genU Ω r s l k = 0 := by
  have h1 : ¬ k < l := not_lt.2 h.le
  simp [genU, h1, h.ne]

theorem genU_self (s : S) (k : Fin (r s)) : genU Ω r s k k = 1 := by
  simp [genU]

theorem det_genU_rows (s : S) (k l : Fin (r s)) (hkl : k ≤ l) :
    ((genU Ω r s).submatrix
      (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then l else Fin.castLE k.2 i) (Fin.castLE k.2)).det
      = genU Ω r s l k := by
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_castSucc]
    have h1 : ∀ i : Fin (k : ℕ), (genU Ω r s).submatrix
        (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then l else Fin.castLE k.2 i) (Fin.castLE k.2)
        i.castSucc i.castSucc = 1 := by
      intro i
      have : ((i.castSucc : Fin ((k : ℕ) + 1)) : ℕ) ≠ k := by simpa using i.2.ne
      simp only [Matrix.submatrix_apply, if_neg this]
      exact genU_self s _
    simp only [h1, Finset.prod_const_one, one_mul, Matrix.submatrix_apply, Fin.val_last, if_true]
    congr 1
  · intro i j hij
    have hij' : i < j := hij
    have hi : (i : ℕ) ≠ k := by
      have := j.2
      have : (i : ℕ) < j := hij'
      omega
    simp only [Matrix.submatrix_apply, if_neg hi]
    exact genU_of_lt s (show Fin.castLE k.2 i < Fin.castLE k.2 j from hij')

variable {E : Type} [AddCommGroup E] [Module Ω E] {n : S → ℕ}

theorem map_mul_flagMat (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S)
    (B : Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) :
    B.map (algebraMap Ω (GenField Ω r)) * flagMat φ c s = genU Ω r s := by
  have h : Matrix.of (fun j l => algebraMap Ω (GenField Ω r) (φ s j (c s l))) =
      (Matrix.of (fun j l => φ s j (c s l))).map (algebraMap Ω (GenField Ω r)) := by
    ext j l
    simp
  rw [flagMat, h, ← Matrix.mul_assoc, ← Matrix.map_mul, hB]
  simp

theorem det_genU_submatrix (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S)
    (B : Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) {d : ℕ} (hd : d ≤ r s)
    (R : Fin d → Fin (r s)) :
    ((genU Ω r s).submatrix R (Fin.castLE hd)).det =
      ∑ f : Fin d → Fin (n s), (∏ i, algebraMap Ω (GenField Ω r) (B (R i) (f i))) *
        ((flagMat φ c s).submatrix f (Fin.castLE hd)).det := by
  classical
  have h : (genU Ω r s).submatrix R (Fin.castLE hd) =
      ((B.map (algebraMap Ω (GenField Ω r))).submatrix R id) *
        ((flagMat φ c s).submatrix id (Fin.castLE hd)) := by
    rw [← map_mul_flagMat φ c s B hB]
    ext i j
    simp [Matrix.mul_apply]
  rw [h, det_mul_eq_sum]
  simp [Matrix.submatrix_submatrix]

theorem ratio_update {Q : Type*} [Fintype Q] [DecidableEq Q] {T : Q → Type*} {K : Type*} [Field K]
    (D : ∀ q, T q → K) (ρ : ∀ q, T q) (hρ : ∀ q, D q (ρ q) ≠ 0) (q : Q) (f : T q) (a : K) (ha : a ≠ 0) :
    (a * ∏ q', D q' (Function.update ρ q f q')) / (a * ∏ q', D q' (ρ q')) = D q f / D q (ρ q) := by
  have hP : (∏ q' ∈ Finset.univ.erase q, D q' (ρ q')) ≠ 0 := Finset.prod_ne_zero_iff.2 fun q _ => hρ q
  rw [mul_div_mul_left _ _ ha, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q),
    ← Finset.mul_prod_erase Finset.univ (fun q' => D q' (ρ q')) (Finset.mem_univ q),
    Function.update_self,
    Finset.prod_congr rfl (g := fun q' => D q' (ρ q'))
      (fun q' hq' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hq')])]
  exact mul_div_mul_right _ _ hP

theorem exists_minor_ne_zero (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S)
    (B : Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) (k : Fin (r s)) :
    ∃ f : Fin ((k : ℕ) + 1) → Fin (n s), ((flagMat φ c s).submatrix f (Fin.castLE k.2)).det ≠ 0 := by
  by_contra hall
  push_neg at hall
  have h1 := det_genU_submatrix φ c s B hB k.2
    (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then k else Fin.castLE k.2 i)
  rw [det_genU_rows s k k le_rfl, genU_self, Finset.sum_eq_zero (fun f _ => by rw [hall f, mul_zero])] at h1
  exact one_ne_zero h1

theorem genU_mem (L : Subfield (GenField Ω r)) (hbase : ∀ b : Ω, algebraMap Ω (GenField Ω r) b ∈ L)
    (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S)
    (B : Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) (k l : Fin (r s)) (hkl : k ≤ l)
    (ρ : Fin ((k : ℕ) + 1) → Fin (n s)) (hρ : ((flagMat φ c s).submatrix ρ (Fin.castLE k.2)).det ≠ 0)
    (hminor : ∀ f : Fin ((k : ℕ) + 1) → Fin (n s), ((flagMat φ c s).submatrix f (Fin.castLE k.2)).det /
        ((flagMat φ c s).submatrix ρ (Fin.castLE k.2)).det ∈ L) :
    genU Ω r s l k ∈ L := by
  have hrows : ∀ R : Fin ((k : ℕ) + 1) → Fin (r s),
      ((genU Ω r s).submatrix R (Fin.castLE k.2)).det /
        ((flagMat φ c s).submatrix ρ (Fin.castLE k.2)).det ∈ L := by
    intro R
    rw [det_genU_submatrix φ c s B hB k.2 R, Finset.sum_div]
    refine sum_mem fun f _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (prod_mem fun i _ => hbase _) (hminor f)
  have h1 := hrows (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then l else Fin.castLE k.2 i)
  rw [det_genU_rows s k l hkl] at h1
  have h0 := hrows (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then k else Fin.castLE k.2 i)
  rw [det_genU_rows s k k le_rfl, genU_self] at h0
  have := div_mem h1 h0
  rwa [div_div_div_cancel_right₀ hρ, div_one] at this

theorem mem_of_genU_mem (L : Subfield (GenField Ω r)) (hbase : ∀ b : Ω, algebraMap Ω (GenField Ω r) b ∈ L)
    (hentry : ∀ (s : S) (k l : Fin (r s)), k ≤ l → genU Ω r s l k ∈ L) (a : GenField Ω r) : a ∈ L := by
  have hpoly : ∀ p : MvPolynomial (GenIx r) Ω,
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) p ∈ L := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C b =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact hbase b
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      obtain ⟨s, ⟨⟨l, k⟩, h⟩⟩ := i
      have := hentry s k l (le_of_lt h)
      rwa [genU, dif_pos h] at this
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (GenIx r) Ω) a
  exact div_mem (hpoly p) (hpoly q)

theorem base_mem (L : Subfield (GenField Ω r)) {κ : Type} (x : κ → Ω) (c₀ : κ)
    (hΩ : ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h)
    (hgen : ∀ j, algebraMap Ω (GenField Ω r) (x j / x c₀) ∈ L) (b : Ω) :
    algebraMap Ω (GenField Ω r) b ∈ L := by
  have hgen' : ∀ b ∈ (Set.range fun j => x j / x c₀), b ∈ L.comap (algebraMap Ω (GenField Ω r)) := by
    rintro _ ⟨j, rfl⟩
    exact hgen j
  obtain ⟨g, hg, h, hh, -, rfl⟩ := hΩ b
  exact div_mem (adjoin_int_mem _ hgen' hg) (adjoin_int_mem _ hgen' hh)

theorem mem_of_ratio_mem [Fintype S] (κ : Type) (x : κ → Ω) (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (c : ∀ s, Fin (r s) → E) (c₀ : κ) (hx0 : x c₀ ≠ 0)
    (hΩ : ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h)
    (B : ∀ s, Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : ∀ s, B s * Matrix.of (fun j l => φ s j (c s l)) = 1)
    (ρ : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
    (hρ : ∀ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (ρ q) (Fin.castLE q.2.2)).det ≠ 0)
    (L : Subfield (GenField Ω r))
    (hratio : ∀ j : FlagIx κ n r, flagCoord κ x φ c j / flagCoord κ x φ c (c₀, ρ) ∈ L)
    (a : GenField Ω r) : a ∈ L := by
  classical
  have hxK : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 :=
    (map_ne_zero (algebraMap Ω (GenField Ω r))).2 hx0
  have hP : (∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (ρ q) (Fin.castLE q.2.2)).det) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun q _ => hρ q
  have hbase : ∀ b : Ω, algebraMap Ω (GenField Ω r) b ∈ L := by
    refine base_mem L x c₀ hΩ fun j => ?_
    have h := hratio (j, ρ)
    have e : flagCoord κ x φ c (j, ρ) / flagCoord κ x φ c (c₀, ρ) =
        algebraMap Ω (GenField Ω r) (x j / x c₀) := by
      rw [map_div₀]
      exact mul_div_mul_right _ _ hP
    rwa [e] at h
  have hminor : ∀ (q : Σ s, Fin (r s)) (f : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      ((flagMat φ c q.1).submatrix f (Fin.castLE q.2.2)).det /
        ((flagMat φ c q.1).submatrix (ρ q) (Fin.castLE q.2.2)).det ∈ L := by
    intro q f
    have h := hratio (c₀, Function.update ρ q f)
    have e := ratio_update (fun (q : Σ s, Fin (r s)) (g : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) =>
      ((flagMat φ c q.1).submatrix g (Fin.castLE q.2.2)).det) ρ hρ q f _ hxK
    exact e ▸ h
  exact mem_of_genU_mem L hbase (fun s k l hkl => genU_mem L hbase φ c s (B s) (hB s) k l hkl (ρ ⟨s, k⟩)
    (hρ ⟨s, k⟩) (hminor ⟨s, k⟩)) a

theorem flagCoord_generate (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) [Fintype S]
    (r n : S → ℕ) (κ : Type) (x : κ → Ω) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (c₀ : κ)
    (hx0 : x c₀ ≠ 0)
    (hΩ : ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h)
    (hB : ∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (c s l)) = 1) :
    ∃ J₀ : FlagIx κ n r, flagCoord κ x φ c J₀ ≠ 0 ∧ ∀ a : GenField Ω r,
      ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀),
        h ≠ 0 ∧ a = g / h := by
  classical
  choose B hB using hB
  have hne : ∀ q : (Σ s, Fin (r s)), ∃ f : Fin ((q.2 : ℕ) + 1) → Fin (n q.1),
      ((flagMat φ c q.1).submatrix f (Fin.castLE q.2.2)).det ≠ 0 :=
    fun q => exists_minor_ne_zero φ c q.1 (B q.1) (hB q.1) q.2
  choose ρ hρ using hne
  have hF0 : flagCoord κ x φ c (c₀, ρ) ≠ 0 :=
    mul_ne_zero ((map_ne_zero (algebraMap Ω (GenField Ω r))).2 hx0)
      (Finset.prod_ne_zero_iff.2 fun q _ => hρ q)
  refine ⟨(c₀, ρ), hF0, fun a => ?_⟩
  apply exists_div_of_mem_closure
  exact mem_of_ratio_mem κ x φ c c₀ hx0 hΩ B hB ρ hρ (Subfield.closure _)
    (fun j => Subfield.subset_closure (Set.mem_range_self j)) a

end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
