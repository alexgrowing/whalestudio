import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.EntriesLat

noncomputable section

namespace PI.InvTopW

open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

private theorem exists_nat_mul_lemma {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ d : ℕ, 1 ≤ d ∧ (d : E) * x ∈ Formalism.UG.intOE E := by
  have H : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * x) := by
    have hq : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    first
    | (obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) x hq
       exact ⟨m, nonZeroDivisors.coe_ne_zero m, by rw [← zsmul_eq_mul]; exact hm⟩)
    | (obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := ℚ) (nonZeroDivisors ℤ) x hq
       exact ⟨m, nonZeroDivisors.coe_ne_zero m, by rw [← zsmul_eq_mul]; exact hm⟩)
    | (obtain ⟨y, hy, h⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hq.isAlgebraic).exists_integral_multiple
       exact ⟨y, hy, by rw [← zsmul_eq_mul]; exact h⟩)
  obtain ⟨y, hy0, hint⟩ := H
  have hmem : (y : E) * x ∈ Formalism.UG.intOE E :=
    RingHom.mem_range.2 ((IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨n, Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hy0), ?_⟩
    simpa using hmem
  · refine ⟨n, Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hy0), ?_⟩
    simpa using hmem

theorem exists_nat_den {E : Type} [Field E] [NumberField E] (s : Finset E) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ x ∈ s, (d : E) * x ∈ Formalism.UG.intOE E := by
  classical
  refine Finset.induction_on s ⟨1, le_rfl, by simp⟩ ?_
  intro a s _ ih
  obtain ⟨d, hd, hds⟩ := ih
  obtain ⟨e, he, hea⟩ := exists_nat_mul_lemma a
  refine ⟨d * e, Nat.mul_pos hd he, fun x hx => ?_⟩
  rcases Finset.mem_insert.1 hx with rfl | hx
  · rw [Nat.cast_mul, mul_assoc]
    exact mul_mem (natCast_mem _ d) hea
  · rw [Nat.cast_mul, mul_comm (d : E), mul_assoc]
    exact mul_mem (natCast_mem _ e) (hds x hx)

theorem algebraMap_mem_intOE {E : Type} [Field E] [NumberField E] (a : 𝓞 E) :
    algebraMap (𝓞 E) E a ∈ Formalism.UG.intOE E := by
  first
  | exact RingHom.mem_range_self _ a
  | exact ⟨a, rfl⟩

theorem exists_den_lat {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ x ∈ L, ∀ i, (d : E) * x i ∈ Formalism.UG.intOE E := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨d, hd, hds⟩ := exists_nat_den (S.biUnion fun v => Finset.univ.image v)
  refine ⟨d, hd, fun x hx i => ?_⟩
  let K : Submodule (𝓞 E) (Fin n → E) :=
    { carrier := {x | ∀ i, (d : E) * x i ∈ Formalism.UG.intOE E}
      add_mem' := by
        intro a b ha hb i
        rw [Pi.add_apply, mul_add]
        exact add_mem (ha i) (hb i)
      zero_mem' := by
        intro i
        rw [Pi.zero_apply, mul_zero]
        exact zero_mem _
      smul_mem' := by
        intro r a ha i
        rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm]
        exact mul_mem (algebraMap_mem_intOE r) (ha i) }
  have hSK : Submodule.span (𝓞 E) (S : Set (Fin n → E)) ≤ K := by
    rw [Submodule.span_le]
    intro v hv
    show ∀ j, (d : E) * v j ∈ Formalism.UG.intOE E
    intro j
    exact hds _ (Finset.mem_biUnion.2 ⟨v, Finset.mem_coe.1 hv,
      Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩)
  rw [← hS] at hx
  exact (show ∀ i, (d : E) * x i ∈ Formalism.UG.intOE E from hSK hx) i

theorem exists_single_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (j : Fin n) : ∃ d : ℕ, 1 ≤ d ∧ (d : E) • Pi.single j (1 : E) ∈ L := by
  have hnat : ∀ (d : ℕ) (v : Fin n → E), v ∈ L → (d : E) • v ∈ L := fun d v hv => by
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv d
  let K : Submodule E (Fin n → E) :=
    { carrier := {x | ∃ d : ℕ, 1 ≤ d ∧ (d : E) • x ∈ L}
      add_mem' := by
        rintro a b ⟨d1, h1, ha⟩ ⟨d2, h2, hb⟩
        refine ⟨d1 * d2, Nat.mul_pos h1 h2, ?_⟩
        have e : ((d1 * d2 : ℕ) : E) • (a + b) = (d2 : E) • ((d1 : E) • a) + (d1 : E) • ((d2 : E) • b) := by
          rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (d2 : E) (d1 : E)]
        rw [e]
        exact add_mem (hnat d2 _ ha) (hnat d1 _ hb)
      zero_mem' := ⟨1, le_rfl, by rw [smul_zero]; exact L.zero_mem⟩
      smul_mem' := by
        rintro r x ⟨d, hd, hx⟩
        obtain ⟨d', hd', hr⟩ := exists_nat_den ({r} : Finset E)
        obtain ⟨s, hs⟩ := RingHom.mem_range.1 (hr r (Finset.mem_singleton_self r))
        refine ⟨d' * d, Nat.mul_pos hd' hd, ?_⟩
        have e : ((d' * d : ℕ) : E) • (r • x) = s • ((d : E) • x) := by
          rw [← algebraMap_smul E s ((d : E) • x), hs, smul_smul, smul_smul, Nat.cast_mul]
          congr 1
          ring
        rw [e]
        exact L.smul_mem s hx }
  have hK : Submodule.span E (L : Set (Fin n → E)) ≤ K := by
    rw [Submodule.span_le]
    intro x hx
    show ∃ d : ℕ, 1 ≤ d ∧ (d : E) • x ∈ L
    exact ⟨1, le_rfl, by rw [Nat.cast_one, one_smul]; exact hx⟩
  have hmem : Pi.single j (1 : E) ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL]
    exact Submodule.mem_top
  exact hK hmem

theorem exists_good_den {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hF : L.FG)
    (hS : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ c : ℕ, 1 ≤ c ∧ (∀ x ∈ L, ∀ i, (c : E) * x i ∈ Formalism.UG.intOE E) ∧
      ∀ j, (c : E) • Pi.single j (1 : E) ∈ L := by
  obtain ⟨d, hd, hdL⟩ := exists_den_lat L hF
  choose e he1 he2 using fun j => exists_single_mem L hS j
  refine ⟨d * ∏ j, e j, Nat.mul_pos hd (Finset.prod_pos fun j _ => he1 j), fun x hx i => ?_,
    fun j => ?_⟩
  · rw [Nat.cast_mul, mul_comm (d : E), mul_assoc]
    exact mul_mem (natCast_mem _ _) (hdL x hx i)
  · obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem e (Finset.mem_univ j)
    rw [hm, show d * (e j * m) = d * m * e j by ring, Nat.cast_mul, mul_smul,
      Nat.cast_smul_eq_nsmul]
    exact nsmul_mem (he2 j) _

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclE_mem_int (x : E) (hx : x ∈ Formalism.UG.intOE E) :
    Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x ∈ Formalism.MainNotions.S.IntAf F E := by
  first
  | exact Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)
  | (unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt Formalism.UG.inclE
     exact Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩))

theorem lat_den {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (c : ℕ)
    (hc : ∀ x ∈ L, ∀ i, (c : E) * x i ∈ Formalism.UG.intOE E) :
    ∀ y ∈ Formalism.MainNotions.S.lamAf (F := F) L, ∀ i,
      (c : E ⊗[F] Formalism.MainNotions.S.Af F) * y i ∈ Formalism.MainNotions.S.IntAf F E := by
  intro y hy
  let K : Submodule (Formalism.MainNotions.S.IntAf F E) (Fin n → E ⊗[F] Formalism.MainNotions.S.Af F) :=
    { carrier := {y | ∀ i, (c : E ⊗[F] Formalism.MainNotions.S.Af F) * y i ∈ Formalism.MainNotions.S.IntAf F E}
      add_mem' := by
        intro a b ha hb i
        rw [Pi.add_apply, mul_add]
        exact add_mem (ha i) (hb i)
      zero_mem' := by
        intro i
        rw [Pi.zero_apply, mul_zero]
        exact zero_mem _
      smul_mem' := by
        intro r a ha i
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
        exact mul_mem r.2 (ha i) }
  have hK : Formalism.MainNotions.S.lamAf (F := F) L ≤ K := by
    unfold Formalism.MainNotions.S.lamAf
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    show ∀ i, (c : E ⊗[F] Formalism.MainNotions.S.Af F) * Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) ((x : Fin n → E) i) ∈
      Formalism.MainNotions.S.IntAf F E
    intro i
    have h := inclE_mem_int (F := F) _ (hc x x.2 i)
    rw [map_mul, map_natCast] at h
    exact h
  exact hK hy

theorem single_mem_lat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (c : ℕ)
    (hs : ∀ j, (c : E) • Pi.single j (1 : E) ∈ L) (j : Fin n) :
    Pi.single j (c : E ⊗[F] Formalism.MainNotions.S.Af F) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  have hx : (fun i => Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F)
      (((c : E) • Pi.single j (1 : E) : Fin n → E) i)) = Pi.single j (c : E ⊗[F] Formalism.MainNotions.S.Af F) := by
    funext i
    by_cases h : i = j
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  rw [← hx]
  unfold Formalism.MainNotions.S.lamAf
  exact Submodule.subset_span ⟨⟨_, hs j⟩, rfl⟩

theorem int_vec_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (c : ℕ)
    (hs : ∀ j, (c : E) • Pi.single j (1 : E) ∈ L) (u : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F)
    (hu : ∀ i, u i ∈ Formalism.MainNotions.S.IntAf F E) :
    (fun i => (c : E ⊗[F] Formalism.MainNotions.S.Af F) * u i) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  have h : (fun i => (c : E ⊗[F] Formalism.MainNotions.S.Af F) * u i) =
      ∑ j, (⟨u j, hu j⟩ : Formalism.MainNotions.S.IntAf F E) • Pi.single j (c : E ⊗[F] Formalism.MainNotions.S.Af F) := by
    funext i
    rw [Finset.sum_apply]
    simp [Pi.single_apply, Subring.smul_def, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (single_mem_lat L c hs j)

end Loc

theorem lat_data (I : AutInst) : ∃ c : ℕ, 1 ≤ c ∧
    (∀ y ∈ I.Lf, ∀ i, (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * y i ∈ Formalism.MainNotions.S.IntAf I.F I.E) ∧
    ∀ u : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, (∀ i, u i ∈ Formalism.MainNotions.S.IntAf I.F I.E) →
      (fun i => (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * u i) ∈ I.Lf := by
  obtain ⟨c, hc, h1, h2⟩ := exists_good_den I.L I.L_fg I.L_span
  exact ⟨c, hc, lat_den I.L c h1, fun u hu => int_vec_mem I.L c h2 u hu⟩

theorem matrix_entries_integral (I : AutInst) (c g : ℕ)
    (h1 : ∀ y ∈ I.Lf, ∀ i, (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * y i ∈ Formalism.MainNotions.S.IntAf I.F I.E)
    (h2 : ∀ u : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, (∀ i, u i ∈ Formalism.MainNotions.S.IntAf I.F I.E) →
      (fun i => (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * u i) ∈ I.Lf)
    (X : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))
    (hX : ∀ i j, InNInt I (g * c * c) (X i j)) (y : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
    (hy : y ∈ I.Lf) :
    ∃ z ∈ I.Lf, X *ᵥ y = (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • z := by
  choose w hw hXw using hX
  refine ⟨fun i => (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * ∑ k, w i k * ((c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * y k), h2 _ (fun i => ?_), ?_⟩
  · exact sum_mem fun k _ => mul_mem (hw i k) (h1 y hy k)
  · funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hXw]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring

theorem entries_integral_of_lattice : EntriesLat := by
  intro I g hg
  obtain ⟨c, hc, h1, h2⟩ := lat_data I
  refine ⟨g * c * c, Nat.mul_pos (Nat.mul_pos hg hc) hc, ?_⟩
  intro M M' hMM' hM hM'
  have hsm : ∀ z ∈ I.Lf, ((g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • z) ∈ I.Lf := fun z hz =>
    I.Lf.smul_mem (⟨(g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), natCast_mem _ g⟩ : Formalism.MainNotions.S.IntAf I.F I.E) hz
  have hM'M : M' * M = 1 := by
    first
    | exact mul_eq_one_comm.1 hMM'
    | exact Matrix.mul_eq_one_comm.1 hMM'
    | (letI := Matrix.invertibleOfRightInverse M M' hMM'
       exact invOf_mul_self M)
  refine ⟨fun y => ⟨fun hy => ?_, fun hy => ?_⟩, fun y hy => matrix_entries_integral I c g h1 h2 (M - 1) hM y hy⟩
  · obtain ⟨z, hz, e⟩ := matrix_entries_integral I c g h1 h2 (M - 1) hM y hy
    have h3 : M *ᵥ y = y + (M - 1) *ᵥ y := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [h3, e]
    exact add_mem hy (hsm z hz)
  · obtain ⟨z, hz, e⟩ := matrix_entries_integral I c g h1 h2 (M' - 1) hM' (M *ᵥ y) hy
    have h3 : y = M *ᵥ y + (M' - 1) *ᵥ (M *ᵥ y) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec]
      abel
    rw [h3, e]
    exact add_mem hy (hsm z hz)

end PI.InvTopW
