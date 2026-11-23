import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLat

noncomputable section

namespace GlobalTheory.VolAt

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix

namespace ClosureLat

section Denominators

variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq]

theorem exists_pow_mul_eq {ϖ : W} (hp : Irreducible ϖ) (q : Qq) :
    ∃ (e : ℕ) (w : W), algebraMap W Qq (ϖ ^ e) * q = algebraMap W Qq w := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := W) q
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd0 hp
  refine ⟨e, n * u, ?_⟩
  have hd' : algebraMap W Qq d ≠ 0 := by
    simpa using (IsFractionRing.injective W Qq).ne hd0
  rw [← hu, map_mul, map_mul]
  field_simp

theorem exists_pow_smul_matrix {ϖ : W} (hp : Irreducible ϖ) {m n : Type} [Fintype m] [Fintype n]
    (c : Matrix m n Qq) :
    ∃ (e : ℕ) (M : Matrix m n W), algebraMap W Qq (ϖ ^ e) • c = M.map (algebraMap W Qq) := by
  choose e w h using fun i j => exists_pow_mul_eq (W := W) hp (c i j)
  have hE : ∀ i j, e i j ≤ ∑ i, ∑ j, e i j := fun i j =>
    (Finset.single_le_sum (f := fun j => e i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, e i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  refine ⟨∑ i, ∑ j, e i j, Matrix.of fun i j => ϖ ^ ((∑ i, ∑ j, e i j) - e i j) * w i j, ?_⟩
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.of_apply, map_mul, ← h i j]
  rw [← mul_assoc, ← map_mul, ← pow_add, Nat.sub_add_cancel (hE i j)]

theorem mem_colSpan_iff_mulVec {k : ℕ} (g : Matrix (Fin k) (Fin k) Qq) (z : Fin k → Qq) :
    z ∈ colSpan W g ↔ ∃ v : Fin k → W, z = g *ᵥ (fun i => algebraMap W Qq (v i)) := by
  unfold colSpan
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]

theorem exists_pow_smul_mem_homLat {ϖ : W} (hp : Irreducible ϖ) {k k' : ℕ}
    (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (hb : IsUnit b.det) :
    ∃ N : ℕ, ∀ M : Matrix (Fin k') (Fin k) W,
      algebraMap W Qq (ϖ ^ N) • M.map (algebraMap W Qq) ∈ homLat W (colSpan W a) (colSpan W b) := by
  obtain ⟨e₁, B, hB⟩ := exists_pow_smul_matrix (W := W) hp b⁻¹
  obtain ⟨e₂, A, hA⟩ := exists_pow_smul_matrix (W := W) hp a
  refine ⟨e₁ + e₂, fun M z hz => ?_⟩
  obtain ⟨v, rfl⟩ := (mem_colSpan_iff_mulVec (W := W) a z).1 hz
  refine (mem_colSpan_iff_mulVec (W := W) b _).2 ⟨(B * M * A) *ᵥ v, ?_⟩
  have h1 : (fun i => algebraMap W Qq (((B * M * A) *ᵥ v) i)) =
      (B.map (algebraMap W Qq) * M.map (algebraMap W Qq) * A.map (algebraMap W Qq)) *ᵥ
        (fun i => algebraMap W Qq (v i)) := by
    ext i
    rw [RingHom.map_mulVec, Matrix.map_mul, Matrix.map_mul]
    rfl
  have hbb : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv b hb
  rw [h1, ← hB, ← hA]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mulVec, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hbb, Matrix.one_mul, pow_add, map_mul, smul_smul]
  rw [mul_comm (algebraMap W Qq (ϖ ^ e₁))]

theorem exists_pow_smul_of_mem_homLat {ϖ : W} (hp : Irreducible ϖ) {k k' : ℕ}
    (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (ha : IsUnit a.det) :
    ∃ m : ℕ, ∀ t ∈ homLat W (colSpan W a) (colSpan W b), ∃ M : Matrix (Fin k') (Fin k) W,
      algebraMap W Qq (ϖ ^ m) • t = M.map (algebraMap W Qq) := by
  obtain ⟨e₁, B, hB⟩ := exists_pow_smul_matrix (W := W) hp b
  obtain ⟨e₂, A, hA⟩ := exists_pow_smul_matrix (W := W) hp a⁻¹
  refine ⟨e₁ + e₂, fun t ht => ?_⟩
  have hcol : ∀ c, ∃ v : Fin k' → W, t *ᵥ (fun i => a i c) = b *ᵥ (fun i => algebraMap W Qq (v i)) :=
    fun c => (mem_colSpan_iff_mulVec (W := W) b _).1 (ht _ (Submodule.subset_span ⟨c, rfl⟩))
  choose v hv using hcol
  have hta : t * a = b * (Matrix.of fun i c => v c i : Matrix (Fin k') (Fin k) W).map (algebraMap W Qq) := by
    ext i c
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using congrFun (hv c) i
  have ht' : t = b * (Matrix.of fun i c => v c i : Matrix (Fin k') (Fin k) W).map (algebraMap W Qq) * a⁻¹ := by
    rw [← hta, Matrix.mul_assoc, Matrix.mul_nonsing_inv a ha, Matrix.mul_one]
  refine ⟨B * (Matrix.of fun i c => v c i : Matrix (Fin k') (Fin k) W) * A, ?_⟩
  rw [Matrix.map_mul, Matrix.map_mul, ← hB, ← hA, ht']
  simp only [Matrix.smul_mul, Matrix.mul_smul, pow_add, map_mul, smul_smul]
  rw [mul_comm (algebraMap W Qq (ϖ ^ e₁))]

end Denominators

section Approximation

variable {E : Type} [Field E] [NumberField E] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem approx_of_mem_span {ϖ : W} (ρ : E →+* Qq)
    (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + ϖ ^ n * z))
    {k k' : ℕ} (Y : Submodule (𝓞 E) (Matrix (Fin k') (Fin k) E)) (m : ℕ)
    (hm : ∀ A ∈ Y, ∃ M : Matrix (Fin k') (Fin k) W,
      algebraMap W Qq (ϖ ^ m) • A.map ρ = M.map (algebraMap W Qq))
    {t : Matrix (Fin k') (Fin k) Qq}
    (ht : t ∈ Submodule.span W ((fun A : Matrix (Fin k') (Fin k) E => A.map ρ) '' (Y : Set (Matrix (Fin k') (Fin k) E))))
    (n : ℕ) :
    ∃ A ∈ Y, ∃ M : Matrix (Fin k') (Fin k) W,
      t - A.map ρ = algebraMap W Qq (ϖ ^ n) • M.map (algebraMap W Qq) := by
  induction ht using Submodule.span_induction generalizing n with
  | mem x hx =>
    obtain ⟨A, hA, rfl⟩ := hx
    exact ⟨A, hA, 0, by simp⟩
  | zero =>
    exact ⟨0, Y.zero_mem, 0, by ext i j; simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA, M, hM⟩ := hx n
    obtain ⟨A', hA', M', hM'⟩ := hy n
    refine ⟨A + A', Y.add_mem hA hA', M + M', ?_⟩
    ext i j
    have e1 := congrFun (congrFun hM i) j
    have e2 := congrFun (congrFun hM' i) j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_add]
    linear_combination e1 + e2
  | smul c x _ hx =>
    obtain ⟨A, hA, M, hM⟩ := hx n
    obtain ⟨u, z, hxz⟩ := h2 c (n + m)
    obtain ⟨M', hM'⟩ := hm A hA
    refine ⟨u • A, Y.smul_mem u hA, c • M - z • M', ?_⟩
    ext i j
    have e1 := congrFun (congrFun hM i) j
    have e2 := congrFun (congrFun hM' i) j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2
    have e3 : ρ ((u • A) i j) = ρ (u : E) * ρ (A i j) := by
      rw [Matrix.smul_apply, ← map_mul]
      rfl
    rw [Matrix.sub_apply, Matrix.map_apply, e3, hxz]
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.sub_apply, smul_eq_mul, Algebra.smul_def, map_add,
      map_sub, map_mul, map_pow, pow_add] at e1 e2 ⊢
    linear_combination (algebraMap W Qq c) * e1 -
      algebraMap W Qq ϖ ^ n * algebraMap W Qq z * e2

end Approximation

section Neighbourhoods

variable {X : Type} [TopologicalSpace X]

theorem exists_box_subset {ι : Type} [Fintype ι] (x : X) (B : ℕ → Set X) (hB : Antitone B)
    (h : ∀ U ∈ nhds x, ∃ n, B n ⊆ U) (V : Set (ι → X)) (hV : V ∈ nhds (fun _ => x)) :
    ∃ n, {d : ι → X | ∀ i, d i ∈ B n} ⊆ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := hV
  choose n hn using fun i => h (t i) (ht i)
  refine ⟨∑ i, n i, fun d hd => hsub fun i _ => hn i (hB ?_ (hd i))⟩
  exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem exists_doubleIndex_box_subset_nhds_const_of_antitone {ι κ : Type} [Fintype ι] [Fintype κ] (x : X) (B : ℕ → Set X) (hB : Antitone B)
    (h : ∀ U ∈ nhds x, ∃ n, B n ⊆ U) (V : Set (ι → κ → X)) (hV : V ∈ nhds (fun _ _ => x)) :
    ∃ n, {d : ι → κ → X | ∀ i j, d i j ∈ B n} ⊆ V :=
  exists_box_subset (fun _ => x) (fun n => {d : κ → X | ∀ j, d j ∈ B n})
    (fun _ _ hnm _ hd j => hB hnm (hd j)) (fun U hU => exists_box_subset x B hB h U hU) V hV

end Neighbourhoods

end ClosureLat

open ClosureLat in

theorem mem_closure_iff_map_mem_homLat {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type}
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ)
    (hp : Irreducible (p : W)) (ρ : E →+* Qq)
    (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z))
    (φ : P.adicCompletion E ≃+* Qq) (hφ : ∀ x : E, φ (algebraMap E (P.adicCompletion E) x) = ρ x)
    (hop : ∀ n : ℕ, IsOpen {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)})
    (hnb : ∀ U ∈ nhds (0 : P.adicCompletion E), ∃ n : ℕ,
      {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)} ⊆ U)
    {k k' : ℕ} (Y : Submodule (𝓞 E) (Matrix (Fin k') (Fin k) E)) (a : Matrix (Fin k) (Fin k) Qq)
    (b : Matrix (Fin k') (Fin k') Qq) (ha : IsUnit a.det) (hb : IsUnit b.det)
    (hY : ∀ A ∈ Y, A.map ρ ∈ homLat W (colSpan W a) (colSpan W b))
    (hT : homLat W (colSpan W a) (colSpan W b) ≤ Submodule.span W
      ((fun A : Matrix (Fin k') (Fin k) E => A.map ρ) '' (Y : Set (Matrix (Fin k') (Fin k) E))))
    (y : Matrix (Fin k') (Fin k) (P.adicCompletion E)) :
    y ∈ (Y.toAddSubgroup.map ((algebraMap E (P.adicCompletion E)).toAddMonoidHom.mapMatrix)).topologicalClosure ↔
      y.map φ ∈ homLat W (colSpan W a) (colSpan W b) := by
  obtain ⟨N, hN⟩ := exists_pow_smul_mem_homLat (W := W) hp a b hb
  obtain ⟨m, hm⟩ := exists_pow_smul_of_mem_homLat (W := W) hp a b ha
  constructor
  · intro hy
    let S : AddSubgroup (Matrix (Fin k') (Fin k) (P.adicCompletion E)) :=
      (homLat W (colSpan W a) (colSpan W b)).toAddSubgroup.comap
        ((φ : P.adicCompletion E →+* Qq).toAddMonoidHom.mapMatrix)
    have hS : ∀ d, d ∈ S ↔ d.map φ ∈ homLat W (colSpan W a) (colSpan W b) := fun d => Iff.rfl
    let U : Set (Matrix (Fin k') (Fin k) (P.adicCompletion E)) :=
      ⋂ i, ⋂ j, (fun d : Matrix (Fin k') (Fin k) (P.adicCompletion E) => d i j) ⁻¹'
        {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ N * w)}
    have hU : IsOpen U := isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (hop N).preimage (continuous_id.matrix_elem i j)
    have h0 : (0 : Matrix (Fin k') (Fin k) (P.adicCompletion E)) ∈ U := by
      simp only [U, Set.mem_iInter]
      exact fun i j => ⟨0, by simp⟩
    have hUS : U ⊆ S := by
      intro d hd
      simp only [U, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq] at hd
      choose w hw using hd
      refine (hS d).2 ?_
      have : d.map φ = algebraMap W Qq ((p : W) ^ N) • (Matrix.of w).map (algebraMap W Qq) := by
        ext i j
        simp [hw i j]
      rw [this]
      exact hN _
    have hopen : IsOpen (S : Set (Matrix (Fin k') (Fin k) (P.adicCompletion E))) :=
      AddSubgroup.isOpen_of_mem_nhds S (Filter.mem_of_superset (hU.mem_nhds h0) hUS)
    have hle : Y.toAddSubgroup.map ((algebraMap E (P.adicCompletion E)).toAddMonoidHom.mapMatrix) ≤ S := by
      rintro _ ⟨A, hA, rfl⟩
      rw [hS]
      have : (((algebraMap E (P.adicCompletion E)).toAddMonoidHom.mapMatrix A).map φ) = A.map ρ := by
        ext i j
        simp [hφ]
      rw [this]
      exact hY A hA
    exact (hS y).1 (AddSubgroup.topologicalClosure_minimal _ hle (AddSubgroup.isClosed_of_isOpen S hopen) hy)
  · intro hy
    rw [← SetLike.mem_coe, AddSubgroup.topologicalClosure_coe, mem_closure_iff_nhds]
    intro U hU
    have hV : (fun d : Matrix (Fin k') (Fin k) (P.adicCompletion E) => y + d) ⁻¹' U ∈
        nhds (0 : Matrix (Fin k') (Fin k) (P.adicCompletion E)) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
    have hanti : Antitone fun n : ℕ => {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)} := by
      intro n n' hnn z hz
      obtain ⟨w, hw⟩ := hz
      refine ⟨(p : W) ^ (n' - n) * w, ?_⟩
      rw [hw, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnn]
    obtain ⟨n, hn⟩ := exists_doubleIndex_box_subset_nhds_const_of_antitone (ι := Fin k') (κ := Fin k) (0 : P.adicCompletion E)
      (fun n : ℕ => {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)}) hanti hnb _ hV
    obtain ⟨A, hAY, M, hM⟩ := approx_of_mem_span (ϖ := (p : W)) ρ h2 Y m (fun A hA => hm _ (hY A hA)) (hT hy) n
    refine ⟨(algebraMap E (P.adicCompletion E)).toAddMonoidHom.mapMatrix A, ?_, ⟨A, hAY, rfl⟩⟩
    have hd : (algebraMap E (P.adicCompletion E)).toAddMonoidHom.mapMatrix A - y ∈
        (fun d : Matrix (Fin k') (Fin k) (P.adicCompletion E) => y + d) ⁻¹' U := by
      refine hn fun i j => ⟨-M i j, ?_⟩
      have e1 := congrFun (congrFun hM i) j
      simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at e1
      have e2 : φ (((algebraMap E (P.adicCompletion E)).toAddMonoidHom.mapMatrix A - y) i j) =
          ρ (A i j) - φ (y i j) := by
        simp [hφ]
      refine e2.trans ?_
      simp only [map_mul, map_neg] at e1 ⊢
      linear_combination -e1
    simpa using hd

end GlobalTheory.VolAt
