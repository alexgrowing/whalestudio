import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsPrimitiveNorm
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LinearIndependentOfGramDetNeZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanSInduction

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def gram (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ} (x : Fin n → V) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => h (x i) (x j)

def spanS (S : Subring K) {n : ℕ} (x : Fin n → V) : Submodule S V :=
  Submodule.span S (Set.range x)

variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem mem_spanS {n : ℕ} (x : Fin n → V) (i : Fin n) : x i ∈ spanS S x :=
  Submodule.subset_span ⟨i, rfl⟩

theorem smul_mem_spanS {n : ℕ} {x : Fin n → V} {c : K} (hc : c ∈ S) {v : V} (hv : v ∈ spanS S x) :
    c • v ∈ spanS S x :=
  (spanS S x).smul_mem (⟨c, hc⟩ : S) hv

theorem spanS_induction {n : ℕ} {x : Fin n → V} {p : V → Prop} (h0 : p 0)
    (hadd : ∀ a b, p a → p b → p (a + b)) (hsmul : ∀ c ∈ S, ∀ a, p a → p (c • a))
    (hx : ∀ i, p (x i)) : ∀ v ∈ spanS S x, p v := by
  first | exact UpperTheory.Reformulated.B.Qe24.spanS_induction .. | (apply UpperTheory.Reformulated.B.Qe24.spanS_induction <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe24.spanS_induction <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe24.spanS_induction <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe24.spanS_induction <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe24.spanS_induction <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul hx v ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul hx v | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul hx | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K

theorem int_spanS (hS : IsHermSemilocal S) {n : ℕ} {x : Fin n → V}
    (hx : ∀ i j, h (x i) (x j) ∈ S) : ∀ a ∈ spanS S x, ∀ b ∈ spanS S x, h a b ∈ S := by
  intro a ha
  refine spanS_induction (by simp [S.zero_mem]) (fun b c hb hc => by
    rw [map_add]; exact S.add_mem hb hc) (fun c hc b hb => by
    rw [map_smul]; exact S.mul_mem hc hb) (fun j => ?_)
  revert a
  refine spanS_induction (by simp [S.zero_mem]) (fun b c hb hc => by
    rw [map_add, LinearMap.add_apply]; exact S.add_mem hb hc) (fun c hc b hb => by
    rw [map_smulₛₗ, LinearMap.smul_apply]; exact S.mul_mem (hS.star_mem _ hc) hb)
    (fun i => hx i j)

theorem exists_coeff {n : ℕ} {y : Fin n → V} {v : V} (hv : v ∈ spanS S y) :
    ∃ c : Fin n → S, v = ∑ j, (c j : K) • y j := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hv
  exact ⟨c, hc.symm⟩

theorem gram_det_of_le (hS : IsHermSemilocal S) {n : ℕ} {x y : Fin n → V}
    (hxy : ∀ i, x i ∈ spanS S y) : ∃ c ∈ S, (gram h x).det = c * (gram h y).det := by
  choose T hT using fun i => exists_coeff (hxy i)
  have e : gram h x = ((S.subtype.mapMatrix (Matrix.of T)).map star) * gram h y *
      (S.subtype.mapMatrix (Matrix.of T)).transpose := by
    ext i l
    simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
      RingHom.mapMatrix_apply, Subring.subtype_apply]
    conv_lhs => rw [hT i, hT l]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have e2 : ((S.subtype.mapMatrix (Matrix.of T)).map star).det =
      star (S.subtype.mapMatrix (Matrix.of T)).det := by
    have := (starRingEnd K).map_det (S.subtype.mapMatrix (Matrix.of T))
    rw [starRingEnd_apply] at this
    rw [this]
    rfl
  have e3 : (S.subtype.mapMatrix (Matrix.of T)).det ∈ S := by
    rw [← RingHom.map_det]
    exact (Matrix.of T).det.2
  refine ⟨star (S.subtype.mapMatrix (Matrix.of T)).det * (S.subtype.mapMatrix (Matrix.of T)).det,
    S.mul_mem (hS.star_mem _ e3) e3, ?_⟩
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e2]
  ring

theorem gram_det_cons (hs : h.IsSymm) {n : ℕ} (f : V) (x : Fin n → V) (hf : ∀ k, h f (x k) = 0) :
    (gram h (Fin.cons f x : Fin (n + 1) → V)).det = h f f * (gram h x).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h1 : ∀ i : Fin n, (-1 : K) ^ (i.succ : ℕ) * gram h (Fin.cons f x : Fin (n + 1) → V) i.succ 0 *
      ((gram h (Fin.cons f x : Fin (n + 1) → V)).submatrix i.succ.succAbove Fin.succ).det = 0 := by
    intro i
    have : gram h (Fin.cons f x : Fin (n + 1) → V) i.succ 0 = 0 := by
      simp only [gram, Matrix.of_apply, Fin.cons_succ, Fin.cons_zero]
      rw [← show star (h f (x i)) = h (x i) f from hs.eq f (x i), hf, star_zero]
    rw [this]
    ring
  rw [Finset.sum_eq_zero fun i _ => h1 i, add_zero]
  have h2 : (gram h (Fin.cons f x : Fin (n + 1) → V)).submatrix (Fin.succAbove 0) Fin.succ =
      gram h x := by
    ext i j
    simp [gram]
  rw [h2]
  simp [gram]

theorem gram_det_dv (hπ : IsUnif S π) {n : ℕ} (x : Fin (n + 2) → V)
    (hx : ∀ i j, Dv S π (h (x i) (x j))) : Dv S π ((gram h x).det * π⁻¹) := by
  have e : gram h x = π • S.subtype.mapMatrix
      (Matrix.of fun i j => (⟨h (x i) (x j) * π⁻¹, hx i j⟩ : S)) := by
    ext i j
    have := hπ.ne
    simp only [gram, Matrix.of_apply, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Subring.subtype_apply, smul_eq_mul]
    field_simp
  rw [e, Matrix.det_smul, ← RingHom.map_det, Fintype.card_fin]
  unfold Dv
  have e2 : ∀ d : K, π ^ (n + 2) * d * π⁻¹ * π⁻¹ = π ^ n * d := by
    intro d
    have := hπ.ne
    field_simp
    ring
  rw [e2]
  exact S.mul_mem (S.pow_mem hπ.mem n) (Subtype.mem _)

theorem exists_pivot (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {n : ℕ}
    (x : Fin (n + 1) → V) (hx : ∀ i j, h (x i) (x j) ∈ S)
    (hnd : ∃ i j, ¬ Dv S π (h (x i) (x j))) :
    ∃ i₀ : Fin (n + 1), ∃ r ∈ spanS S (x ∘ i₀.succAbove), IsUnitIn S (h (x i₀ + r) (x i₀ + r)) := by
  obtain ⟨i, j, hij⟩ := hnd
  by_cases h1 : IsUnitIn S (h (x i) (x i))
  · exact ⟨i, 0, Submodule.zero_mem _, by simpa using h1⟩
  by_cases h2 : IsUnitIn S (h (x j) (x j))
  · exact ⟨j, 0, Submodule.zero_mem _, by simpa using h2⟩
  have d1 := dv_of_not_unit hπ (hx i i) (hs.eq _ _) h1
  have d2 := dv_of_not_unit hπ (hx j j) (hs.eq _ _) h2
  have hne : j ≠ i := by
    rintro rfl
    exact hij d1
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hne
  obtain ⟨s, hsS, hs1⟩ := exists_trace_mul hS hπ (hx i j) hij S.one_mem (star_one K)
  refine ⟨i, s • x j, smul_mem_spanS hsS (by rw [← hk]; exact mem_spanS (x ∘ i.succAbove) k), ?_⟩
  have hji : h (x j) (x i) = star (h (x i) (x j)) := (hs.eq _ _).symm
  have e : h (x i + s • x j) (x i + s • x j) =
      1 + (star s * s * h (x j) (x j) + h (x i) (x i)) := by
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hji,
      starRingEnd_apply, RingHom.id_apply]
    simp only [star_mul'] at hs1
    linear_combination hs1
  rw [e]
  exact unit_add_dv hπ isUnitIn_one
    ((d2.mul_left (S.mul_mem (hS.star_mem _ hsS) hsS)).add d1)

theorem spanS_cons {n : ℕ} (f : V) (y : Fin n → V) :
    spanS S (Fin.cons f y : Fin (n + 1) → V) = Submodule.span S {f} ⊔ spanS S y := by
  unfold spanS
  rw [Fin.range_cons, Submodule.span_insert]

theorem exists_orth_tuple (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) :
    ∀ (n : ℕ) (x : Fin n → V), (∀ i j, h (x i) (x j) ∈ S) →
      ¬ Dv S π ((gram h x).det * π⁻¹) →
      ∃ y : Fin n → V, (∀ i j, i ≠ j → h (y i) (y j) = 0) ∧ spanS S y = spanS S x := by
  intro n
  induction n with
  | zero => exact fun x _ _ => ⟨x, fun i => i.elim0, rfl⟩
  | succ n ih =>
    intro x hx hdet
    by_cases hnd : ∃ i j, ¬ Dv S π (h (x i) (x j))
    · obtain ⟨i₀, r, hr, hu⟩ := exists_pivot hS hπ hs x hx hnd
      have hrx : r ∈ spanS S x :=
        Submodule.span_mono (Set.range_comp_subset_range _ _) hr
      have hint := int_spanS hS hx
      generalize hfdef : x i₀ + r = f at hu
      have hf : f ∈ spanS S x := by
        rw [← hfdef]; exact (spanS S x).add_mem (mem_spanS x i₀) hrx
      have hc : ∀ k, h f (x (i₀.succAbove k)) * (h f f)⁻¹ ∈ S := fun k =>
        S.mul_mem (hint f hf _ (mem_spanS x _)) hu.2.2
      let x' : Fin n → V := fun k =>
        x (i₀.succAbove k) - (h f (x (i₀.succAbove k)) * (h f f)⁻¹) • f
      have hx'mem : ∀ k, x' k ∈ spanS S x := fun k =>
        (spanS S x).sub_mem (mem_spanS x _) (smul_mem_spanS (hc k) hf)
      have hfx' : ∀ k, h f (x' k) = 0 := by
        intro k
        have := hu.1
        simp only [x', map_sub, map_smul, smul_eq_mul]
        field_simp
        ring
      have hf0 : f ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) :=
        mem_spanS (Fin.cons f x' : Fin (n + 1) → V) 0
      have hge1 : ∀ k, x (i₀.succAbove k) ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) := by
        intro k
        have h1 : x' k ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) :=
          mem_spanS (Fin.cons f x' : Fin (n + 1) → V) k.succ
        have h2 := Submodule.add_mem _ h1 (smul_mem_spanS (hc k) hf0)
        simpa only [x', sub_add_cancel] using h2
      have hge : ∀ i, x i ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) := by
        intro i
        rcases Fin.eq_self_or_eq_succAbove i₀ i with rfl | ⟨k, rfl⟩
        · have h1 : r ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) := by
            refine (Submodule.span_le.mpr ?_) hr
            rintro _ ⟨k, rfl⟩
            exact hge1 k
          have h2 := Submodule.sub_mem _ hf0 h1
          have e : f - r = x i := by rw [← hfdef, add_sub_cancel_right]
          rwa [e] at h2
        · exact hge1 k
      have hspan : spanS S (Fin.cons f x' : Fin (n + 1) → V) = spanS S x := by
        apply le_antisymm
        · refine Submodule.span_le.mpr ?_
          rintro _ ⟨i, rfl⟩
          refine Fin.cases ?_ (fun k => ?_) i
          · exact hf
          · exact hx'mem k
        · refine Submodule.span_le.mpr ?_
          rintro _ ⟨i, rfl⟩
          exact hge i
      obtain ⟨c, hcS, hcdet⟩ := gram_det_of_le (h := h) hS hge
      rw [gram_det_cons hs f x' hfx'] at hcdet
      obtain ⟨y', horth, hspan'⟩ := ih x' (fun i j => hint _ (hx'mem i) _ (hx'mem j)) (by
        intro hd
        apply hdet
        have e : (gram h x).det * π⁻¹ = c * h f f * ((gram h x').det * π⁻¹) := by
          rw [hcdet]; ring
        rw [e]
        exact hd.mul_left (S.mul_mem hcS hu.2.1))
      have hfy : ∀ k, h f (y' k) = 0 := by
        intro k
        have h1 : y' k ∈ spanS S x' := by rw [← hspan']; exact mem_spanS y' k
        exact spanS_induction (p := fun v => h f v = 0) (by simp)
          (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
          (fun c _ a ha => by rw [map_smul, ha, smul_zero]) hfx' _ h1
      refine ⟨Fin.cons f y', ?_, ?_⟩
      · intro i j
        refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
        · intro hne; exact absurd rfl hne
        · intro _; simpa using hfy l
        · intro _
          simp only [Fin.cons_succ, Fin.cons_zero]
          rw [← show star (h f (y' k)) = h (y' k) f from hs.eq _ _, hfy, star_zero]
        · intro hne
          simp only [Fin.cons_succ]
          exact horth k l fun hkl => hne (by rw [hkl])
      · rw [← hspan, spanS_cons, spanS_cons, hspan']
    · push Not at hnd
      cases n with
      | zero => exact ⟨x, fun i j hij => absurd (by omega : i = j) hij, rfl⟩
      | succ m => exact absurd (gram_det_dv hπ x hnd) hdet

end Formalism.HermitianLattices.Ext.L3.U0
