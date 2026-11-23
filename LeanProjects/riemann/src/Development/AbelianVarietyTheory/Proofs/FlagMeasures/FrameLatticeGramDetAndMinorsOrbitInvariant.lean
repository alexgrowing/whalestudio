import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetGramTwoFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameUnipotentUnitriangular

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FrameGram

theorem submatrix_mul_upper {E : Type} [CommRing E] {N m : ℕ} (hm : m ≤ N) {ι : Type} (f : ι → Fin N)
    (M B : Matrix (Fin N) (Fin N) E) (hB : ∀ i j, j < i → B i j = 0) :
    (M * B).submatrix f (Fin.castLE hm) =
      M.submatrix f (Fin.castLE hm) * B.submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hm) (Fin.castLE_injective hm) _ _ ?_ fun _ => rfl
  intro i hi
  rw [hB, mul_zero]
  by_contra h
  apply hi
  have h1 : (i : ℕ) ≤ b := not_lt.1 h
  exact ⟨⟨i, by omega⟩, rfl⟩

theorem det_sub_upper {E : Type} [CommRing E] {N m : ℕ} (hm : m ≤ N)
    (B : Matrix (Fin N) (Fin N) E) (hB : ∀ i j, j < i → B i j = 0) (h1 : ∀ i, B i i = 1) :
    (B.submatrix (Fin.castLE hm) (Fin.castLE hm)).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [h1]
  · intro i j hij
    exact hB _ _ hij

theorem lead_mul_upper {E : Type} [CommRing E] {N : ℕ} (M B : Matrix (Fin N) (Fin N) E)
    (hB : ∀ i j, j < i → B i j = 0) (h1 : ∀ i, B i i = 1) (l : Fin (N + 1)) :
    lead (M * B) l = lead M l := by
  unfold lead
  rw [submatrix_mul_upper _ _ _ _ hB, Matrix.det_mul, det_sub_upper _ _ hB h1, mul_one]

theorem lead_transpose {E : Type} [CommRing E] {N : ℕ} (M : Matrix (Fin N) (Fin N) E)
    (l : Fin (N + 1)) : lead M.transpose l = lead M l := by
  unfold lead
  rw [← Matrix.det_transpose]
  rfl

theorem lead_lower_mul {E : Type} [CommRing E] {N : ℕ} (M B : Matrix (Fin N) (Fin N) E)
    (hB : ∀ i j, j < i → B i j = 0) (h1 : ∀ i, B i i = 1) (l : Fin (N + 1)) :
    lead (B.transpose * M) l = lead M l := by
  rw [← lead_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, lead_mul_upper _ _ hB h1,
    lead_transpose]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_sum_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι]
    (α : ι → E) (g : ι → Fin n → E) (y : Fin n → E) :
    hf L H (∑ i, α i • g i) y = ∑ i, α i * hf L H (g i) y := by
  change GlobalTheory.FrameBasic.hfL L H y _ = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl

theorem gram_change (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    {ι : Type} [Fintype ι] (u u' v v' : ι → Fin n → E) (P P' : Matrix ι ι E)
    (hv : ∀ j, v j = ∑ i, P i j • u i) (hv' : ∀ j, v' j = ∑ i, P' i j • u' i) :
    (Matrix.of fun a b => hf L H (v' b) (v a)) =
      (P.map L.cj).transpose * (Matrix.of fun a b => hf L H (u' b) (u a)) * P' := by
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hv', hf_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, GlobalTheory.FrameBasic.hf_conj L h, hv, hf_sum_left, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← GlobalTheory.FrameBasic.hf_conj L h]

theorem det_conj (L : LocE F E) {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι E) :
    (A.map L.cj).transpose.det = L.cj A.det := by
  rw [Matrix.det_transpose]
  exact (AlgEquiv.map_det L.cj A).symm

theorem span_frames {V : Type} [AddCommGroup V] [Module E V] {ι : Type} (g g' : ι → V) (t : F)
    (ht : t ≠ 0) :
    Submodule.span E (Set.range (Sum.elim g fun i => algebraMap F E t⁻¹ • (g' i - g i))) =
      Submodule.span E (Set.range g) ⊔ Submodule.span E (Set.range g') := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i | i, rfl⟩
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
        (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)))
  · rw [sup_le_iff, Submodule.span_le, Submodule.span_le]
    constructor
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · rintro _ ⟨i, rfl⟩
      have e : g' i = algebraMap F E t • (algebraMap F E t⁻¹ • (g' i - g i)) + g i := by
        rw [smul_smul, ← map_mul, mul_inv_cancel₀ ht, map_one, one_smul, sub_add_cancel]
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
        (Submodule.subset_span ⟨Sum.inl i, rfl⟩)

theorem vE_const [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (r k : ℕ)
    (S : Frames L r k) (c : F) (hc : c ≠ 0) (m : ℕ) :
    vE L S.ϖ (algebraMap F E ((-1) ^ (r + 1) * c * S.th⁻¹ ^ m)) =
      vE L S.ϖ (algebraMap F E c) - m * S.vth := by
  obtain ⟨hadd, hϖ, -, -⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
  have hth : S.th ≠ 0 := (GlobalTheory.FrameBasic.main L r k S).2.2.2.2.2.1
  have h1 : vE L S.ϖ (algebraMap F E 1) = 0 := by
    have := hadd 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega
  have hn : vE L S.ϖ (algebraMap F E (-1)) = 0 := by
    have := hadd (-1) (-1) (by simp) (by simp)
    rw [neg_mul_neg, mul_one] at this
    omega
  have ht : vE L S.ϖ (algebraMap F E S.th) = S.vth := by
    unfold Frames.th Frames.vth
    split_ifs
    · exact hϖ
    · exact h1
  have hti : vE L S.ϖ (algebraMap F E S.th⁻¹) = -S.vth := by
    have := hadd S.th S.th⁻¹ hth (inv_ne_zero hth)
    rw [mul_inv_cancel₀ hth] at this
    omega
  have hpow : ∀ x : F, x ≠ 0 → ∀ j : ℕ,
      vE L S.ϖ (algebraMap F E (x ^ j)) = j * vE L S.ϖ (algebraMap F E x) := by
    intro x hx j
    induction j with
    | zero => rw [pow_zero, h1]; simp
    | succ j ih => rw [pow_succ, hadd _ _ (pow_ne_zero _ hx) hx, ih]; push_cast; ring
  rw [hadd _ _ (mul_ne_zero (pow_ne_zero _ (by simp)) hc) (pow_ne_zero _ (inv_ne_zero hth)),
    hadd _ _ (pow_ne_zero _ (by simp)) hc, hpow _ (by simp), hpow _ (inv_ne_zero hth), hn, hti]
  ring

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', (∃ c : F, c ≠ 0 ∧ vE L S.ϖ (algebraMap F E c) = S.a ∧ (Matrix.of fun a b => S.h (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) b) (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) a)).det = algebraMap F E c) ∧ (∀ l, lead (Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a))) l = S.D l) ∧ Submodule.span E (Set.range (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))))) = S.ME := by
  intro F _ _ _ _ _ E _ _ _ L r k S n hn n' hn'
  obtain ⟨⟨s, ⟨hs0, hs1⟩, hs⟩, hsp, -⟩ := (GlobalTheory.HL.frame_unipotent_unitriangular L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩)).2 n hn
  obtain ⟨⟨s', ⟨hs0', hs1'⟩, hs'⟩, hsp', -⟩ :=
    (GlobalTheory.HL.frame_unipotent_unitriangular L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩)).2 n' hn'
  obtain ⟨-, -, ⟨c, hc0, hc⟩, -, -, hth, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hlead : ∀ l, lead (Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a))) l = S.D l := by
    intro l
    have e := gram_change L S.herm.1 S.f S.f' _ _ s s' hs hs'
    unfold Frames.h
    rw [e, lead_mul_upper _ _ hs0' hs1', lead_lower_mul]
    · rfl
    · intro i j hij; rw [Matrix.map_apply, hs0 i j hij, map_zero]
    · intro i; rw [Matrix.map_apply, hs1, map_one]
  refine ⟨⟨(-1) ^ (r + 1) * c * S.th⁻¹ ^ (2 * (r + 1)),
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) hc0) (pow_ne_zero _ (inv_ne_zero hth)),
    ?_, ?_⟩, hlead, ?_⟩
  · rw [vE_const L r k S c hc0, Frames.a, hc]
    push_cast; ring
  · set Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
      Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a)) with hZ
    set t : E := algebraMap F E S.th⁻¹ with ht
    let P : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      Matrix.fromBlocks 1 (Matrix.diagonal fun _ => -t) 0 (Matrix.diagonal fun _ => t)
    have hP : ∀ j, (Sum.elim (fun i => n (S.f i)) (fun i => t • (n' (S.f' i) - n (S.f i)))) j =
        ∑ i, P i j • (Sum.elim (fun i => n (S.f i)) (fun i => n' (S.f' i))) i := by
      rintro (j | j)
      · simp [P, Fintype.sum_sum_type, Matrix.one_apply]
      · simp [P, Fintype.sum_sum_type, Matrix.diagonal_apply, smul_sub]
        abel
    have hPd : P.det = t ^ (r + 1) := by
      simp [P, Matrix.det_fromBlocks_zero₂₁]
    have e := gram_change L S.herm.1 _ _ _ _ P P hP hP
    have hG : (Matrix.of fun a b => hf L S.Hm
        ((Sum.elim (fun i => n (S.f i)) (fun i => n' (S.f' i))) b)
        ((Sum.elim (fun i => n (S.f i)) (fun i => n' (S.f' i))) a)) =
        Matrix.fromBlocks (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E S.T))) Z
          (Z.map L.cj).transpose
          (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E S.T'))) := by
      ext (a | a) (b | b)
      · have := hn.1.1 (S.f b) (S.f a)
        simp only [Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, this, S.gram,
          Matrix.single_apply, eq_comm, and_comm]
      · rfl
      · exact GlobalTheory.FrameBasic.hf_conj L S.herm.1 _ _
      · have := hn'.1.1 (S.f' b) (S.f' a)
        simp only [Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, this, S.gram',
          Matrix.single_apply, eq_comm, and_comm]
    have hD1 : Z.det = S.D (Fin.last (r + 1)) := hlead (Fin.last (r + 1))
    have hD0 : (Z.submatrix Fin.castSucc Fin.castSucc).det = S.D (Fin.last r).castSucc :=
      hlead (Fin.last r).castSucc
    have e2 : ((Z.map L.cj).transpose.submatrix Fin.castSucc Fin.castSucc) =
      ((Z.submatrix Fin.castSucc Fin.castSucc).map L.cj).transpose := rfl
    have hct : L.cj t = t := L.cj.commutes _
    unfold Frames.h
    rw [e, Matrix.det_mul, Matrix.det_mul, det_conj, hPd, hG, GlobalTheory.HL.det_gram_two_frames, e2,
      det_conj, det_conj, hD1, hD0, ← map_mul (algebraMap F E), map_pow, hct]
    change _ * (_ * S.G) * _ = _
    rw [hc, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, ← ht]
    ring
  · have hu : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
      ext i; simpa using i.2
    rw [span_frames _ _ _ hth, Frames.ME, ← hsp, ← hsp']
    simp only [Frames.spanTo, hu, Set.image_univ]

end GlobalTheory.FrameGram
