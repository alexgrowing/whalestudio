import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeCongruenceStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringOHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceStabUFromIntegralUnipotentIsometryStatement
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.CovTerm

theorem one_le_prod0 {α : Type} {s : Finset α} {f : α → ℝ} (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i :=
  Finset.prod_induction f (fun x => 1 ≤ x) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl h

theorem le_prod_of_one_le {α : Type} {s : Finset α} {f : α → ℝ} (h : ∀ i ∈ s, 1 ≤ f i) {a : α}
    (ha : a ∈ s) : f a ≤ ∏ i ∈ s, f i := by
  rw [← Finset.mul_prod_erase s f ha]
  exact le_mul_of_one_le_right (zero_le_one.trans (h a ha))
    (one_le_prod0 fun i hi => h i (Finset.mem_of_mem_erase hi))

section Pt
variable {K : Type} [Field K] (τ : K →+* ℂ)

noncomputable def lm (bs : List (K × ℕ)) (l : ℕ) : K :=
  (Matrix.of fun i j : Fin l => ptEntry bs i j).det

theorem lm_cons (t : K) (s : ℕ) (bs : List (K × ℕ)) (l : ℕ) :
    ‖τ (lm ((t, s) :: bs) (s + l))‖ = ‖τ t‖ ^ s * ‖τ (lm bs l)‖ := by
  have h : (Matrix.of fun i j : Fin (s + l) => ptEntry ((t, s) :: bs) i j).submatrix
      finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks ((Matrix.diagonal fun _ : Fin s => t).submatrix id Fin.revPerm) 0 0
        (Matrix.of fun i j : Fin l => ptEntry bs i j) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · have hi := i.2
      have hj := j.2
      simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, Matrix.of_apply, Fin.val_castAdd,
        ptEntry.eq_2, Matrix.fromBlocks_apply₁₁, id, Matrix.diagonal_apply, Fin.revPerm_apply,
        Fin.ext_iff, Fin.val_rev, hi, hj, and_self, if_true]
      exact if_congr (by omega) rfl rfl
    · have hi := i.2
      simp [ptEntry.eq_2]
    · have hj := j.2
      simp [ptEntry.eq_2]
    · simp [ptEntry.eq_2]
  unfold lm
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, h, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_permute', Matrix.det_diagonal]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with e | e <;>
    simp [e]

noncomputable def entP (bs : List (K × ℕ)) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, max 1 ‖τ (ptEntry bs i j)‖

theorem prodMaxOneNorm_cons (t : K) (s : ℕ) (bs : List (K × ℕ)) (n : ℕ) :
    entP τ ((t, s) :: bs) (s + n) = max 1 ‖τ t‖ ^ s * entP τ bs n := by
  unfold entP
  rw [Finset.prod_range_add]
  congr 1
  · rw [Finset.prod_congr rfl (g := fun _ => max 1 ‖τ t‖), Finset.prod_const, Finset.card_range]
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [Finset.prod_eq_single (s - 1 - i)]
    · rw [ptEntry.eq_2, if_pos (by omega), if_pos (by omega)]
    · intro j _ hj
      rw [ptEntry.eq_2]
      split_ifs with h1 h2 h3
      · omega
      · simp
      · omega
      · simp
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_range_add, Finset.prod_eq_one, one_mul]
    · refine Finset.prod_congr rfl fun j _ => ?_
      simp [ptEntry.eq_2]
    · intro j hj
      have hj' := Finset.mem_range.1 hj
      rw [ptEntry.eq_2, if_neg (by omega), if_neg (by omega)]
      simp

noncomputable def gg2 (x : ℝ) : ℝ := max 1 x * max 1 x⁻¹

theorem one_le_maxOneMulMaxOneInv (x : ℝ) : 1 ≤ gg2 x :=
  one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)

theorem prodMaxOneNorm_le (bs : List (K × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (c : ℝ) (hc : 0 < c) :
    entP τ bs (bs.map Prod.snd).sum ≤
      max 1 c⁻¹ * ∏ l ∈ Finset.range (bs.map Prod.snd).sum, gg2 (c * ‖τ (lm bs (l + 1))‖) := by
  induction bs generalizing c with
  | nil => simp [entP]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    obtain ⟨ht, hs⟩ := h (t, s) List.mem_cons_self
    have ht' : 0 < ‖τ t‖ := norm_pos_iff.2 ((map_ne_zero τ).2 ht)
    have hc' : 0 < c * ‖τ t‖ ^ s := by positivity
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) _ hc'
    simp only [List.map_cons, List.sum_cons]
    rw [prodMaxOneNorm_cons, Finset.prod_range_add]
    have h1 : max 1 ‖τ t‖ ^ s ≤ max 1 c⁻¹ * max 1 (c * ‖τ t‖ ^ s) := by
      rcases le_total ‖τ t‖ 1 with h2 | h2
      · rw [max_eq_left h2, one_pow]
        exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
      · rw [max_eq_right h2]
        calc ‖τ t‖ ^ s = c⁻¹ * (c * ‖τ t‖ ^ s) := by field_simp
          _ ≤ _ := mul_le_mul (le_max_right _ _) (le_max_right _ _) hc'.le (by positivity)
    have h2 : gg2 (c * ‖τ t‖ ^ s) ≤
        ∏ l ∈ Finset.range s, gg2 (c * ‖τ (lm ((t, s) :: bs) (l + 1))‖) := by
      have e : gg2 (c * ‖τ t‖ ^ s) = gg2 (c * ‖τ (lm ((t, s) :: bs) (s - 1 + 1))‖) := by
        have : s - 1 + 1 = s + 0 := by simp at hs; omega
        rw [this, lm_cons]
        simp [lm]
      rw [e]
      exact le_prod_of_one_le (f := fun l => gg2 (c * ‖τ (lm ((t, s) :: bs) (l + 1))‖))
        (fun l _ => one_le_maxOneMulMaxOneInv _) (Finset.mem_range.2 (by simp at hs; omega))
    have h3 : ∏ l ∈ Finset.range (bs.map Prod.snd).sum, gg2 (c * ‖τ (lm ((t, s) :: bs) (s + l + 1))‖) =
        ∏ l ∈ Finset.range (bs.map Prod.snd).sum, gg2 (c * ‖τ t‖ ^ s * ‖τ (lm bs (l + 1))‖) := by
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [add_assoc, lm_cons, mul_assoc]
    rw [h3]
    set R := ∏ l ∈ Finset.range (bs.map Prod.snd).sum, gg2 (c * ‖τ t‖ ^ s * ‖τ (lm bs (l + 1))‖)
    have hR : 0 ≤ R := Finset.prod_nonneg fun l _ => zero_le_one.trans (one_le_maxOneMulMaxOneInv _)
    have hE : 0 ≤ entP τ bs (bs.map Prod.snd).sum :=
      Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by positivity
    calc _ ≤ (max 1 c⁻¹ * max 1 (c * ‖τ t‖ ^ s)) * (max 1 (c * ‖τ t‖ ^ s)⁻¹ * R) :=
          mul_le_mul h1 ih' hE (by positivity)
      _ = max 1 c⁻¹ * (gg2 (c * ‖τ t‖ ^ s) * R) := by unfold gg2; ring
      _ ≤ _ := by gcongr

theorem minor_pt_le {N : ℕ} (p : Point K N) (t : ℕ) (I J : Fin t → Fin N) :
    ‖(((ptMat p).map τ).submatrix I J).det‖ ≤
      ∏ l ∈ Finset.range N, gg2 ‖τ (leadMinorE (ptMat p) (l + 1))‖ := by
  obtain ⟨σ, d, hd, hw⟩ := GlobalTheory.LoopV.Cell.ptMat_monomial p
  have e : (ptMat p).map τ = Matrix.of fun i j => if j = σ i then τ (d i) else 0 := by
    ext i j
    simp only [Matrix.map_apply, hw, Matrix.of_apply]
    split_ifs <;> simp
  rw [e]
  refine (Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.monomialMinor N σ (fun i => τ (d i)) t I J).trans ?_
  have h := prodMaxOneNorm_le τ p.1 p.2.1 1 one_pos
  rw [p.2.2] at h
  simp only [inv_one, max_self, one_mul] at h
  have e1 : ∏ i, max 1 ‖τ (d i)‖ = entP τ p.1 N := by
    unfold entP
    rw [Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_range, Finset.prod_eq_single (σ i)]
    · have := hw i (σ i)
      rw [if_pos rfl] at this
      rw [← this]; rfl
    · intro j _ hj
      have := hw i j
      rw [if_neg hj] at this
      have h0 : ptEntry p.1 i j = 0 := this
      simp [h0]
    · simp
  rw [e1]
  refine h.trans (le_of_eq (Finset.prod_congr rfl fun l hl => ?_))
  have hl' : l + 1 ≤ N := Finset.mem_range.1 hl
  unfold leadMinorE
  rw [dif_pos hl']
  rfl

end Pt

section Red
open GlobalTheory.LoopV GlobalTheory.LoopV.Cell
variable {K : Type} [Field K] [NumberField K] {N : ℕ}

theorem entIn_iff (I : Ideal (𝓞 K)) (x : Matrix (Fin N) (Fin N) K) :
    EntIn I x ↔ ∃ X : Matrix (Fin N) (Fin N) (𝓞 K), (∀ i j, X i j ∈ I) ∧
      X.map (algebraMap (𝓞 K) K) = x := by
  constructor
  · intro h
    choose X h1 h2 using h
    exact ⟨Matrix.of X, h1, by ext i j; exact h2 i j⟩
  · rintro ⟨X, h1, rfl⟩ i j
    exact ⟨X i j, h1 i j, rfl⟩

theorem entIn_mul {I : Ideal (𝓞 K)} {A x B : Matrix (Fin N) (Fin N) K} (hA : EntIn ⊤ A)
    (hx : EntIn I x) (hB : EntIn ⊤ B) : EntIn I (A * x * B) := by
  rw [entIn_iff] at *
  obtain ⟨A, -, rfl⟩ := hA
  obtain ⟨B, -, rfl⟩ := hB
  obtain ⟨x, hx, rfl⟩ := hx
  refine ⟨A * x * B, fun i j => ?_, by rw [Matrix.map_mul, Matrix.map_mul]⟩
  simp only [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (I.sum_mem fun l _ => I.mul_mem_left _ (hx _ _))

theorem entIn_inv {B : Matrix (Fin N) (Fin N) K} (hB : EntIn ⊤ B) (hd : B.det = 1) : EntIn ⊤ B⁻¹ := by
  rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul]
  rw [entIn_iff] at *
  obtain ⟨B, -, rfl⟩ := hB
  exact ⟨B.adjugate, fun _ _ => trivial, RingHom.map_adjugate (algebraMap (𝓞 K) K) B⟩

theorem leadMinor_int {Z : Matrix (Fin N) (Fin N) K} (hZ : EntIn ⊤ Z) (l : ℕ) :
    ∃ o : 𝓞 K, (o : K) = leadMinorE Z l := by
  rw [entIn_iff] at hZ
  obtain ⟨X, -, rfl⟩ := hZ
  unfold leadMinorE
  split_ifs with h
  · refine ⟨(X.submatrix (Fin.castLE h) (Fin.castLE h)).det, ?_⟩
    exact (RingHom.map_det (algebraMap (𝓞 K) K) _)
  · exact ⟨0, by simp⟩

omit [NumberField K] in
theorem leadMinor_cell {L U w : Matrix (Fin N) (Fin N) K} (hL : IsLoUni L) (hU : IsUpUni U) (l : ℕ) :
    leadMinorE (L * w * U) l = leadMinorE w l := by
  unfold leadMinorE
  split_ifs with h
  · convert Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.leadingMinorInvariant K N l h L w U (fun i => (hL i i).2 rfl)
      (fun i j hij => (hL i j).1 hij) (fun i => (hU i i).2 rfl) (fun i j hij => (hU i j).1 hij)
  · rfl

omit [NumberField K] in
theorem upUni_mul {U B : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) (hB : IsUpUni B) :
    IsUpUni (U * B) := by
  intro i j
  refine ⟨fun h => (up_tri hU).mul (up_tri hB) h, fun h => ?_⟩
  subst h
  rw [Matrix.mul_apply, Finset.sum_eq_single i, (hU i i).2 rfl, (hB i i).2 rfl, one_mul]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [(hU i k).1 h, zero_mul]
    · rw [(hB k i).1 h, mul_zero]
  · simp

variable {ι : Type} [Fintype ι] (τ : ι → (K →+* ℂ))

omit [Fintype ι] in
theorem reduce_up {ρ : ℝ} (h1 : 1 ≤ ρ) (hρ : ∀ x : K, ∃ o : 𝓞 K, ∀ v, ‖τ v (x + o)‖ ≤ ρ)
    {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) :
    ∃ B : Matrix (Fin N) (Fin N) K, IsUpUni B ∧ EntIn ⊤ B ∧ ∀ v i j, ‖τ v ((U * B) i j)‖ ≤ ρ := by
  obtain ⟨B, b1, b2, b3, b4⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.unipotentReduce K (algebraMap (𝓞 K) K).range
    {x | ∀ v, ‖τ v x‖ ≤ ρ} N U
    (fun x => by obtain ⟨o, ho⟩ := hρ x; exact ⟨o, ⟨o, rfl⟩, ho⟩)
    (fun i => (hU i i).2 rfl) (fun i j hij => (hU i j).1 hij)
  have hB : IsUpUni B := fun i j => ⟨b2 i j, fun h => h ▸ b1 i⟩
  refine ⟨B, hB, fun i j => ?_, fun v i j => ?_⟩
  · obtain ⟨o, ho⟩ := b3 i j
    exact ⟨o, trivial, ho⟩
  · rcases lt_trichotomy i j with h | h | h
    · exact b4 i j h v
    · rw [(upUni_mul hU hB i j).2 h]; simpa using h1
    · rw [(upUni_mul hU hB i j).1 h]; simpa using zero_le_one.trans h1

noncomputable def PiZ (Z : Matrix (Fin N) (Fin N) K) : ℝ :=
  ∏ v, ∏ l ∈ Finset.range N, max 1 ‖τ v (leadMinorE Z (l + 1))‖

omit [NumberField K] in
theorem one_le_PiZ (Z : Matrix (Fin N) (Fin N) K) : 1 ≤ PiZ τ Z :=
  one_le_prod0 fun _ _ => one_le_prod0 fun _ _ => le_max_left _ _

theorem prod_maxOneMulMaxOneInv_leadingMinors_le_sq (hN : ∀ o : 𝓞 K, o ≠ 0 → 1 ≤ ∏ v, ‖τ v o‖) {Z : Matrix (Fin N) (Fin N) K}
    (hZ : EntIn ⊤ Z) :
    ∏ v, ∏ l ∈ Finset.range N, gg2 ‖τ v (leadMinorE Z (l + 1))‖ ≤ PiZ τ Z ^ 2 := by
  unfold PiZ
  rw [Finset.prod_comm, Finset.prod_comm (s := Finset.univ), ← Finset.prod_pow]
  refine Finset.prod_le_prod (fun l _ => Finset.prod_nonneg fun v _ =>
    zero_le_one.trans (one_le_maxOneMulMaxOneInv _)) fun l _ => ?_
  obtain ⟨o, ho⟩ := leadMinor_int hZ (l + 1)
  rw [← ho]
  by_cases h0 : o = 0
  · subst h0; simp [gg2]
  · have hp : ∀ v, 0 < ‖τ v o‖ := fun v => norm_pos_iff.2 ((map_ne_zero (τ v)).2 (by simpa using h0))
    have := (Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.lemmaP ι (fun v => ‖τ v o‖) Finset.univ hp (hN o h0)).2
    simp only [one_div] at this
    unfold gg2
    rw [Finset.prod_mul_distrib, sq]
    exact mul_le_mul_of_nonneg_left this (Finset.prod_nonneg fun v _ => by positivity)

theorem cov_lead [StarRing K] (L U : Matrix (Fin N) (Fin N) K) (p : Point K N) (I : Ideal (𝓞 K)) (ρ : ℝ)
    (hs : ∀ v a, τ v (star a) = starRingEnd ℂ (τ v a))
    (hw : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w)
    (hr : finrank ℚ K = 2 * Fintype.card ι) (hL : IsLoUni L) (hU : IsUpUni U)
    (hZ : EntIn ⊤ (L * ptMat p * U)) (hI : I ≠ ⊥) (h1 : 1 ≤ ρ)
    (hρ : ∀ x : K, ∃ o : 𝓞 K, ∀ v, ‖τ v (x + o)‖ ≤ ρ)
    (hN : ∀ o : 𝓞 K, o ≠ 0 → 1 ≤ ∏ v, ‖τ v o‖) :
    ∃ Ω : Set (ι → roots (ptMat p) → ℂ), MeasurableSet Ω ∧ MeasureTheory.volume Ω ≤
      ENNReal.ofReal ((|(NumberField.discr K : ℝ)| ^ (1 / 2 : ℝ) * (4 * (N : ℝ) ^ 2) ^ (Fintype.card ι) *
        ((4 ^ N * (N.factorial : ℝ) ^ 2 * ρ ^ (2 * N)) ^ Fintype.card ι * PiZ τ (L * ptMat p * U) ^ 2) ^ 4 *
        (Ideal.absNorm I : ℝ) * (N.factorial : ℝ) ^ (2 * Fintype.card ι)) ^ (N ^ 2)) ∧
      ∀ c : ι → roots (ptMat p) → ℂ, ∃ a ∈ stabU (L * ptMat p * U), EntIn I (a - 1) ∧
        (fun v (q : roots (ptMat p)) => ((U * a * U⁻¹).map (τ v) * ofRoots (roots (ptMat p)) (c v) :
          Matrix (Fin N) (Fin N) ℂ) q.1.1 q.1.2) ∈ Ω := by
  obtain ⟨B, hB, hBi, hBb⟩ := reduce_up τ h1 hρ hU
  have hLt : IsUpUni Lᵀ := fun i j => ⟨(hL j i).1, fun h => (hL j i).2 h.symm⟩
  obtain ⟨A, hA, hAi, hAb⟩ := reduce_up τ h1 hρ hLt
  have hL' : IsLoUni (Aᵀ * L) := by
    intro i j
    have := upUni_mul hLt hA j i
    rw [← Matrix.transpose_apply (Lᵀ * A) i j, Matrix.transpose_mul, Matrix.transpose_transpose] at this
    exact ⟨this.1, fun h => this.2 h.symm⟩
  have hLb : ∀ v i j, ‖τ v ((Aᵀ * L) i j)‖ ≤ ρ := by
    intro v i j
    have := hAb v j i
    rwa [← Matrix.transpose_apply (Lᵀ * A) i j, Matrix.transpose_mul, Matrix.transpose_transpose] at this
  have hU' := upUni_mul hU hB
  set κ : ℝ := 4 ^ N * (N.factorial : ℝ) ^ 2 * ρ ^ (2 * N) with hκ
  have hκ1 : 1 ≤ κ := by
    have : (1 : ℝ) ≤ N.factorial := by exact_mod_cast N.factorial_pos
    refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ?_ ?_) ?_ <;>
      apply one_le_pow₀ <;> first | assumption | norm_num
  have hZ' : EntIn ⊤ (Aᵀ * L * ptMat p * (U * B)) := by
    have := entIn_mul (A := Aᵀ) (fun i j => hAi j i) hZ hBi
    simpa only [Matrix.mul_assoc] using this
  obtain ⟨Ω, hm, hv, hc⟩ := Cov.covolume_congruence_stabiliser K ι τ N (Aᵀ * L) (U * B) p I
    (κ ^ Fintype.card ι * PiZ τ (L * ptMat p * U) ^ 2)
    (fun v => κ * ∏ l ∈ Finset.range N, gg2 ‖τ v (leadMinorE (ptMat p) (l + 1))‖) hs hw hr hL' hU' hZ' hI
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hκ1) (one_le_pow₀ (one_le_PiZ τ _)))
    (fun t J J' v => by
      have := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.minorBound N ((Aᵀ * L).map (τ v)) ((ptMat p).map (τ v))
        ((U * B).map (τ v)) ρ _ h1 (hLb v) (hBb v) (minor_pt_le (τ v) p) t J J'
      rw [← Matrix.map_mul, ← Matrix.map_mul] at this
      rw [RingHom.map_det]
      exact this)
    (by
      have h2 := prod_maxOneMulMaxOneInv_leadingMinors_le_sq τ hN hZ
      simp only [leadMinor_cell hL hU] at h2
      rw [Finset.prod_congr rfl fun v _ => max_eq_right (one_le_mul_of_one_le_of_one_le hκ1
        (one_le_prod0 fun l _ => one_le_maxOneMulMaxOneInv _)), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ]
      exact mul_le_mul_of_nonneg_left h2 (by positivity))
  refine ⟨Ω, hm, hv, fun c => ?_⟩
  obtain ⟨a, ha, hai, hΩ⟩ := hc c
  have hBd : B.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (up_tri hB), Finset.prod_eq_one fun i _ => (hB i i).2 rfl]
  have e : U * (B * a * B⁻¹) * U⁻¹ = U * B * a * (U * B)⁻¹ := by
    simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]
  refine ⟨B * a * B⁻¹, ?_, ?_, ?_⟩
  · rw [(stab_cell K N L U p hL hU).1, e, ← (stab_cell K N _ _ p hL' hU').1]
    exact ha
  · rw [← conj_sub_one (up_det hB)]
    exact entIn_mul hBi hai (entIn_inv hBi hBd)
  · rw [e]; exact hΩ

end Red

theorem num (b rd ρ d P S NI : ℝ) (N f r c n : ℕ) (hb : 2 ≤ b) (hN : N = r + 1) (hr : 1 ≤ r)
    (hn : n = c + 20) (hrd0 : 0 ≤ rd) (hrd : rd ≤ b) (hd0 : 0 ≤ d) (hd : d ≤ b ^ f) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ b ^ (2 * N)) (hNI0 : 0 ≤ NI) (hNI : NI ≤ (b ^ ((1 + 4 * c) * N)) ^ (4 * f) * P ^ 10)
    (hP0 : 0 ≤ P) (hP : P ≤ (b ^ ((2 + 4 * n) * N ^ 2)) ^ (N * f) * S) (hS : 1 ≤ S) :
    (d * (4 * (N : ℝ) ^ 2) ^ f * ((4 ^ N * (N.factorial : ℝ) ^ 2 * ρ ^ (2 * N)) ^ f * P ^ 2) ^ 4 * NI *
        (N.factorial : ℝ) ^ (2 * f)) ^ (N ^ 2) * rd ^ (2 * f * N ^ 3) ≤
      ((b ^ (n * (2 * N) ^ 2 * f)) ^ (n * (2 * N)) * S ^ 4) ^ (n * r ^ 2) := by
  have hb1 : 1 ≤ b := by linarith
  have hS0 : 0 ≤ S := by linarith
  have h1 : (N : ℝ) ≤ b ^ N := by
    calc (N : ℝ) ≤ 2 ^ N := by exact_mod_cast N.lt_two_pow_self.le
      _ ≤ b ^ N := by gcongr
  have h4 : (4 : ℝ) ≤ b ^ 2 := by nlinarith
  have h2 : (N.factorial : ℝ) ≤ (b ^ N) ^ N := by
    calc (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast N.factorial_le_pow
      _ ≤ _ := by gcongr
  have hNI' : NI ≤ (b ^ ((1 + 4 * c) * N)) ^ (4 * f) * ((b ^ ((2 + 4 * n) * N ^ 2)) ^ (N * f) * S) ^ 10 :=
    hNI.trans (by gcongr)
  calc _ ≤ (b ^ f * (b ^ 2 * (b ^ N) ^ 2) ^ f * (((b ^ 2) ^ N * ((b ^ N) ^ N) ^ 2 * (b ^ (2 * N)) ^ (2 * N)) ^ f *
        ((b ^ ((2 + 4 * n) * N ^ 2)) ^ (N * f) * S) ^ 2) ^ 4 *
        ((b ^ ((1 + 4 * c) * N)) ^ (4 * f) * ((b ^ ((2 + 4 * n) * N ^ 2)) ^ (N * f) * S) ^ 10) *
        ((b ^ N) ^ N) ^ (2 * f)) ^ (N ^ 2) * b ^ (2 * f * N ^ 3) := by gcongr
    _ = b ^ (N ^ 2 * f * (3 + (14 + 16 * c) * N + 26 * N ^ 2 + (36 + 72 * n) * N ^ 3) + 2 * f * N ^ 3) *
        S ^ (18 * N ^ 2) := by ring
    _ ≤ b ^ (8 * n ^ 3 * (r ^ 2 * f * N ^ 3)) * S ^ (4 * n * r ^ 2) := by
      have hN2 : N ^ 2 ≤ 4 * r ^ 2 := by subst hN; nlinarith
      have hN1 : 1 ≤ N := by omega
      have a0 : 1 ≤ N ^ 3 := Nat.one_le_pow _ _ hN1
      have a1 : N ≤ N ^ 3 := Nat.le_self_pow (by norm_num) _
      have a2 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right hN1 (by norm_num)
      have a3 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
      have hn' : 20 ≤ n := by omega
      refine mul_le_mul (pow_le_pow_right₀ hb1 ?_) (pow_le_pow_right₀ hS ?_) (by positivity) (by positivity)
      · calc _ ≤ 4 * r ^ 2 * f * (3 * N ^ 3 + (14 + 16 * n) * N ^ 3 + 26 * N ^ 3 + (36 + 72 * n) * N ^ 3) +
              2 * (r ^ 2 * f) * N ^ 3 := by
              gcongr
              · omega
              · omega
              · exact Nat.le_mul_of_pos_left _ a3
          _ = (318 + 352 * n) * (r ^ 2 * f * N ^ 3) := by ring
          _ ≤ _ := by
              refine Nat.mul_le_mul_right _ ?_
              have : 400 * n ≤ n ^ 3 := by
                have : 400 ≤ n ^ 2 := by nlinarith
                calc 400 * n ≤ n ^ 2 * n := by gcongr
                  _ = n ^ 3 := by ring
              omega
      · nlinarith
    _ = _ := by ring

section Sign
open GlobalTheory.LoopV GlobalTheory.LoopV.Cell
variable {K : Type} [Field K] {r : ℕ}

theorem zhatOM_eq (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM Z = Z * Matrix.diagonal fun b : Fin (r + 1) => (-1 : K) ^ (r - b.val) := by
  ext a b
  rw [Matrix.mul_diagonal, mul_comm]; rfl

theorem norm_lead_zhatOM (τ : K →+* ℂ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (l : ℕ) :
    ‖τ (leadMinorE (ZhatOM Z) l)‖ = ‖τ (leadMinorE Z l)‖ := by
  unfold leadMinorE
  split_ifs with h
  · have := Matrix.det_mul_row (fun b : Fin l => (-1 : K) ^ (r - (Fin.castLE h b).val))
      (Z.submatrix (Fin.castLE h) (Fin.castLE h))
    have e : ((ZhatOM Z).submatrix (Fin.castLE h) (Fin.castLE h)).det = _ := this
    rw [e]
    simp [norm_prod]
  · rfl

theorem sign_eq (i j : Fin (r + 1)) :
    (-1 : K) ^ (r - i.val) * (-1) ^ (r - j.val) = (-1) ^ (i.val + j.val) := by
  have hi := i.2
  have hj := j.2
  have h : ∀ k, k ≤ r → (-1 : K) ^ (r - k) = (-1) ^ r * (-1) ^ k := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [Nat.add_sub_cancel_left, pow_add, mul_right_comm, ← pow_add, ← two_mul, pow_mul]
    simp
  rw [h _ (by omega), h _ (by omega), mul_mul_mul_comm, ← pow_add, ← two_mul, pow_mul, pow_add]
  simp

theorem sign_stab {Z a : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (ha : a ∈ stabU (ZhatOM Z)) :
    (Matrix.of fun i j => (-1) ^ (i.val + j.val) * a i j) ∈ stabU Z := by
  set S : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
    Matrix.diagonal fun b : Fin (r + 1) => (-1 : K) ^ (r - b.val) with hS
  have hSS : S * S = 1 := by
    rw [hS, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext b
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have e : (Matrix.of fun i j => (-1) ^ (i.val + j.val) * a i j) = S * a * S := by
    ext i j
    rw [hS, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, ← sign_eq]; ring
  refine ⟨fun i j => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · simp [(ha.1 i j).1 h]
  · subst h
    rw [Matrix.of_apply, (ha.1 i i).2 rfl, ← two_mul, pow_mul]; simp
  · have h2 := ha.2
    rw [zhatOM_eq, ← hS, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hSS] at h2
    rw [e]
    simpa only [Matrix.mul_assoc] using h2

end Sign

theorem frame_mem (D : D7) {T : D.host.E} (Λ : LatV D) (F : LFlag (hS D) D.R.rS T) (h1 : IsLift Λ F)
    (h2 : XLam Λ F = XS D F.fl) (b : Fin (D.R.rS + 1)) : frame F b ∈ Λ := by
  refine Fin.lastCases ?_ (fun a => ?_) b
  · simpa [frame, FlagG.fvec] using h1.1
  · have : F.fl.e a ∈ XS D F.fl := by
      refine Submodule.subset_span ⟨a, 1, ?_, (one_smul _ _).symm⟩
      have ha := a.2
      have e : -((D.R.rS : ℤ) - (a : ℕ)) = -((D.R.rS - a : ℕ) : ℤ) := by omega
      rw [e, _root_.zpow_neg, _root_.zpow_natCast]
      have hne : ddS D ≠ 0 := by
        intro h
        have := (GlobalTheory.real_places_facts D).2.2.2.2.2.2.2.2.1
        rw [h] at this
        have h1 := (GlobalTheory.real_places_facts D).2.2.2.2.1
        have : (0 : ℝ) < 0 := by
          calc (0 : ℝ) < D.host.rdE ^ (2 * D.R.f) := by positivity
            _ = 0 := by simpa using this.symm
        exact lt_irrefl _ this
      rw [FractionalIdeal.mem_inv_iff (pow_ne_zero _ hne)]
      intro y hy
      rw [one_mul]
      have hle : ddS D ^ (D.R.rS - a) ≤ 1 := by
        unfold ddS
        rw [← FractionalIdeal.coeIdeal_pow]
        exact FractionalIdeal.coeIdeal_le_one
      exact hle hy
    rw [← h2] at this
    simpa [frame, FlagG.fvec] using this.1

theorem zhat_int (D : D7) {T T' : D.host.E} (Λ : LatV D) (F : LFlag (hS D) D.R.rS T)
    (F' : LFlag (hS D) D.R.rS T') (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ)
    (h : ∀ b, frame F b ∈ Λ) (h' : ∀ b, frame F' b ∈ Λ) :
    GlobalTheory.LoopV.EntIn ⊤ (ZhatOM (ZhatL F F')) := by
  intro a b
  have h1 : frame F' b ∈ Formalism.HermitianLatticesTheory.dual (hS D).hT Λ := by rw [hu]; exact h' b
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    Submodule.mem_one] at h1
  obtain ⟨o, ho⟩ := h1 _ (h a)
  refine ⟨(-1) ^ (D.R.rS - b.val) * o, trivial, ?_⟩
  have : (o : D.host.E) = ZhatL F F' a b := ho
  simp [ZhatOM, ← this]

theorem frameExp_le (r l : ℕ) (hl : l ≤ r + 1) : frameExp r l ≤ (r + 1) ^ 2 := by
  unfold frameExp
  calc _ ≤ (Finset.Icc 1 l).card • (r + 1) := Finset.sum_le_card_nsmul _ _ _ fun a _ => Nat.sub_le _ _
    _ ≤ _ := by simp only [Nat.card_Icc, smul_eq_mul, sq]; gcongr; omega

theorem PiZ_le (D : D7) (b : ℝ) (n : ℕ) (hb : 1 ≤ b) (hrd : D.host.rdE ≤ b) (Z : GramM D) :
    PiZ (embS D) Z ≤ (b ^ ((2 + 4 * n) * (D.R.rS + 1) ^ 2)) ^ ((D.R.rS + 1) * D.R.f) * sizeZ D b n Z := by
  obtain ⟨hc, -, -, hm, h1, -⟩ := GlobalTheory.real_places_facts D
  unfold PiZ sizeZ
  rw [← hc, pow_mul _ (D.R.rS + 1), ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => Finset.prod_nonneg fun _ _ => by positivity) fun v _ => ?_
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  nth_rewrite 4 [← Finset.card_range (D.R.rS + 1)]
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun _ _ => by positivity) fun l hl => ?_
  have hl' : l + 1 ≤ D.R.rS + 1 := Finset.mem_range.1 hl
  have e : b ^ ((n : ℝ) * (D.R.m : ℝ) ^ 2) = b ^ (4 * n * (D.R.rS + 1) ^ 2) := by
    rw [← Real.rpow_natCast b (4 * n * (D.R.rS + 1) ^ 2), hm]; congr 1; push_cast; ring
  rw [e, add_comm 1 l]
  refine max_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hb) (le_max_left _ _)) ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
  unfold absDl absReal
  have e2 : D.host.rdE ^ (-(2 * (frameExp D.R.rS (l + 1) : ℝ))) =
      (D.host.rdE ^ (2 * frameExp D.R.rS (l + 1)))⁻¹ := by
    rw [Real.rpow_neg (by linarith), ← Real.rpow_natCast]; congr 2; push_cast; rfl
  have h3 : D.host.rdE ^ (2 * frameExp D.R.rS (l + 1)) ≤ b ^ (2 * (D.R.rS + 1) ^ 2) :=
    (pow_le_pow_left₀ (by linarith) hrd _).trans
      (pow_le_pow_right₀ hb (Nat.mul_le_mul_left _ (frameExp_le _ _ hl')))
  rw [e2, add_mul, pow_add]
  have h4 : 0 < D.host.rdE ^ (2 * frameExp D.R.rS (l + 1)) := by positivity
  have h5 : 0 < b ^ (4 * n * (D.R.rS + 1) ^ 2) := by positivity
  calc _ = D.host.rdE ^ (2 * frameExp D.R.rS (l + 1)) * b ^ (4 * n * (D.R.rS + 1) ^ 2) *
        (‖embS D v (leadMinorE Z (l + 1))‖ * (D.host.rdE ^ (2 * frameExp D.R.rS (l + 1)))⁻¹ /
          b ^ (4 * n * (D.R.rS + 1) ^ 2)) := by field_simp
    _ ≤ _ := by gcongr

theorem ideal_bound (D : D7) {T T' : ℕ} (F : LFlag (hS D) D.R.rS (T : D.host.E))
    (F' : LFlag (hS D) D.R.rS (T' : D.host.E)) (hr : 1 ≤ D.R.rS) (Y : ℝ) (hY : 1 + (T : ℝ) * T' ≤ Y) :
    (∏ τ, ‖embS D τ (Gval F F')‖) ^ 4 * ∏ τ, ‖embS D τ (Dr1 F F')‖ ^ 2 ≤
      Y ^ (4 * D.R.f) * PiZ (embS D) (ZhatL F F') ^ 10 := by
  obtain ⟨hc, -, -, -, -, hs, -⟩ := GlobalTheory.real_places_facts D
  set Q : D.what₂.Tau → ℝ := fun v => ∏ l ∈ Finset.range (D.R.rS + 1),
    max 1 ‖embS D v (leadMinorE (ZhatL F F') (l + 1))‖ with hQ
  have hq : ∀ v l, l < D.R.rS + 1 → ‖embS D v (leadMinorE (ZhatL F F') (l + 1))‖ ≤ Q v := fun v l hl =>
    (le_max_right _ _).trans (le_prod_of_one_le
      (f := fun l => max 1 ‖embS D v (leadMinorE (ZhatL F F') (l + 1))‖)
      (fun _ _ => le_max_left _ _) (Finset.mem_range.2 hl))
  have h1 : ∀ v, ‖embS D v (Dr1 F F')‖ ≤ Q v := fun v => hq v _ (Nat.lt_succ_self _)
  have h2 : ∀ v, ‖embS D v (Dr F F')‖ ≤ Q v := fun v => by
    have := hq v (D.R.rS - 1) (by omega)
    rwa [Nat.sub_add_cancel hr] at this
  have hY0 : 0 ≤ Y := le_trans (by positivity) hY
  have h3 : ∀ v, ‖embS D v (Gval F F')‖ ≤ Y * Q v ^ 2 := fun v => by
    have e : Gval F F' = Dr1 F F' * star (Dr1 F F') - (T : D.host.E) * T' * (Dr F F' * star (Dr F F')) := rfl
    rw [e, map_sub]
    refine (norm_sub_le _ _).trans ?_
    simp only [map_mul, hs, norm_mul, map_natCast, Complex.norm_natCast, RCLike.norm_conj]
    have a1 := h1 v
    have a2 := h2 v
    have a0 : 0 ≤ Q v := (norm_nonneg _).trans a1
    calc _ ≤ Q v * Q v + (T : ℝ) * T' * (Q v * Q v) := by gcongr
      _ = (1 + (T : ℝ) * T') * Q v ^ 2 := by ring
      _ ≤ _ := by gcongr
  have hP : PiZ (embS D) (ZhatL F F') = ∏ v, Q v := rfl
  calc _ ≤ (∏ v, Y * Q v ^ 2) ^ 4 * ∏ v, Q v ^ 2 := by
        gcongr with v _ v _
        · exact h3 v
        · exact h1 v
    _ = _ := by
        rw [hP, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hc, Finset.prod_pow]; ring

theorem covolume_term : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ (F0 : Fb D u) (Λ : LatV D), IsBase D u F0 → IsRowLat D F0 Λ → ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → ∀ (p : Point D.host.E (D.R.rS + 1)) (L U : GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D F0) F') = L * ptMat p * U → ∃ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat p) → ℂ), MeasurableSet Ω ∧ MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) ≤ ENNReal.ofReal (HHZ D large₂.sc.b C (ZhatL (lf D F0) F') ^ (C * (D.R.rS : ℝ) ^ 2)) ∧ ∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat p) → ℂ, ∃ n ∈ NLam Λ (lf D F0) ∩ NLam Λ F', ∃ a : GramM D, (∀ j : Fin (D.R.rS + 1), n (frame F' j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame F' i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat p)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω := by
  intro Cg cb Cu cT CT C0 A
  refine ⟨((⌈CT⌉₊ + 20 : ℕ) : ℝ), by exact_mod_cast (by omega : 1 ≤ ⌈CT⌉₊ + 20), ?_⟩
  intro D large₂ u u' C' Cl hCl hH F0 Λ hF0 hΛ F' hF' p L U hL hU hZ
  obtain ⟨hc, hfE, -, hm, hrd1, hs, hnorm, -, -, hw⟩ := GlobalTheory.real_places_facts D
  obtain ⟨⟨hS0, -⟩, hSt, -⟩ := hH
  obtain ⟨-, -, hmf, -, hlf, -, -, -, -, -, hlrd, -, -, -, -, -, -, -, -, -, -, -, hT, -⟩ := hS0
  obtain ⟨I, hI, hNI, hcong⟩ := GlobalTheory.T.congruence_stabU_from_integral_unipotent_isometry D u u' F0 Λ hSt hF0 hΛ F' hF'
  have hr : 1 ≤ D.R.rS := hSt.1
  have hL1 : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hbe : Real.exp 1 ≤ large₂.sc.b := Real.exp_le_exp.2 hL1
  have hb : 2 ≤ large₂.sc.b := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hbe
  have hb1 : 1 ≤ large₂.sc.b := by linarith
  have hrd : D.host.rdE ≤ large₂.sc.b :=
    (Real.log_le_iff_le_exp (by linarith)).1 (hlrd.trans (div_le_self (by linarith) hCl))
  have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
  have hf1' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  have hr' : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hr
  have hf : (D.R.f : ℝ) ≤ large₂.sc.b ^ D.R.rS := by
    have h1 : Real.sqrt D.R.rS ≤ D.R.rS := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have h2 := (Real.log_le_iff_le_exp (by linarith)).1 (hlf.trans h1)
    rw [← Real.exp_one_pow] at h2
    exact h2.trans (by gcongr)
  set ρ : ℝ := Real.sqrt (finrank ℚ D.host.E) * D.host.rdE with hρ
  have hs1 : 1 ≤ Real.sqrt (finrank ℚ D.host.E) := by
    rw [hfE]; refine Real.one_le_sqrt.2 ?_; push_cast; linarith
  have hρ1 : 1 ≤ ρ := one_le_mul_of_one_le_of_one_le hs1 hrd1
  have hρb : ρ ≤ large₂.sc.b ^ (2 * (D.R.rS + 1)) := by
    have h1 : Real.sqrt (finrank ℚ D.host.E) ≤ 2 * D.R.f := by
      rw [hfE]; push_cast
      exact Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    calc ρ ≤ (large₂.sc.b * large₂.sc.b ^ D.R.rS) * large₂.sc.b :=
          mul_le_mul (h1.trans (by gcongr)) hrd (by linarith) (by positivity)
      _ = large₂.sc.b ^ (D.R.rS + 2) := by ring
      _ ≤ _ := pow_le_pow_right₀ hb1 (by omega)
  have hcx : ∀ w : InfinitePlace D.host.E, w.IsComplex := by
    have h1 : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
      rw [← hc]
      exact (Fintype.card_of_bijective ((Function.bijective_iff_existsUnique _).2 hw)).symm
    have h2 := InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E
    have h4 : InfinitePlace.nrRealPlaces D.host.E = 0 := by omega
    intro w
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hw'
    exact (Fintype.card_eq_zero_iff.1 h4).elim ⟨w, hw'⟩
  have hcov : ∀ x : D.host.E, ∃ o : 𝓞 D.host.E, ∀ v, ‖embS D v (x + o)‖ ≤ ρ := by
    intro x
    obtain ⟨a, ha⟩ := GlobalTheory.coveringO_holds D.host.E hcx (fun w => w.embedding x)
    refine ⟨-a, fun v => ?_⟩
    have := ha (InfinitePlace.mk (embS D v))
    rw [← map_sub, InfinitePlace.norm_embedding_eq, InfinitePlace.apply] at this
    have e : x + ((-a : 𝓞 D.host.E) : D.host.E) = x - a := by simp [sub_eq_add_neg]
    rw [e]; exact this
  have hN : ∀ o : 𝓞 D.host.E, o ≠ 0 → 1 ≤ ∏ v, ‖embS D v o‖ := by
    intro o ho
    have h1 := hnorm o
    rw [Finset.prod_pow, ← Algebra.coe_norm_int] at h1
    have h2 : Algebra.norm ℤ o ≠ 0 := Algebra.norm_ne_zero_iff.2 ho
    have h3 : (1 : ℝ) ≤ |((Algebra.norm ℤ o : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h2
    refine (one_le_sq_iff₀ (Finset.prod_nonneg fun _ _ => norm_nonneg _)).1 ?_
    rw [h1]; simpa using h3
  have hint : GlobalTheory.LoopV.EntIn ⊤ (L * ptMat p * U) := by
    rw [← hZ]
    exact zhat_int D Λ _ _ hΛ.2.1.2.1 (frame_mem D Λ _ hΛ.2.1.2.2.1 hΛ.2.2)
      (frame_mem D Λ _ hF'.1.1 hF'.2.2)
  obtain ⟨Ω, hΩm, hΩv, hΩc⟩ := cov_lead (embS D) L U p I ρ hs hw (by rw [hc, hfE]) hL hU hint hI hρ1 hcov hN
  refine ⟨Ω, hΩm, ?_, fun c => ?_⟩
  · have hPi : PiZ (embS D) (L * ptMat p * U) = PiZ (embS D) (ZhatL (lf D F0) F') := by
      rw [← hZ]; unfold PiZ; simp only [norm_lead_zhatOM]
    rw [hPi, hc] at hΩv
    refine (mul_le_mul_left hΩv _).trans ?_
    rw [← ENNReal.ofReal_mul' (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hTb : ∀ w, (Tu D w : ℝ) ≤ large₂.sc.b ^ (⌈CT⌉₊ * (2 * (D.R.rS + 1))) := by
      intro w
      refine (hT w).2.trans ?_
      rw [← Real.rpow_natCast]
      refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
      rw [hm]; push_cast
      have := Nat.le_ceil CT
      nlinarith
    have hY : 1 + (Tu D u : ℝ) * Tu D u' ≤ large₂.sc.b ^ ((1 + 4 * ⌈CT⌉₊) * (D.R.rS + 1)) := by
      have a1 := hTb u
      have a2 := hTb u'
      set X := large₂.sc.b ^ (⌈CT⌉₊ * (2 * (D.R.rS + 1))) with hX
      have hX1 : 1 ≤ X := one_le_pow₀ hb1
      have a3 : (Tu D u : ℝ) * Tu D u' ≤ X * X := by gcongr
      have a4 : large₂.sc.b ≤ large₂.sc.b ^ (D.R.rS + 1) := le_self_pow₀ hb1 (by omega)
      calc _ ≤ 2 * (X * X) := by nlinarith
        _ ≤ large₂.sc.b ^ (D.R.rS + 1) * (X * X) := by gcongr; linarith
        _ = _ := by rw [hX]; ring
    have hd : |(NumberField.discr D.host.E : ℝ)| ^ (1 / 2 : ℝ) ≤ large₂.sc.b ^ D.R.f := by
      have : |(NumberField.discr D.host.E : ℝ)| ^ (1 / 2 : ℝ) = D.host.rdE ^ D.R.f := by
        unfold Host.rdE
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), hfE]
        congr 1; push_cast; field_simp
      rw [this]; gcongr
    have hS : 1 ≤ sizeZ D large₂.sc.b ((⌈CT⌉₊ + 20 : ℕ) : ℝ) (ZhatL (lf D F0) F') :=
      one_le_prod0 fun _ _ => one_le_prod0 fun _ _ => le_max_left _ _
    have key := num large₂.sc.b D.host.rdE ρ _ _ _ (Ideal.absNorm I : ℝ) (D.R.rS + 1) D.R.f D.R.rS ⌈CT⌉₊ _ hb rfl hr rfl
      (by linarith) hrd (by positivity) hd (by linarith) hρb (by positivity)
      (hNI.trans ((ideal_bound D _ F' hr _ hY)))
      (zero_le_one.trans (one_le_PiZ _ _)) (PiZ_le D _ _ hb1 hrd _) hS
    refine key.trans (le_of_eq ?_)
    unfold HHZ
    rw [hm, show 2 * D.R.rS + 2 = 2 * (D.R.rS + 1) by ring]
    norm_cast
  · obtain ⟨a, ha, hai, hΩ⟩ := hΩc c
    rw [← hZ] at ha
    obtain ⟨n, hn, hn'⟩ := hcong _ (sign_stab ha) (by
      intro i j
      obtain ⟨o, ho, ho'⟩ := hai i j
      refine ⟨(-1) ^ (i.val + j.val) * o, I.mul_mem_left _ ho, ?_⟩
      by_cases h : i = j
      · subst h
        simp [ho', ← two_mul, pow_mul]
      · simp [ho', Matrix.one_apply_ne h])
    exact ⟨n, hn, a, hn', hΩ⟩

end GlobalTheory.LoopC.CovTerm
