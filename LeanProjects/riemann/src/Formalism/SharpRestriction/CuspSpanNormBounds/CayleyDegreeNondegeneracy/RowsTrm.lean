import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDef
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Uni

variable {K : Type*} [CommRing K] {N : ℕ}

theorem rows_loUni_mul {L M : Matrix (Fin N) (Fin N) K} (hL : IsLoUni L) (hM : IsLoUni M) : IsLoUni (L * M) := by
  intro i j
  constructor
  · intro hij
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge i k with hik | hki
    · rw [(hL i k).1 hik, zero_mul]
    · rw [(hM k j).1 (lt_of_le_of_lt hki hij), mul_zero]
  · intro hij
    subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hL i i).2 rfl, (hM i i).2 rfl, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [(hM k i).1 h, mul_zero]
      · rw [(hL i k).1 h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem rows_upUni_mul {L M : Matrix (Fin N) (Fin N) K} (hL : IsUpUni L) (hM : IsUpUni M) : IsUpUni (L * M) := by
  intro i j
  constructor
  · intro hji
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge k i with hki | hik
    · rw [(hL i k).1 hki, zero_mul]
    · rw [(hM k j).1 (lt_of_lt_of_le hji hik), mul_zero]
  · intro hij
    subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hL i i).2 rfl, (hM i i).2 rfl, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [(hL i k).1 h, zero_mul]
      · rw [(hM k i).1 h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

def rows_tw {r : ℕ} (B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun i j => (-1) ^ (r - i.val) * B i j * (-1) ^ (r - j.val)

theorem rows_ZhatOM_mul {r : ℕ} (A Z B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM (A * Z * B) = A * ZhatOM Z * rows_tw B := by
  ext a b
  simp only [ZhatOM, rows_tw, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  have hs : ((-1 : K) ^ (r - c.val)) * (-1) ^ (r - c.val) = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination (-(A a d * Z d c * B c b * (-1) ^ (r - b.val))) * hs

end Uni

section Inv

variable {D : D7}

private theorem rows_leadMinor_aux_lemma {E : Type*} [CommRing E] {n l : ℕ} (hl : l ≤ n)
    (P Q R : Matrix (Fin n) (Fin n) E) (hP0 : ∀ a b, a < b → P a b = 0) (hP1 : ∀ a, P a a = 1)
    (hR0 : ∀ a b, b < a → R a b = 0) (hR1 : ∀ a, R a a = 1) :
    ((P * Q * R).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (Q.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have hrange : ∀ q : Fin n, q ∉ Set.range (Fin.castLE hl) → l ≤ q.val := by
    intro q hq
    by_contra hlt
    push_neg at hlt
    exact hq ⟨⟨q.val, hlt⟩, Fin.ext rfl⟩
  have hval : ∀ i : Fin l, ((Fin.castLE hl i : Fin n) : ℕ) = (i : ℕ) := fun i => rfl
  have key : (P * Q * R).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      P.submatrix (Fin.castLE hl) (Fin.castLE hl) * Q.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        R.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    have inner : ∀ p : Fin n, ∑ q : Fin n, P (Fin.castLE hl i) q * Q q p =
        ∑ q : Fin l, P (Fin.castLE hl i) (Fin.castLE hl q) * Q (Fin.castLE hl q) p := by
      intro p
      symm
      apply Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
      · intro q hq
        have h1 := hrange q hq
        have h0 := i.isLt
        have h2 : Fin.castLE hl i < q := by
          rw [Fin.lt_iff_val_lt_val, hval]
          omega
        simp only [hP0 _ _ h2, zero_mul]
      · intro q
        rfl
    simp only [inner]
    symm
    apply Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
    · intro p hp
      have h1 := hrange p hp
      have h0 := j.isLt
      have h2 : Fin.castLE hl j < p := by
        rw [Fin.lt_iff_val_lt_val, hval]
        omega
      simp only [hR0 _ _ h2, mul_zero]
    · intro p
      rfl
  rw [key, Matrix.det_mul, Matrix.det_mul]
  have dP : (P.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · simp [hP1]
    · intro i j hij
      have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
      simp only [Matrix.submatrix_apply]
      apply hP0
      rw [Fin.lt_iff_val_lt_val, hval, hval]
      exact Fin.lt_iff_val_lt_val.mp hij'
  have dR : (R.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · simp [hR1]
    · intro i j hij
      simp only [Matrix.submatrix_apply]
      apply hR0
      rw [Fin.lt_iff_val_lt_val, hval, hval]
      exact Fin.lt_iff_val_lt_val.mp hij
  rw [dP, dR, one_mul, mul_one]

theorem rows_leadMinor_inv {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) (l : ℕ) : leadMinorE Z₂ l = leadMinorE Z l := by
  obtain ⟨A, B, hA0, hA1, hB0, hB1, hZ⟩ := h
  subst hZ
  unfold leadMinorE
  split_ifs with hl
  · exact rows_leadMinor_aux_lemma hl _ _ _ (fun a b hab => by simp [hA0 a b hab])
      (fun a => by simp [hA1]) (fun a b hab => by simp [hB0 a b hab]) (fun a => by simp [hB1])
  · rfl

theorem rows_absDl_inv {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) (l : ℕ) (τ : D.what₂.Tau) :
    absDl D Z₂ l τ = absDl D Z l τ := by
  simp only [absDl, rows_leadMinor_inv h]

theorem rows_Gz_inv {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) (T T' : ℝ) (τ : D.what₂.Tau) :
    Gz D T T' Z₂ τ = Gz D T T' Z τ := by
  simp only [Gz, rows_absDl_inv h]

theorem rows_sizeZ_inv {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) (b C : ℝ) : sizeZ D b C Z₂ = sizeZ D b C Z := by
  simp only [sizeZ, rows_absDl_inv h]

theorem rows_HHZ_inv {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) (b C : ℝ) : HHZ D b C Z₂ = HHZ D b C Z := by
  simp only [HHZ, rows_sizeZ_inv h]

theorem rows_nV_inv {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) (T T' : ℝ) (τ : D.what₂.Tau) :
    nV D T T' Z₂ τ = nV D T T' Z τ := by
  simp only [nV, rows_Gz_inv h]

theorem rows_nZ_inv {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) (u u' : D.what₂.Word) :
    wordPairGramNorm D u u' Z₂ = wordPairGramNorm D u u' Z := by
  simp only [wordPairGramNorm, rows_nV_inv h]

theorem gramProductG0_equiv_invariant {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) (u u' : D.what₂.Word) :
    wordPairGramProduct D u u' Z₂ = wordPairGramProduct D u u' Z := by
  simp only [wordPairGramProduct, rows_Gz_inv h]

theorem rows_RelZ_inv {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) (hZ : RelZ D Z) : RelZ D Z₂ := by
  obtain ⟨A, B, hA0, hA1, hB0, hB1, hZe⟩ := h
  unfold RelZ IsInCell at hZ ⊢
  obtain ⟨p, L, U, hL, hU, hZp⟩ := hZ
  have hs : ∀ k : ℕ, ((-1 : D.host.E) ^ k) * (-1) ^ k = 1 := fun k => by
    rw [← mul_pow]
    norm_num
  refine ⟨p, A.map (fun x => (x : D.host.E)) * L, U * rows_tw (B.map (fun x => (x : D.host.E))), ?_, ?_, ?_⟩
  · apply rows_loUni_mul _ hL
    intro i j
    exact ⟨fun hij => by simp [hA0 i j hij], fun hij => by subst hij; simp [hA1]⟩
  · apply rows_upUni_mul hU
    intro i j
    refine ⟨fun hji => ?_, fun hij => ?_⟩
    · simp [rows_tw, hB0 i j hji]
    · subst hij
      simp [rows_tw, hB1, hs]
  · rw [hZe, rows_ZhatOM_mul, hZp]
    simp only [Matrix.mul_assoc]

theorem rows_RelZ_term (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hrel : D.s.relevant t) : RelZ D (termGramMatrix X t) := by
  unfold RelZ
  exact ⟨D.s.ptOf t, X.pt_cell t hG hrel⟩

end Inv

section Size

variable {D : D7}

theorem rows_one_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro a s ha ih h
  rw [Finset.prod_insert ha]
  have h1 : 1 ≤ f a := h a (Finset.mem_insert_self a s)
  have h2 : 1 ≤ ∏ i ∈ s, f i := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
  nlinarith

theorem rows_one_le_sizeZ (b C : ℝ) (Z : GramM D) : 1 ≤ sizeZ D b C Z := by
  unfold sizeZ
  exact rows_one_le_prod _ _ (fun τ _ => rows_one_le_prod _ _ (fun l _ => le_max_left _ _))

theorem rows_absDl_nonneg (hrd : 0 < D.host.rdE) (Z : GramM D) (l : ℕ) (τ : D.what₂.Tau) : 0 ≤ absDl D Z l τ := by
  unfold absDl absReal
  first
    | exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hrd.le _)
    | exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg_of_nonneg hrd.le _)

theorem rows_max_cmp {b x c Ch M : ℝ} (hb : 1 ≤ b) (hx : 0 ≤ x) (hM : 0 ≤ M) :
    max 1 (x / b ^ (c * M)) ≤ b ^ (max (Ch - c) 0 * M) * max 1 (x / b ^ (Ch * M)) := by
  have hb0 : 0 < b := by linarith
  have hpos : ∀ y : ℝ, 0 < b ^ y := fun y => Real.rpow_pos_of_pos hb0 y
  have he : 0 ≤ max (Ch - c) 0 * M := mul_nonneg (le_max_right _ _) hM
  have hbe : 1 ≤ b ^ (max (Ch - c) 0 * M) := Real.one_le_rpow hb he
  have hy : 0 ≤ x / b ^ (Ch * M) := div_nonneg hx (hpos _).le
  have hexp : Ch * M - c * M ≤ max (Ch - c) 0 * M := by
    have e1 : Ch * M - c * M = (Ch - c) * M := by ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hM
  have h1 : x / b ^ (c * M) = b ^ (Ch * M - c * M) * (x / b ^ (Ch * M)) := by
    have n1 := (hpos (c * M)).ne'
    have n2 := (hpos (Ch * M)).ne'
    rw [Real.rpow_sub hb0]
    field_simp
  apply max_le
  · calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ b ^ (max (Ch - c) 0 * M) * max 1 (x / b ^ (Ch * M)) :=
        mul_le_mul hbe (le_max_left _ _) zero_le_one (by linarith)
  · calc x / b ^ (c * M) = b ^ (Ch * M - c * M) * (x / b ^ (Ch * M)) := h1
      _ ≤ b ^ (max (Ch - c) 0 * M) * (x / b ^ (Ch * M)) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hb hexp) hy
      _ ≤ b ^ (max (Ch - c) 0 * M) * max 1 (x / b ^ (Ch * M)) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (hpos _).le

theorem rows_sizeZ_cmp (hrd : 0 < D.host.rdE) {b : ℝ} (hb : 1 ≤ b) (c Ch : ℝ) (Z : GramM D) :
    sizeZ D b c Z ≤ b ^ (max (Ch - c) 0 * (D.R.m : ℝ) ^ 2 * D.R.f * ((D.R.rS : ℝ) + 1)) * sizeZ D b Ch Z := by
  have hb0 : 0 < b := by linarith
  have hM0 : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by positivity
  unfold sizeZ
  calc ∏ τ, ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (absDl D Z l τ / b ^ (c * (D.R.m : ℝ) ^ 2))
      ≤ ∏ τ, ∏ l ∈ Finset.Icc 1 (D.R.rS + 1),
          (b ^ (max (Ch - c) 0 * (D.R.m : ℝ) ^ 2) * max 1 (absDl D Z l τ / b ^ (Ch * (D.R.m : ℝ) ^ 2))) := by
        apply Finset.prod_le_prod
        · intro τ _
          exact Finset.prod_nonneg (fun l _ => le_trans zero_le_one (le_max_left _ _))
        · intro τ _
          apply Finset.prod_le_prod
          · intro l _
            exact le_trans zero_le_one (le_max_left _ _)
          · intro l _
            exact rows_max_cmp hb (rows_absDl_nonneg hrd Z l τ) hM0
    _ = ((b ^ (max (Ch - c) 0 * (D.R.m : ℝ) ^ 2)) ^ (D.R.rS + 1)) ^ Fintype.card D.what₂.Tau *
          ∏ τ, ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (absDl D Z l τ / b ^ (Ch * (D.R.m : ℝ) ^ 2)) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Finset.card_univ,
          Nat.add_sub_cancel]
    _ = b ^ (max (Ch - c) 0 * (D.R.m : ℝ) ^ 2 * D.R.f * ((D.R.rS : ℝ) + 1)) *
          ∏ τ, ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (absDl D Z l τ / b ^ (Ch * (D.R.m : ℝ) ^ 2)) := by
        congr 1
        rw [D.what₂.card_Tau, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
        congr 1
        push_cast
        ring

theorem rows_HHZ_cmp (hrd : 0 < D.host.rdE) {b : ℝ} (hb : 1 ≤ b) (c Ch : ℝ) (Z : GramM D) :
    HHZ D b c Z ≤ b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f +
      4 * (max (Ch - c) 0 * (D.R.m : ℝ) ^ 2 * D.R.f * ((D.R.rS : ℝ) + 1))) * sizeZ D b Ch Z ^ 4 := by
  have hb0 : 0 < b := by linarith
  have h1 := rows_sizeZ_cmp hrd hb c Ch Z
  have h0 : 0 ≤ sizeZ D b c Z := le_trans zero_le_one (rows_one_le_sizeZ b c Z)
  have hpos : 0 ≤ b ^ (c * (D.R.m : ℝ) ^ 2 * D.R.f) := (Real.rpow_pos_of_pos hb0 _).le
  unfold HHZ
  set E := max (Ch - c) 0 * (D.R.m : ℝ) ^ 2 * D.R.f * ((D.R.rS : ℝ) + 1) with hE
  have h4 : sizeZ D b c Z ^ 4 ≤ (b ^ E * sizeZ D b Ch Z) ^ 4 := by
    first
      | exact pow_le_pow_left h0 h1 4
      | exact pow_le_pow_left₀ h0 h1 4
  have e1 : (b ^ (c * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (c * (D.R.m : ℝ)) =
      b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) := by
    rw [← Real.rpow_mul hb0.le]
    congr 1
    ring
  have e2 : (b ^ E) ^ 4 = b ^ (4 * E) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
    congr 1
    push_cast
    ring
  calc (b ^ (c * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (c * (D.R.m : ℝ)) * sizeZ D b c Z ^ 4
      ≤ (b ^ (c * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (c * (D.R.m : ℝ)) * (b ^ E * sizeZ D b Ch Z) ^ 4 :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hpos _)
    _ = b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f + 4 * E) * sizeZ D b Ch Z ^ 4 := by
        rw [e1, mul_pow, e2, Real.rpow_add hb0]
        ring

end Size

section Term

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_sizeV_nonneg (H : ℝ) {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) : 0 ≤ sizeV H z z' γ := by
  unfold sizeV
  exact Finset.prod_nonneg (fun l _ => le_trans zero_le_one (le_max_left _ _))

theorem rows_term_L2dec {C' Cl Cg cb Cu cT CT C0 A Cpr C C2 Ch CV δ δm : ℝ}
    (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hDEC : VanishingOnXAndXPlus.adm26 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δm) (ha : VanishingOnXAndXPlus.PlaneWaveLetters D)
    (hb : VanishingOnXAndXPlus.PlaneWaveIsometry D large₂ C' Cl Cg cb Cu cT CT C0)
    (hp : VanishingOnXAndXPlus.L2LossProductBound D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch)
    (h6 : VanishingOnXAndXPlus.adm6 D large₂ C' Cl Cg cb Cu cT CT C0 δ) (hδ : 0 ≤ δ)
    (hV : VanishingOnXAndXPlus.TermVolumeSmallCellBound D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A CV) (hT : TermPtsTie X Y) (hCh : 0 ≤ Ch)
    (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t) (q : ℕ)
    (hq : (q : ℝ) ≤ Cpr * D.R.k * (D.R.m : ℝ) ^ 2) :
    wordPairGramNorm D u u' (termGramMatrix X t) * aT X t ^ 2 / dimPi (hc := D.hcW) u ≤
      (HHZ D large₂.sc.b CV (termGramMatrix X t) ^ (CV * (D.R.rS : ℝ) ^ 2)) ^ 2 *
        (GamS D large₂ * sizeZ D large₂.sc.b Ch (termGramMatrix X t) ^ (C2 * (D.R.m : ℝ) ^ 2)) *
        sizeZ D large₂.sc.b Ch (termGramMatrix X t) ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1))) * ((1 + δ) * rDD D u') := by
  have hrd := d_rdE_pos hH.1
  have hTT := d_hypTT hH.2.1
  set x : ℝ := 2 * (q : ℝ) / ((D.R.rS : ℝ) + 1) with hx
  have each : ∀ τ, nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ *
      hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ)) / (Module.finrank ℂ (Y.W τ).Wp : ℝ) ≤
      lossV large₂.sc.b C D.R.m (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ) * (tvPr D τ u' ^ D.R.k)⁻¹ *
        sizeV (scalePowQuadraticExponent D large₂ Ch) (Y.W τ).z (Y.W τ).z' (Y.γ t τ) ^ (-x) := by
    intro τ
    obtain ⟨r1, r2, r3⟩ := Y.rel t hG hrel τ
    rw [← d_nV_eq Y hrd t τ]
    exact (hDEC τ u u' hTT Y.θ Y.θ_win (Y.W τ) (Y.goodW τ) (Y.A τ) (Y.goodS τ) (Y.deg_eq τ) (Y.γ t τ) (Y.pt t τ) r1
      (Y.θR t τ) r2 (Y.νR t τ) r3 hH q hq).1
  have nn : ∀ τ, 0 ≤ nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ *
      hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ)) / (Module.finrank ℂ (Y.W τ).Wp : ℝ) := by
    intro τ
    have h1 : 0 ≤ nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ := by
      unfold nV; exact D.R.k_even.pow_nonneg _
    exact div_nonneg (mul_nonneg h1 (d_hsNormSq_nonneg _)) (Nat.cast_nonneg _)
  have P := Finset.prod_le_prod (s := Finset.univ) (fun τ _ => nn τ) (fun τ _ => each τ)
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, d_dims Y hH.1 ha hb,
    Real.finsetProd_rpow _ _ (fun τ _ => rows_sizeV_nonneg _ _ _ _), d_size_eq Y hrd hCh t] at P
  have e : aT X t ^ 2 = Y.volR t ^ 2 * ∏ τ, hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ)) := by
    unfold aT
    rw [Real.sq_sqrt (d_hsNormSq_nonneg _), Y.J_norm t hG hrel]
  have hv : 0 ≤ Y.volR t ^ 2 := by positivity
  have Q := mul_le_mul_of_nonneg_left P hv
  have h2 := hp u u' _ _ _ _ (hT t hG hrel) hH Finset.univ
  rw [d_size_eq Y hrd hCh t] at h2
  have h3 := d_tprod_inv hH.1 h6 hδ u'
  have h4 := hV hH t hG hrel
  have v0 := (Y.volR_pos t).le
  have i0 : 0 ≤ (∏ τ, tvPr D τ u' ^ D.R.k)⁻¹ :=
    inv_nonneg.2 (Finset.prod_nonneg fun τ _ => D.R.k_even.pow_nonneg _)
  have s0 : 0 ≤ sizeZ D large₂.sc.b Ch (ZhatL (X.fl t) (X.fl' t)) := le_trans zero_le_one (rows_one_le_sizeZ _ _ _)
  have L0 : 0 ≤ GamS D large₂ * sizeZ D large₂.sc.b Ch (ZhatL (X.fl t) (X.fl' t)) ^ (C2 * (D.R.m : ℝ) ^ 2) :=
    mul_nonneg (by unfold GamS; exact (Real.exp_pos _).le) (Real.rpow_nonneg s0 _)
  have sx0 : 0 ≤ sizeZ D large₂.sc.b Ch (ZhatL (X.fl t) (X.fl' t)) ^ (-x) := Real.rpow_nonneg s0 _
  have v2 : Y.volR t ^ 2 ≤ (HHZ D large₂.sc.b CV (ZhatL (X.fl t) (X.fl' t)) ^ (CV * (D.R.rS : ℝ) ^ 2)) ^ 2 :=
    pow_le_pow_left₀ v0 h4 2
  have t1 := (mul_le_mul_of_nonneg_right h2 i0).trans (mul_le_mul_of_nonneg_left h3 L0)
  have t2 := mul_le_mul_of_nonneg_right t1 sx0
  have R0 : 0 ≤ (1 + δ) * rDD D u' := i0.trans h3
  have t3 := (mul_le_mul_of_nonneg_left t2 hv).trans
    (mul_le_mul_of_nonneg_right v2 (mul_nonneg (mul_nonneg L0 R0) sx0))
  unfold wordPairGramNorm
  calc _ = Y.volR t ^ 2 * ((∏ τ, nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ) *
        (∏ τ, hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ))) / dimPi (hc := D.hcW) u) := by rw [e]; ring
    _ ≤ _ := Q
    _ ≤ _ := t3
    _ = _ := by ring

end Term

section Term2

theorem rows_prod4 {ι : Type*} [Fintype ι] (a h c e : ι → ℝ) (T : ℝ) (n : ℕ) :
    ∏ τ, (a τ * h τ * c τ ^ n * T / e τ) =
      (∏ τ, a τ) * (∏ τ, h τ) * (∏ τ, c τ) ^ n * T ^ (Fintype.card ι) / ∏ τ, e τ := by
  simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const,
    Finset.card_univ]

theorem rows_prod4' {ι : Type*} [Fintype ι] (l p s : ι → ℝ) (c : ℝ) :
    ∏ τ, (l τ * p τ ^ 2 * c * s τ) = (∏ τ, l τ) * (∏ τ, p τ) ^ 2 * c ^ (Fintype.card ι) * ∏ τ, s τ := by
  simp only [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ]

theorem rows_prod5 {ι : Type*} [Fintype ι] (l p t a s : ι → ℝ) (n : ℕ) :
    ∏ τ, (l τ * p τ ^ 2 * (t τ)⁻¹ * a τ ^ n * s τ) =
      (∏ τ, l τ) * (∏ τ, p τ) ^ 2 * (∏ τ, t τ)⁻¹ * (∏ τ, a τ) ^ n * ∏ τ, s τ := by
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_pow]

theorem rows_foldr_max (l : List ℝ) : 1 ≤ l.foldr max 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact le_trans ih (le_max_right _ _)

theorem loss_nonneg₂ {b : ℝ} (hb : 0 ≤ b) (C : ℝ) (m : ℕ) {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ)
    (γ : MatKR k r) (p : Point ℂ (r + 1)) : 0 ≤ lossP b C m z z' γ p := by
  unfold lossP
  apply Real.rpow_nonneg
  apply mul_nonneg (Real.rpow_nonneg hb _)
  exact le_trans zero_le_one (rows_foldr_max _)

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def rows_Kt (t : D.s.Term u u') : ℝ :=
  ∏ τ, chRatio (Tr D u) (Tr D u') (Y.W τ).z (Y.W τ).z' (Y.γ t τ)

def rows_Mt (C δ : ℝ) (t : D.s.Term u u') : ℝ :=
  ∏ τ, ampMinF D C δ τ u u' (Y.W τ).z (Y.W τ).z' (Y.γ t τ)

theorem rows_term_MINdec {C' Cl Cg cb Cu cT CT C0 A Cpr C C2 Ch CV δm : ℝ}
    (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hDEC : VanishingOnXAndXPlus.adm26 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δm) (ha : VanishingOnXAndXPlus.PlaneWaveLetters D)
    (hb : VanishingOnXAndXPlus.PlaneWaveIsometry D large₂ C' Cl Cg cb Cu cT CT C0)
    (hp : VanishingOnXAndXPlus.L2LossProductBound D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch)
    (hpp : VanishingOnXAndXPlus.AbsoluteLossProductBound D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch)
    (hV : VanishingOnXAndXPlus.TermVolumeSmallCellBound D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A CV) (hT : TermPtsTie X Y) (hCh : 0 ≤ Ch)
    (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t) (q : ℕ)
    (hq : (q : ℝ) ≤ Cpr * D.R.k * (D.R.m : ℝ) ^ 2) :
    wordPairGramNorm D u u' (termGramMatrix X t) * aT X t ^ 2 * rows_Kt Y t ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f) /
        dimPi (hc := D.hcW) u ≤
      (HHZ D large₂.sc.b CV (termGramMatrix X t) ^ (CV * (D.R.rS : ℝ) ^ 2)) ^ 2 *
        (GamS D large₂ * sizeZ D large₂.sc.b Ch (termGramMatrix X t) ^ (C2 * (D.R.m : ℝ) ^ 2)) *
        (Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) *
          sizeZ D large₂.sc.b Ch (termGramMatrix X t) ^ (C2 * (D.R.m : ℝ) ^ 4)) ^ 2 *
        (C / D.R.k) ^ (D.R.k * D.R.f) *
        sizeZ D large₂.sc.b Ch (termGramMatrix X t) ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1))) := by
  have hrd := d_rdE_pos hH.1
  have hTT := d_hypTT hH.2.1
  have hb2 := d_two_le_b D large₂
  set x : ℝ := 2 * (q : ℝ) / ((D.R.rS : ℝ) + 1) with hx
  have each : ∀ τ, nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ *
      hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ)) *
      chRatio (Tr D u) (Tr D u') (Y.W τ).z (Y.W τ).z' (Y.γ t τ) ^ (2 * D.R.k) * (Tr D u ^ D.R.k)⁻¹ /
        (Module.finrank ℂ (Y.W τ).Wp : ℝ) ≤
      lossV large₂.sc.b C D.R.m (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ) *
        lossP large₂.sc.b C D.R.m (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ) ^ 2 * (C / D.R.k) ^ D.R.k *
        sizeV (scalePowQuadraticExponent D large₂ Ch) (Y.W τ).z (Y.W τ).z' (Y.γ t τ) ^ (-x) := by
    intro τ
    obtain ⟨r1, r2, r3⟩ := Y.rel t hG hrel τ
    rw [← d_nV_eq Y hrd t τ]
    exact (hDEC τ u u' hTT Y.θ Y.θ_win (Y.W τ) (Y.goodW τ) (Y.A τ) (Y.goodS τ) (Y.deg_eq τ) (Y.γ t τ) (Y.pt t τ) r1
      (Y.θR t τ) r2 (Y.νR t τ) r3 hH q hq).2.2.2
  have nn : ∀ τ, 0 ≤ nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ *
      hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ)) *
      chRatio (Tr D u) (Tr D u') (Y.W τ).z (Y.W τ).z' (Y.γ t τ) ^ (2 * D.R.k) * (Tr D u ^ D.R.k)⁻¹ /
        (Module.finrank ℂ (Y.W τ).Wp : ℝ) := by
    intro τ
    have h1 : 0 ≤ nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ := by
      unfold nV; exact D.R.k_even.pow_nonneg _
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 (d_hsNormSq_nonneg _)) ((even_two_mul _).pow_nonneg _))
      (inv_nonneg.2 (D.R.k_even.pow_nonneg _))) (Nat.cast_nonneg _)
  have P := Finset.prod_le_prod (s := Finset.univ) (fun τ _ => nn τ) (fun τ _ => each τ)
  rw [rows_prod4, rows_prod4', D.what₂.card_Tau, d_dims Y hH.1 ha hb,
    Real.finsetProd_rpow _ _ (fun τ _ => rows_sizeV_nonneg _ _ _ _), d_size_eq Y hrd hCh t] at P
  have e : aT X t ^ 2 = Y.volR t ^ 2 * ∏ τ, hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ)) := by
    unfold aT
    rw [Real.sq_sqrt (d_hsNormSq_nonneg _), Y.J_norm t hG hrel]
  have hv : 0 ≤ Y.volR t ^ 2 := by positivity
  have Q := mul_le_mul_of_nonneg_left P hv
  have h2 := hp u u' _ _ _ _ (hT t hG hrel) hH Finset.univ
  have h5 := hpp u u' _ _ _ _ (hT t hG hrel) hH Finset.univ
  rw [d_size_eq Y hrd hCh t] at h2 h5
  have h4 := hV hH t hG hrel
  have v0 := (Y.volR_pos t).le
  have s0 : 0 ≤ sizeZ D large₂.sc.b Ch (ZhatL (X.fl t) (X.fl' t)) := le_trans zero_le_one (rows_one_le_sizeZ _ _ _)
  have L0 : 0 ≤ GamS D large₂ * sizeZ D large₂.sc.b Ch (ZhatL (X.fl t) (X.fl' t)) ^ (C2 * (D.R.m : ℝ) ^ 2) :=
    mul_nonneg (by unfold GamS; exact (Real.exp_pos _).le) (Real.rpow_nonneg s0 _)
  have sx0 : 0 ≤ sizeZ D large₂.sc.b Ch (ZhatL (X.fl t) (X.fl' t)) ^ (-x) := Real.rpow_nonneg s0 _
  have pp0 : 0 ≤ ∏ τ, lossP large₂.sc.b C D.R.m (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ) :=
    Finset.prod_nonneg fun τ _ => loss_nonneg₂ (by linarith) _ _ _ _ _ _
  have c0 : 0 ≤ ((C / (D.R.k : ℝ)) ^ D.R.k) ^ D.R.f := pow_nonneg (D.R.k_even.pow_nonneg _) _
  have v2 : Y.volR t ^ 2 ≤ (HHZ D large₂.sc.b CV (ZhatL (X.fl t) (X.fl' t)) ^ (CV * (D.R.rS : ℝ) ^ 2)) ^ 2 :=
    pow_le_pow_left₀ v0 h4 2
  have t1 := (mul_le_mul_of_nonneg_right h2 (sq_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ pp0 h5 2) L0)
  have t2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right t1 c0) sx0
  have t3 := (mul_le_mul_of_nonneg_left t2 hv).trans
    (mul_le_mul_of_nonneg_right v2 (mul_nonneg (mul_nonneg (mul_nonneg L0 (sq_nonneg _)) c0) sx0))
  unfold wordPairGramNorm rows_Kt
  calc _ = Y.volR t ^ 2 * ((∏ τ, nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ) *
        (∏ τ, hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ))) *
        (∏ τ, chRatio (Tr D u) (Tr D u') (Y.W τ).z (Y.W τ).z' (Y.γ t τ)) ^ (2 * D.R.k) *
        ((Tr D u ^ D.R.k)⁻¹) ^ D.R.f / dimPi (hc := D.hcW) u) := by
          rw [e, pow_mul, inv_pow]; ring
    _ ≤ _ := Q
    _ ≤ _ := t3
    _ = _ := by rw [pow_mul]; ring

theorem rows_term_MINIdec {C' Cl Cg cb Cu cT CT C0 A Cpr C C2 Ch CV δ δm : ℝ}
    (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hDEC : VanishingOnXAndXPlus.adm26 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δm) (ha : VanishingOnXAndXPlus.PlaneWaveLetters D)
    (hb : VanishingOnXAndXPlus.PlaneWaveIsometry D large₂ C' Cl Cg cb Cu cT CT C0)
    (hp : VanishingOnXAndXPlus.L2LossProductBound D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch)
    (hpp : VanishingOnXAndXPlus.AbsoluteLossProductBound D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch)
    (h6 : VanishingOnXAndXPlus.adm6 D large₂ C' Cl Cg cb Cu cT CT C0 δ) (hδ : 0 ≤ δ)
    (hV : VanishingOnXAndXPlus.TermVolumeSmallCellBound D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A CV) (hT : TermPtsTie X Y) (hCh : 0 ≤ Ch)
    (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t) (q : ℕ)
    (hq : (q : ℝ) ≤ Cpr * D.R.k * (D.R.m : ℝ) ^ 2) :
    wordPairGramNorm D u u' (termGramMatrix X t) * aT X t ^ 2 / dimPi (hc := D.hcW) u ≤
      (HHZ D large₂.sc.b CV (termGramMatrix X t) ^ (CV * (D.R.rS : ℝ) ^ 2)) ^ 2 *
        (GamS D large₂ * sizeZ D large₂.sc.b Ch (termGramMatrix X t) ^ (C2 * (D.R.m : ℝ) ^ 2)) *
        (Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) *
          sizeZ D large₂.sc.b Ch (termGramMatrix X t) ^ (C2 * (D.R.m : ℝ) ^ 4)) ^ 2 *
        ((1 + δ) * rDD D u') * rows_Mt Y C δm t ^ D.R.k *
        sizeZ D large₂.sc.b Ch (termGramMatrix X t) ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1))) := by
  have hrd := d_rdE_pos hH.1
  have hTT := d_hypTT hH.2.1
  have hb2 := d_two_le_b D large₂
  set x : ℝ := 2 * (q : ℝ) / ((D.R.rS : ℝ) + 1) with hx
  have each : ∀ τ, nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ *
      hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ)) / (Module.finrank ℂ (Y.W τ).Wp : ℝ) ≤
      lossV large₂.sc.b C D.R.m (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ) *
        lossP large₂.sc.b C D.R.m (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ) ^ 2 * (tvPr D τ u' ^ D.R.k)⁻¹ *
        ampMinF D C δm τ u u' (Y.W τ).z (Y.W τ).z' (Y.γ t τ) ^ D.R.k *
        sizeV (scalePowQuadraticExponent D large₂ Ch) (Y.W τ).z (Y.W τ).z' (Y.γ t τ) ^ (-x) := by
    intro τ
    obtain ⟨r1, r2, r3⟩ := Y.rel t hG hrel τ
    rw [← d_nV_eq Y hrd t τ]
    exact (hDEC τ u u' hTT Y.θ Y.θ_win (Y.W τ) (Y.goodW τ) (Y.A τ) (Y.goodS τ) (Y.deg_eq τ) (Y.γ t τ) (Y.pt t τ) r1
      (Y.θR t τ) r2 (Y.νR t τ) r3 hH q hq).2.2.1
  have nn : ∀ τ, 0 ≤ nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ *
      hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ)) / (Module.finrank ℂ (Y.W τ).Wp : ℝ) := by
    intro τ
    have h1 : 0 ≤ nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ := by
      unfold nV; exact D.R.k_even.pow_nonneg _
    exact div_nonneg (mul_nonneg h1 (d_hsNormSq_nonneg _)) (Nat.cast_nonneg _)
  have P := Finset.prod_le_prod (s := Finset.univ) (fun τ _ => nn τ) (fun τ _ => each τ)
  rw [rows_prod5, Finset.prod_div_distrib, Finset.prod_mul_distrib, d_dims Y hH.1 ha hb,
    Real.finsetProd_rpow _ _ (fun τ _ => rows_sizeV_nonneg _ _ _ _), d_size_eq Y hrd hCh t] at P
  have e : aT X t ^ 2 = Y.volR t ^ 2 * ∏ τ, hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ)) := by
    unfold aT
    rw [Real.sq_sqrt (d_hsNormSq_nonneg _), Y.J_norm t hG hrel]
  have hv : 0 ≤ Y.volR t ^ 2 := by positivity
  have Q := mul_le_mul_of_nonneg_left P hv
  have h2 := hp u u' _ _ _ _ (hT t hG hrel) hH Finset.univ
  have h5 := hpp u u' _ _ _ _ (hT t hG hrel) hH Finset.univ
  rw [d_size_eq Y hrd hCh t] at h2 h5
  have h3 := d_tprod_inv hH.1 h6 hδ u'
  have h4 := hV hH t hG hrel
  have v0 := (Y.volR_pos t).le
  have i0 : 0 ≤ (∏ τ, tvPr D τ u' ^ D.R.k)⁻¹ :=
    inv_nonneg.2 (Finset.prod_nonneg fun τ _ => D.R.k_even.pow_nonneg _)
  have R0 : 0 ≤ (1 + δ) * rDD D u' := i0.trans h3
  have s0 : 0 ≤ sizeZ D large₂.sc.b Ch (ZhatL (X.fl t) (X.fl' t)) := le_trans zero_le_one (rows_one_le_sizeZ _ _ _)
  have L0 : 0 ≤ GamS D large₂ * sizeZ D large₂.sc.b Ch (ZhatL (X.fl t) (X.fl' t)) ^ (C2 * (D.R.m : ℝ) ^ 2) :=
    mul_nonneg (by unfold GamS; exact (Real.exp_pos _).le) (Real.rpow_nonneg s0 _)
  have sx0 : 0 ≤ sizeZ D large₂.sc.b Ch (ZhatL (X.fl t) (X.fl' t)) ^ (-x) := Real.rpow_nonneg s0 _
  have pp0 : 0 ≤ ∏ τ, lossP large₂.sc.b C D.R.m (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ) :=
    Finset.prod_nonneg fun τ _ => loss_nonneg₂ (by linarith) _ _ _ _ _ _
  have c0 : 0 ≤ (∏ τ, ampMinF D C δm τ u u' (Y.W τ).z (Y.W τ).z' (Y.γ t τ)) ^ D.R.k := D.R.k_even.pow_nonneg _
  have v2 : Y.volR t ^ 2 ≤ (HHZ D large₂.sc.b CV (ZhatL (X.fl t) (X.fl' t)) ^ (CV * (D.R.rS : ℝ) ^ 2)) ^ 2 :=
    pow_le_pow_left₀ v0 h4 2
  have t1 := (mul_le_mul_of_nonneg_right h2 (sq_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ pp0 h5 2) L0)
  have t1' := (mul_le_mul_of_nonneg_right t1 i0).trans
    (mul_le_mul_of_nonneg_left h3 (mul_nonneg L0 (sq_nonneg _)))
  have t2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right t1' c0) sx0
  have t3 := (mul_le_mul_of_nonneg_left t2 hv).trans
    (mul_le_mul_of_nonneg_right v2 (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg L0 (sq_nonneg _)) R0) c0) sx0))
  unfold wordPairGramNorm rows_Mt
  calc _ = Y.volR t ^ 2 * ((∏ τ, nV D (Tu D u) (Tu D u') (ZhatL (X.fl t) (X.fl' t)) τ) *
        (∏ τ, hsNormSq ((Y.A τ).J (Y.νR t τ) (Y.γ t τ))) / dimPi (hc := D.hcW) u) := by rw [e]; ring
    _ ≤ _ := Q
    _ ≤ _ := t3
    _ = _ := by ring

end Term2

section Dict

open NumberField

theorem rows_card_emb (D : D7) : Fintype.card (D.host.E →+* ℂ) = 2 * D.R.f := by
  rw [NumberField.Embeddings.card]
  have h2 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  rw [h2]
  show 4 * D.R.ord = 2 * (2 * D.R.ord)
  ring

def rows_embSum (D : D7) : D.what₂.Tau ⊕ D.what₂.Tau → (D.host.E →+* ℂ)
  | Sum.inl τ => embS D τ
  | Sum.inr τ => ComplexEmbedding.conjugate (embS D τ)

theorem rows_embSum_bij (D : D7) : Function.Bijective (rows_embSum D) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
  · have key : ∀ τ τ' : D.what₂.Tau, embS D τ ≠ ComplexEmbedding.conjugate (embS D τ') := by
      intro τ τ' h
      unfold embS at h
      rw [LocalModelPeriodLattices.conj_emb] at h
      have h1 := LocalModelPeriodLattices.emb_injective D h
      apply LocalModelPeriodLattices.cc_notMem D.R.toFrame
      have h2 : D.R.cc =
          ((D.eTau τ : D.R.Psi) : D.R.GG) *
            ((D.eTau τ' : D.R.Psi) : D.R.GG)⁻¹ := by
        rw [h1]; group
      rw [h2]
      exact (D.R.Psi).mul_mem (D.eTau τ).2 ((D.R.Psi).inv_mem (D.eTau τ').2)
    have inj : ∀ τ τ' : D.what₂.Tau, embS D τ = embS D τ' → τ = τ' := fun τ τ' h =>
      D.eTau.injective (Subtype.ext (LocalModelPeriodLattices.emb_injective D h))
    rintro (τ | τ) (τ' | τ') h
    · exact congrArg Sum.inl (inj τ τ' h)
    · exact absurd h (key τ τ')
    · exact absurd h.symm (key τ' τ)
    · exact congrArg Sum.inr (inj τ τ' (star_injective h))
  · rw [Fintype.card_sum, D.what₂.card_Tau, rows_card_emb]; ring

theorem rows_placeProd (D : D7) (f : (D.host.E →+* ℂ) → ℝ)
    (hc : ∀ φ, f (ComplexEmbedding.conjugate φ) = f φ) (h0 : ∀ φ, 0 ≤ f φ) :
    placeProd f = ∏ τ, f (embS D τ) := by
  unfold placeProd
  have hb := rows_embSum_bij D
  rw [← (Equiv.ofBijective _ hb).prod_comp, Fintype.prod_sum_type]
  simp only [Equiv.ofBijective_apply, rows_embSum, hc]
  rw [← sq, Real.sqrt_sq (Finset.prod_nonneg (fun τ _ => h0 _))]

theorem rows_frameExp_succ (r : ℕ) : frameExp r (r + 1) = frameExp r r := by
  unfold frameExp
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ r + 1)]
  simp

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_ch_eq (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (τ : D.what₂.Tau) :
    chV (Tr D u) (Tr D u') (Y.W τ).z (Y.W τ).z' (Y.γ t τ) =
      Lat.ch (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) := by
  have h1 := d_norm_Dmin Y hrd t τ (D.R.rS + 1) le_rfl
  have h2 := d_norm_Dmin Y hrd t τ D.R.rS (Nat.le_succ _)
  unfold DminN at h1 h2
  rw [dif_pos (by omega)] at h1 h2
  have h1' : ‖Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Fin.last (D.R.rS + 1))‖ =
      absDl D (ZhatL (X.fl t) (X.fl' t)) (D.R.rS + 1) τ := h1
  unfold chV Lat.ch Formalism.QuantumDeterminants.zeta
  rw [norm_div, map_div₀, norm_div, h1', h2]
  unfold absDl absReal
  rw [rows_frameExp_succ, mul_div_mul_right _ _ (Real.rpow_pos_of_pos hrd _).ne']
  rfl

theorem rows_sh_eq (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (τ : D.what₂.Tau) :
    shV (Tr D u) (Tr D u') (Y.W τ).z (Y.W τ).z' (Y.γ t τ) =
      Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) := by
  unfold shV Lat.sh
  rw [rows_ch_eq Y hrd t τ]

theorem rows_Dr_zero_iff (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (τ : D.what₂.Tau) :
    DminN (Y.W τ).z (Y.W τ).z' (Y.γ t τ) D.R.rS = 0 ↔ Dr (X.fl t) (X.fl' t) = 0 := by
  rw [← norm_eq_zero, d_norm_Dmin Y hrd t τ D.R.rS (Nat.le_succ _)]
  unfold absDl absReal
  rw [mul_eq_zero, norm_eq_zero, map_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (Real.rpow_pos_of_pos hrd _).ne'
  · intro h
    exact Or.inl h

theorem rows_chRatio_eq (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (τ : D.what₂.Tau) :
    chRatio (Tr D u) (Tr D u') (Y.W τ).z (Y.W τ).z' (Y.γ t τ) =
      onePlusChSh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) := by
  unfold chRatio onePlusChSh
  have h := rows_Dr_zero_iff Y hrd t τ
  by_cases h0 : Dr (X.fl t) (X.fl' t) = 0
  · rw [if_pos (h.2 h0), if_pos h0]
  · rw [if_neg (fun h1 => h0 (h.1 h1)), if_neg h0, rows_ch_eq Y hrd t τ, rows_sh_eq Y hrd t τ]

theorem rows_ch_conj (T T' : ℕ) (F : LFlag (hS D) D.R.rS (T : D.host.E)) (F' : LFlag (hS D) D.R.rS (T' : D.host.E))
    (φ : D.host.E →+* ℂ) : Lat.ch T T' F F' (ComplexEmbedding.conjugate φ) = Lat.ch T T' F F' φ := by
  simp [Lat.ch, NumberField.ComplexEmbedding.conjugate_coe_eq]

theorem onePlusChSh_conjugate (T T' : ℕ) (F : LFlag (hS D) D.R.rS (T : D.host.E)) (F' : LFlag (hS D) D.R.rS (T' : D.host.E))
    (φ : D.host.E →+* ℂ) : onePlusChSh T T' F F' (ComplexEmbedding.conjugate φ) = onePlusChSh T T' F F' φ := by
  simp only [onePlusChSh, Lat.sh, rows_ch_conj]

theorem onePlusChSh_nonneg (T T' : ℕ) (F : LFlag (hS D) D.R.rS (T : D.host.E)) (F' : LFlag (hS D) D.R.rS (T' : D.host.E))
    (φ : D.host.E →+* ℂ) : 0 ≤ onePlusChSh T T' F F' φ := by
  unfold onePlusChSh Lat.sh Lat.ch
  split_ifs <;> positivity

theorem rows_Kpair_eq (hrd : 0 < D.host.rdE) (t t' : D.s.Term u u') :
    placeProd (fun τ : D.host.E →+* ℂ => onePlusChSh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) τ *
      onePlusChSh (Tu D u) (Tu D u') (X.fl t) (X.fl' t') τ) = rows_Kt Y t * rows_Kt Y t' := by
  have e : X.fl t = X.fl t' := (Y.fl_eq t).trans (Y.fl_eq t').symm
  rw [rows_placeProd D _ (fun φ => by rw [onePlusChSh_conjugate, onePlusChSh_conjugate])
    (fun φ => mul_nonneg (onePlusChSh_nonneg _ _ _ _ _) (onePlusChSh_nonneg _ _ _ _ _)), Finset.prod_mul_distrib]
  congr 1
  · unfold rows_Kt
    exact Finset.prod_congr rfl fun τ _ => (rows_chRatio_eq Y hrd t τ).symm
  · unfold rows_Kt
    rw [e]
    exact Finset.prod_congr rfl fun τ _ => (rows_chRatio_eq Y hrd t' τ).symm

end Dict

section Pos

theorem rowsT_Tr_pos (D : D7) (w : D.what₂.Word) : 0 < Tr D w := by
  unfold Tr
  first
    | exact_mod_cast (D.mem w).A.T_pos
    | exact_mod_cast (D.mem w).A.hT
    | exact_mod_cast (D.mem w).A.pos
    | exact_mod_cast (D.mem w).A.prime.pos
    | exact_mod_cast (D.mem w).A.hprime.pos
    | exact_mod_cast (D.mem w).A.T_prime.pos
    | exact_mod_cast (D.mem w).A.hT.pos

theorem rowsT_gS_pos {D : D7} {u u' : D.what₂.Word} (h : Cnt.Stand D u u') : (0 : ℝ) < (gS D : ℝ) := by
  unfold Cnt.Stand at h
  obtain ⟨_, _, _, _, _, _, _, hp0, hp1, _⟩ := h
  have h0 : 0 < gS D := Nat.mul_pos hp0.pos hp1.pos
  exact_mod_cast h0

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

include Y

theorem rowsT_Gz_pos (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t)
    (τ : D.what₂.Tau) : 0 < Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ := by
  rw [← d_Gf_eq Y hrd t τ]
  obtain ⟨r1, _, _⟩ := Y.rel t hG hrel τ
  obtain ⟨_, _, hz, hz', hT, hT', _⟩ := Y.goodW τ
  exact lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS _ _ hz hz' (by rw [hT]; exact rowsT_Tr_pos D u)
    (by rw [hT']; exact rowsT_Tr_pos D u') _ r1.1) (Ne.symm r1.2.2)

theorem rowsT_isTermF (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) :
    IsTermF D (X.abelian₂ t) (X.fl t) (X.fl' t) := by
  refine ⟨⟨X.lift' t, X.adm t, ?_⟩, Y.frame_ok t⟩
  rw [← X.G_eq t]
  exact fun h => hG ((map_eq_zero _).1 h)

theorem rowsT_HH_term {C' Cl Cg cb Cu cT CT C0 A CH : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : VanishingOnXAndXPlus.HerrCocycleExtensionClass D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CH) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hrel : D.s.relevant t) :
    NT D u ≤ HHZ D large₂.sc.b CH (termGramMatrix X t) ∧
    ∏ τ, max 1 (Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ) ≤ HHZ D large₂.sc.b CH (termGramMatrix X t) ∧
    ∏ τ, max 1 (Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ)⁻¹ ≤ HHZ D large₂.sc.b CH (termGramMatrix X t) ∧
    ∃ Z : GramM D, ZEquiv (termGramMatrix X t) Z ∧
      ∀ (j : ℕ) (I J : Fin j ↪o Fin (D.R.rS + 1)), (Z.submatrix I J).det ≠ 0 →
        ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z I J τ) ≤ HHZ D large₂.sc.b CH (termGramMatrix X t) ∧
        ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z I J τ)⁻¹ ≤ HHZ D large₂.sc.b CH (termGramMatrix X t) := by
  have key := hHH hH Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero (X.abelian₂ t) (Y.isRows.1 _ (Y.Lam_mem t)) (X.fl' t)
  rw [← Y.fl_eq t] at key
  exact key (rowsT_isTermF Y t hG) (rows_RelZ_term X t hG hrel)

theorem rowsT_shV_pos (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t)
    (τ : D.what₂.Tau) (hD : DminN (Y.W τ).z (Y.W τ).z' (Y.γ t τ) D.R.rS ≠ 0) :
    0 < shV (Tr D u) (Tr D u') (Y.W τ).z (Y.W τ).z' (Y.γ t τ) := by
  have hGp := rowsT_Gz_pos Y hrd t hG hrel τ
  have h1 := d_norm_Dmin Y hrd t τ (D.R.rS + 1) le_rfl
  have h2 := d_norm_Dmin Y hrd t τ D.R.rS (Nat.le_succ _)
  have hD' : 0 < absDl D (termGramMatrix X t) D.R.rS τ := by rw [← h2]; exact norm_pos_iff.2 hD
  unfold DminN at h1 h2
  rw [dif_pos (by omega)] at h1 h2
  have h1' : ‖Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Fin.last (D.R.rS + 1))‖ =
      absDl D (ZhatL (X.fl t) (X.fl' t)) (D.R.rS + 1) τ := h1
  have hT := rowsT_Tr_pos D u
  have hT' := rowsT_Tr_pos D u'
  unfold shV
  apply Real.sqrt_pos.2
  unfold chV Formalism.QuantumDeterminants.zeta
  rw [norm_div, h1', h2, div_pow, div_pow, Real.sq_sqrt (mul_pos hT hT').le, sub_pos, lt_div_iff₀ (mul_pos hT hT'),
    lt_div_iff₀ (by positivity), one_mul]
  unfold Gz at hGp
  have e1 : ((Tu D u : ℕ) : ℝ) = Tr D u := rfl
  have e2 : ((Tu D u' : ℕ) : ℝ) = Tr D u' := rfl
  rw [e1, e2] at hGp
  linarith

theorem rowsT_chRatio_pos (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t)
    (τ : D.what₂.Tau) : 0 < chRatio (Tr D u) (Tr D u') (Y.W τ).z (Y.W τ).z' (Y.γ t τ) := by
  rw [rows_chRatio_eq Y hrd t τ]
  unfold onePlusChSh
  split_ifs with hD
  · exact one_pos
  · have hDm : DminN (Y.W τ).z (Y.W τ).z' (Y.γ t τ) D.R.rS ≠ 0 :=
      fun h0 => hD ((rows_Dr_zero_iff Y hrd t τ).mp h0)
    have hsh := rowsT_shV_pos Y hrd t hG hrel τ hDm
    rw [rows_sh_eq Y hrd t τ] at hsh
    have h0 : 0 ≤ Lat.ch (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) := by
      unfold Lat.ch
      positivity
    exact div_pos (by linarith) hsh

theorem rowsT_Kt_pos (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t) :
    0 < rows_Kt Y t := by
  unfold rows_Kt
  exact Finset.prod_pos (fun τ _ => rowsT_chRatio_pos Y hrd t hG hrel τ)

end Pos

section Small

open NumberField

variable {D : D7}

theorem rowsT_chSh_conj (T T' : ℕ) (F : LFlag (hS D) D.R.rS (T : D.host.E)) (F' : LFlag (hS D) D.R.rS (T' : D.host.E))
    (φ : D.host.E →+* ℂ) : chSh T T' F F' (ComplexEmbedding.conjugate φ) = chSh T T' F F' φ := by
  simp only [chSh, Lat.sh, rows_ch_conj]

theorem rowsT_invSh_conj (T T' : ℕ) (F : LFlag (hS D) D.R.rS (T : D.host.E)) (F' : LFlag (hS D) D.R.rS (T' : D.host.E))
    (φ : D.host.E →+* ℂ) : invSh T T' F F' (ComplexEmbedding.conjugate φ) = invSh T T' F F' φ := by
  simp only [invSh, Lat.sh, rows_ch_conj]

theorem rowsT_ch_nonneg (T T' : ℕ) (F : LFlag (hS D) D.R.rS (T : D.host.E)) (F' : LFlag (hS D) D.R.rS (T' : D.host.E))
    (φ : D.host.E →+* ℂ) : 0 ≤ Lat.ch T T' F F' φ := by
  unfold Lat.ch
  positivity

theorem rowsT_chSh_nonneg (T T' : ℕ) (F : LFlag (hS D) D.R.rS (T : D.host.E)) (F' : LFlag (hS D) D.R.rS (T' : D.host.E))
    (φ : D.host.E →+* ℂ) : 0 ≤ chSh T T' F F' φ := by
  unfold chSh Lat.sh Lat.ch
  split_ifs <;> positivity

theorem rowsT_invSh_nonneg (T T' : ℕ) (F : LFlag (hS D) D.R.rS (T : D.host.E)) (F' : LFlag (hS D) D.R.rS (T' : D.host.E))
    (φ : D.host.E →+* ℂ) : 0 ≤ invSh T T' F F' φ := by
  unfold invSh Lat.sh Lat.ch
  split_ifs <;> first | positivity | exact le_rfl

theorem rowsT_small_one {ι : Type*} [Fintype ι] (s : ι → ℝ) (T T' g : ℝ) (hT : 0 < T) (hT' : 0 < T') (hg : 0 < g)
    (hs : ∀ v, 0 < s v) (h : Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι ≤ ∏ v, 1 / s v) :
    ∏ v, min (T' * s v ^ 2) T' ≤ (4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι := by
  obtain ⟨q, hq⟩ : ∃ q, q = Real.sqrt (T * T' / g ^ 2) := ⟨_, rfl⟩
  rw [← hq] at h
  have hT0 : T ≠ 0 := hT.ne'
  have hg0 : g ≠ 0 := hg.ne'
  have hqpos : 0 < q := by
    rw [hq]
    exact Real.sqrt_pos.mpr (div_pos (mul_pos hT hT') (pow_pos hg 2))
  have hP : 0 < ∏ v, s v := Finset.prod_pos (fun v _ => hs v)
  have hinv : ∏ v, 1 / s v = (∏ v, s v)⁻¹ := by
    simp only [one_div, Finset.prod_inv_distrib]
  rw [hinv] at h
  have h2 : q ^ Fintype.card ι * ∏ v, s v ≤ 1 := by
    calc q ^ Fintype.card ι * ∏ v, s v ≤ (∏ v, s v)⁻¹ * ∏ v, s v :=
          mul_le_mul_of_nonneg_right h hP.le
      _ = 1 := inv_mul_cancel₀ hP.ne'
  have hv : ∀ v, min (T' * s v ^ 2) T' ≤ T' * s v := by
    intro v
    have hsv := hs v
    rcases le_total (s v) 1 with h1 | h1
    · calc min (T' * s v ^ 2) T' ≤ T' * s v ^ 2 := min_le_left _ _
        _ ≤ T' * s v := by
          apply mul_le_mul_of_nonneg_left _ hT'.le
          nlinarith
    · calc min (T' * s v ^ 2) T' ≤ T' := min_le_right _ _
        _ ≤ T' * s v := by nlinarith
  have hr0 : 0 ≤ Real.sqrt (T' / T) * g := mul_nonneg (Real.sqrt_nonneg _) hg.le
  have e1 : T' / T * (T * T' / g ^ 2) = (T' / g) ^ 2 := by
    first
      | (field_simp; ring)
      | field_simp
  have h3 : Real.sqrt (T' / T) * q = T' / g := by
    rw [hq, ← Real.sqrt_mul (div_nonneg hT'.le hT.le), e1, Real.sqrt_sq (div_nonneg hT'.le hg.le)]
  have hrq : Real.sqrt (T' / T) * g * q = T' := by
    calc Real.sqrt (T' / T) * g * q = (Real.sqrt (T' / T) * q) * g := by ring
      _ = T' / g * g := by rw [h3]
      _ = T' := by field_simp
  calc ∏ v, min (T' * s v ^ 2) T' ≤ ∏ v, (T' * s v) :=
        Finset.prod_le_prod (fun v _ => le_min (mul_nonneg hT'.le (sq_nonneg _)) hT'.le)
          (fun v _ => hv v)
    _ = T' ^ Fintype.card ι * ∏ v, s v := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    _ = (Real.sqrt (T' / T) * g * q) ^ Fintype.card ι * ∏ v, s v := by rw [hrq]
    _ = (Real.sqrt (T' / T) * g) ^ Fintype.card ι * (q ^ Fintype.card ι * ∏ v, s v) := by
        rw [mul_pow]; ring
    _ ≤ (Real.sqrt (T' / T) * g) ^ Fintype.card ι * 1 :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg hr0 _)
    _ ≤ (4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι := by
        rw [mul_one]
        have h4 : Real.sqrt (T' / T) * g ≤ 4 * Real.sqrt (T' / T) * g := by nlinarith
        first
          | exact pow_le_pow_left hr0 h4 _
          | exact pow_le_pow_left₀ hr0 h4 _

variable {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

include Y

theorem rowsT_sh_pos (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t)
    (hD : Dr (X.fl t) (X.fl' t) ≠ 0) (τ : D.what₂.Tau) :
    0 < Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) := by
  have hDm : DminN (Y.W τ).z (Y.W τ).z' (Y.γ t τ) D.R.rS ≠ 0 :=
    fun h0 => hD ((rows_Dr_zero_iff Y hrd t τ).mp h0)
  rw [← rows_sh_eq Y hrd t τ]
  exact rowsT_shV_pos Y hrd t hG hrel τ hDm

theorem rowsT_ch_sq (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t)
    (hD : Dr (X.fl t) (X.fl' t) ≠ 0) (τ : D.what₂.Tau) :
    Lat.ch (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) ^ 2 =
      Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) ^ 2 + 1 := by
  have hsh := rowsT_sh_pos Y hrd t hG hrel hD τ
  unfold Lat.sh at hsh ⊢
  have hx : 0 < Lat.ch (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) ^ 2 - 1 := Real.sqrt_pos.mp hsh
  rw [Real.sq_sqrt hx.le]
  ring

theorem rowsT_nu_eq (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t)
    (hD : Dr (X.fl t) (X.fl' t) ≠ 0) (τ : D.what₂.Tau) :
    nuV (Tr D u) (Y.W τ).z (Y.W τ).z' (Y.γ t τ) =
      Tr D u' * Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) ^ 2 := by
  have hc := rowsT_ch_sq Y hrd t hG hrel hD τ
  have e : Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) ^ 2 =
      Lat.ch (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) ^ 2 - 1 := by linarith
  rw [e, ← rows_ch_eq Y hrd t τ]
  have h1 := d_norm_Dmin Y hrd t τ (D.R.rS + 1) le_rfl
  have h2 := d_norm_Dmin Y hrd t τ D.R.rS (Nat.le_succ _)
  have hD' : 0 < absDl D (termGramMatrix X t) D.R.rS τ := by
    rw [← h2]; exact norm_pos_iff.2 fun h => hD ((rows_Dr_zero_iff Y hrd t τ).1 h)
  unfold nuV
  rw [h2, d_Gf_eq Y hrd t τ]
  unfold DminN at h1 h2
  rw [dif_pos (by omega)] at h1 h2
  have h1' : ‖Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Fin.last (D.R.rS + 1))‖ =
      absDl D (ZhatL (X.fl t) (X.fl' t)) (D.R.rS + 1) τ := h1
  have hT := rowsT_Tr_pos D u
  have hT' := rowsT_Tr_pos D u'
  unfold chV Formalism.QuantumDeterminants.zeta Gz
  rw [norm_div, h1', h2, div_pow, div_pow, Real.sq_sqrt (mul_pos hT hT').le]
  have e1 : ((Tu D u : ℕ) : ℝ) = Tr D u := rfl
  have e2 : ((Tu D u' : ℕ) : ℝ) = Tr D u' := rfl
  rw [e1, e2]
  have hy : absDl D (ZhatL (X.fl t) (X.fl' t)) D.R.rS τ ≠ 0 := hD'.ne'
  field_simp

theorem rowsT_small (hS : Cnt.Stand D u u') (hrd : 0 < D.host.rdE) (t t' : D.s.Term u u')
    (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t) (hG' : D.s.Gterm t' ≠ 0) (hrel' : D.s.relevant t')
    (hB : ((Tu D u : ℝ) * (Tu D u' : ℝ) / (gS D : ℝ) ^ 2) ^ ((D.R.f : ℝ) / 2) ≤
      placeProd (fun τ : D.host.E →+* ℂ =>
        chSh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) τ * invSh (Tu D u) (Tu D u') (X.fl t) (X.fl' t') τ +
          invSh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) τ * chSh (Tu D u) (Tu D u') (X.fl t) (X.fl' t') τ)) :
    (Dr (X.fl t) (X.fl' t) ≠ 0 ∧ ∏ τ, min (nuV (Tr D u) (Y.W τ).z (Y.W τ).z' (Y.γ t τ)) (Tr D u') ≤
        (4 * Real.sqrt (Tr D u' / Tr D u) * (gS D : ℝ)) ^ D.R.f) ∨
    (Dr (X.fl t') (X.fl' t') ≠ 0 ∧ ∏ τ, min (nuV (Tr D u) (Y.W τ).z (Y.W τ).z' (Y.γ t' τ)) (Tr D u') ≤
        (4 * Real.sqrt (Tr D u' / Tr D u) * (gS D : ℝ)) ^ D.R.f) := by
  have e : X.fl t = X.fl t' := (Y.fl_eq t).trans (Y.fl_eq t').symm
  have hT := rowsT_Tr_pos D u
  have hT' := rowsT_Tr_pos D u'
  have hg := rowsT_gS_pos hS
  have e1 : ((Tu D u : ℕ) : ℝ) = Tr D u := rfl
  have e2 : ((Tu D u' : ℕ) : ℝ) = Tr D u' := rfl
  rw [rows_placeProd D _
    (fun φ => by rw [rowsT_chSh_conj, rowsT_chSh_conj, rowsT_invSh_conj, rowsT_invSh_conj])
    (fun φ => add_nonneg (mul_nonneg (rowsT_chSh_nonneg _ _ _ _ _) (rowsT_invSh_nonneg _ _ _ _ _))
      (mul_nonneg (rowsT_invSh_nonneg _ _ _ _ _) (rowsT_chSh_nonneg _ _ _ _ _))), e1, e2] at hB
  have hq : (Tr D u * Tr D u' / (gS D : ℝ) ^ 2) ^ ((D.R.f : ℝ) / 2) =
      Real.sqrt (Tr D u * Tr D u' / (gS D : ℝ) ^ 2) ^ Fintype.card D.what₂.Tau := by
    rw [D.what₂.card_Tau, Real.sqrt_eq_rpow, ← Real.rpow_natCast _ D.R.f, ← Real.rpow_mul (by positivity)]
    congr 1; ring
  rw [hq] at hB
  have hpos : 0 < Real.sqrt (Tr D u * Tr D u' / (gS D : ℝ) ^ 2) ^ Fintype.card D.what₂.Tau :=
    pow_pos (Real.sqrt_pos.2 (by positivity)) _
  by_cases h0 : Dr (X.fl t) (X.fl' t) = 0
  · by_cases h0' : Dr (X.fl t') (X.fl' t') = 0
    · exfalso
      have h0'' : Dr (X.fl t) (X.fl' t') = 0 := by rw [e]; exact h0'
      have hne : Nonempty D.what₂.Tau := by
        rw [← Fintype.card_pos_iff, D.what₂.card_Tau]
        simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
        positivity
      obtain ⟨τ0⟩ := hne
      have : ∏ τ : D.what₂.Tau,
          (chSh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) *
              invSh (Tu D u) (Tu D u') (X.fl t) (X.fl' t') (embS D τ) +
            invSh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) *
              chSh (Tu D u) (Tu D u') (X.fl t) (X.fl' t') (embS D τ)) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ τ0) ?_
        unfold invSh
        rw [if_pos h0, if_pos h0'']
        ring
      rw [this] at hB
      linarith
    · right
      refine ⟨h0', ?_⟩
      simp_rw [rowsT_nu_eq Y hrd t' hG' hrel' h0']
      rw [← D.what₂.card_Tau]
      refine rowsT_small_one _ _ _ _ hT hT' hg (fun τ => rowsT_sh_pos Y hrd t' hG' hrel' h0' τ) (hB.trans (le_of_eq ?_))
      refine Finset.prod_congr rfl fun τ _ => ?_
      have h0'' : Dr (X.fl t) (X.fl' t') ≠ 0 := by rw [e]; exact h0'
      rw [← e]
      simp only [chSh, invSh, if_pos h0, if_neg h0'']
      ring
  · by_cases h0' : Dr (X.fl t') (X.fl' t') = 0
    · left
      refine ⟨h0, ?_⟩
      have h0'' : Dr (X.fl t) (X.fl' t') = 0 := by rw [e]; exact h0'
      simp_rw [rowsT_nu_eq Y hrd t hG hrel h0]
      rw [← D.what₂.card_Tau]
      refine rowsT_small_one _ _ _ _ hT hT' hg (fun τ => rowsT_sh_pos Y hrd t hG hrel h0 τ) (hB.trans (le_of_eq ?_))
      refine Finset.prod_congr rfl fun τ _ => ?_
      simp only [chSh, invSh, if_neg h0, if_pos h0'']
      ring
    · have h0'' : Dr (X.fl t) (X.fl' t') ≠ 0 := by rw [e]; exact h0'
      have key := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.smallTerm D.what₂.Tau
        (fun τ => Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ))
        (fun τ => Lat.ch (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ))
        (fun τ => Lat.sh (Tu D u) (Tu D u') (X.fl t') (X.fl' t') (embS D τ))
        (fun τ => Lat.ch (Tu D u) (Tu D u') (X.fl t') (X.fl' t') (embS D τ))
        (Tr D u) (Tr D u') (gS D : ℝ) hT hT' hg
        (fun τ => ⟨rowsT_sh_pos Y hrd t hG hrel h0 τ, rowsT_ch_nonneg _ _ _ _ _, rowsT_ch_sq Y hrd t hG hrel h0 τ⟩)
        (fun τ => ⟨rowsT_sh_pos Y hrd t' hG' hrel' h0' τ, rowsT_ch_nonneg _ _ _ _ _,
          rowsT_ch_sq Y hrd t' hG' hrel' h0' τ⟩)
        (hB.trans (le_of_eq (Finset.prod_congr rfl fun τ _ => by
          have p1 := (rowsT_sh_pos Y hrd t hG hrel h0 τ).ne'
          have p2 := (rowsT_sh_pos Y hrd t' hG' hrel' h0' τ).ne'
          rw [← e] at p2 ⊢
          simp only [chSh, invSh, if_neg h0, if_neg h0'']
          field_simp)))
      rw [D.what₂.card_Tau] at key
      rcases key with k1 | k2
      · left
        refine ⟨h0, ?_⟩
        simp_rw [rowsT_nu_eq Y hrd t hG hrel h0]
        exact k1
      · right
        refine ⟨h0', ?_⟩
        simp_rw [rowsT_nu_eq Y hrd t' hG' hrel' h0']
        exact k2

end Small

section Small2

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rowsT_min_le {ν T' t G κ K : ℝ} (hν : 0 < ν) (ht : 0 < t) (hG : 0 < G) (hκ : 0 < κ)
    (h1 : K ≤ G * (T' * t)) (h2 : 1 ≤ K * κ) : min 1 (ν * t * G * κ) ≤ min ν T' * t * G * κ := by
  rcases le_total ν T' with h | h
  · rw [min_eq_left h]
    exact min_le_right _ _
  · rw [min_eq_right h]
    have h3 : K * κ ≤ G * (T' * t) * κ := mul_le_mul_of_nonneg_right h1 hκ.le
    calc min 1 (ν * t * G * κ) ≤ 1 := min_le_left _ _
      _ ≤ K * κ := h2
      _ ≤ G * (T' * t) * κ := h3
      _ = T' * t * G * κ := by ring

theorem rowsT_Mt_small {C δ C₁ C₂ : ℝ} (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hrel : D.s.relevant t) (hD : Dr (X.fl t) (X.fl' t) ≠ 0) (hC : 1 ≤ C) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hg : 0 < gg D) (hk : 1 ≤ D.R.k)
    (hlow : ∀ τ, (D.R.k : ℝ) ^ (3 * D.R.rS) ≤ gg D ^ (-(D.R.m : ℝ)) * Tcrit D u' τ)
    (hsm : ∏ τ, min (nuV (Tr D u) (Y.W τ).z (Y.W τ).z' (Y.γ t τ)) (Tr D u') ≤ (C₁ * (gS D : ℝ)) ^ D.R.f)
    (hC2 : ∏ τ, tvPr D τ u' ≤ C₂) :
    rows_Mt Y C δ t ≤ C₂ * (C₁ * (gS D : ℝ) * gg D ^ (-(D.R.m : ℝ)) *
      (C / D.R.k) ^ (2 * (D.R.rS : ℝ) * (1 - δ))) ^ D.R.f := by
  have hT' := rowsT_Tr_pos D u'
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  set G : ℝ := gg D ^ (-(D.R.m : ℝ)) with hGd
  have hG0 : 0 < G := Real.rpow_pos_of_pos hg _
  set κ : ℝ := (C / D.R.k) ^ (2 * (D.R.rS : ℝ) * (1 - δ)) with hκd
  have hκ0 : 0 < κ := Real.rpow_pos_of_pos (by positivity) _
  have he0 : 0 ≤ 2 * (D.R.rS : ℝ) * (1 - δ) := by
    have : 0 ≤ 1 - δ := by linarith
    positivity
  have he1 : 2 * (D.R.rS : ℝ) * (1 - δ) ≤ 3 * (D.R.rS : ℝ) := by
    have : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    nlinarith
  have hKκ : 1 ≤ (D.R.k : ℝ) ^ (3 * D.R.rS) * κ := by
    have a1 : ((D.R.k : ℝ)⁻¹) ^ (2 * (D.R.rS : ℝ) * (1 - δ)) ≤ κ := by
      refine Real.rpow_le_rpow (by positivity) ?_ he0
      rw [div_eq_mul_inv]
      exact le_mul_of_one_le_left (by positivity) hC
    have a2 : ((D.R.k : ℝ)⁻¹) ^ (3 * (D.R.rS : ℝ)) ≤ ((D.R.k : ℝ)⁻¹) ^ (2 * (D.R.rS : ℝ) * (1 - δ)) :=
      Real.rpow_le_rpow_of_exponent_ge (by positivity) (inv_le_one_of_one_le₀ hk1) he1
    have a3 : (D.R.k : ℝ) ^ (3 * D.R.rS) * ((D.R.k : ℝ)⁻¹) ^ (3 * (D.R.rS : ℝ)) = 1 := by
      have : (3 * (D.R.rS : ℝ)) = ((3 * D.R.rS : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_natCast, ← mul_pow, mul_inv_cancel₀ hk0.ne', one_pow]
    calc (1 : ℝ) = (D.R.k : ℝ) ^ (3 * D.R.rS) * ((D.R.k : ℝ)⁻¹) ^ (3 * (D.R.rS : ℝ)) := a3.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (a2.trans a1) (by positivity)
  have htv : ∀ τ, 0 < tvPr D τ u' := by
    intro τ
    have h := hlow τ
    have : 0 < G * Tcrit D u' τ := lt_of_lt_of_le (by positivity) h
    have h2 : 0 < Tcrit D u' τ := (pos_iff_pos_of_mul_pos this).1 hG0
    unfold tvPr
    exact div_pos h2 hT'
  have hν : ∀ τ, 0 < nuV (Tr D u) (Y.W τ).z (Y.W τ).z' (Y.γ t τ) := by
    intro τ
    rw [rowsT_nu_eq Y hrd t hG hrel hD τ]
    have := rowsT_sh_pos Y hrd t hG hrel hD τ
    positivity
  have each : ∀ τ, ampMinF D C δ τ u u' (Y.W τ).z (Y.W τ).z' (Y.γ t τ) ≤
      min (nuV (Tr D u) (Y.W τ).z (Y.W τ).z' (Y.γ t τ)) (Tr D u') * tvPr D τ u' * G * κ := by
    intro τ
    unfold ampMinF
    rw [if_neg fun h => hD ((rows_Dr_zero_iff Y hrd t τ).1 h)]
    refine rowsT_min_le (hν τ) (htv τ) hG0 hκ0 ((hlow τ).trans (le_of_eq ?_)) hKκ
    unfold tvPr
    rw [mul_div_cancel₀ _ hT'.ne']
  have nn : ∀ τ, 0 ≤ ampMinF D C δ τ u u' (Y.W τ).z (Y.W τ).z' (Y.γ t τ) := by
    intro τ
    unfold ampMinF
    rw [if_neg fun h => hD ((rows_Dr_zero_iff Y hrd t τ).1 h)]
    exact le_min zero_le_one (by have := hν τ; have := htv τ; positivity)
  have P := Finset.prod_le_prod (s := Finset.univ) (fun τ _ => nn τ) (fun τ _ => each τ)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_univ, D.what₂.card_Tau] at P
  unfold rows_Mt
  refine P.trans ?_
  have t0 : 0 ≤ ∏ τ, tvPr D τ u' := Finset.prod_nonneg fun τ _ => (htv τ).le
  have m0 : 0 ≤ ∏ τ, min (nuV (Tr D u) (Y.W τ).z (Y.W τ).z' (Y.γ t τ)) (Tr D u') :=
    Finset.prod_nonneg fun τ _ => le_min (hν τ).le hT'.le
  have s1 := (mul_le_mul_of_nonneg_right hsm t0).trans (mul_le_mul_of_nonneg_left hC2 (m0.trans hsm))
  have s2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right s1 (pow_pos hG0 D.R.f).le) (pow_pos hκ0 D.R.f).le
  refine s2.trans (le_of_eq ?_)
  rw [mul_pow, mul_pow]
  ring

end Small2

end Formalism.MainNotions.BridgeLemma₂

end
