import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumEigenvectorTwoBlockParahoric

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeSource

variable {k : Type} [Field k] [ValuativeRel k]

def IsIntM {m n : Type} (M : Matrix m n k) : Prop := ∀ i j, M i j ∈ 𝒪[k]

theorem isIntM_mul {l m n : Type} [Fintype m] {M : Matrix l m k} {N : Matrix m n k} (hM : IsIntM M) (hN : IsIntM N) :
    IsIntM (M * N) := fun i j => by
  rw [mul_apply]; exact sum_mem fun a _ => mul_mem (hM i a) (hN a j)

theorem isIntM_sub {m n : Type} {M N : Matrix m n k} (hM : IsIntM M) (hN : IsIntM N) : IsIntM (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)

theorem isIntM_neg {m n : Type} {M : Matrix m n k} (hM : IsIntM M) : IsIntM (-M) :=
  fun i j => neg_mem (hM i j)

theorem isIntM_zero {m n : Type} : IsIntM (0 : Matrix m n k) := fun _ _ => zero_mem _

theorem isIntM_one {n : Type} [DecidableEq n] : IsIntM (1 : Matrix n n k) := fun i j => by
  rw [one_apply]; split_ifs
  exacts [one_mem _, zero_mem _]

theorem isIntM_fromBlocks_iff {a b c d : Type} {P : Matrix a c k} {Q : Matrix a d k} {R : Matrix b c k}
    {S : Matrix b d k} : IsIntM (fromBlocks P Q R S) ↔ IsIntM P ∧ IsIntM Q ∧ IsIntM R ∧ IsIntM S := by
  constructor
  · intro h
    exact ⟨fun i j => h (.inl i) (.inl j), fun i j => h (.inl i) (.inr j), fun i j => h (.inr i) (.inl j),
      fun i j => h (.inr i) (.inr j)⟩
  · rintro ⟨h1, h2, h3, h4⟩ (i | i) (j | j)
    exacts [h1 i j, h2 i j, h3 i j, h4 i j]

theorem isIntM_toBlocks {a b c d : Type} {M : Matrix (a ⊕ b) (c ⊕ d) k} (h : IsIntM M) :
    IsIntM M.toBlocks₁₁ ∧ IsIntM M.toBlocks₁₂ ∧ IsIntM M.toBlocks₂₁ ∧ IsIntM M.toBlocks₂₂ := by
  rw [← fromBlocks_toBlocks M] at h
  exact isIntM_fromBlocks_iff.1 h

theorem isIntM_inv {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n k} (hM : IsIntM M)
    (hd : valuation k M.det = 1) : IsIntM M⁻¹ := fun i j => by
  let M' : Matrix n n 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  have eM : M = (algebraMap 𝒪[k] k).mapMatrix M' := rfl
  have hadj : ∀ i j, M.adjugate i j ∈ 𝒪[k] := fun i j => by
    rw [eM, ← RingHom.map_adjugate]; exact (M'.adjugate i j).2
  rw [inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  show valuation k _ ≤ 1
  rw [map_mul, map_inv₀, hd, inv_one, one_mul]
  exact hadj i j

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_of {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : IsIntM g.val)
    (hd : valuation k g.val.det = 1) : g ∈ KO k n := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨hg, ?_⟩
  rw [Matrix.coe_units_inv]
  exact isIntM_inv hg hd

theorem isIntM_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) : IsIntM g.val :=
  ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg).1

theorem val_det_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) :
    valuation k g.val.det = 1 := by
  have := nabs_det_of_mem_KO hg
  rw [nabs_eq_one_iff] at this
  simpa [GeneralLinearGroup.val_det_apply] using this

end GlobalTheory.ParHeckeSource

namespace GlobalTheory.ParHeckeSource

variable {k : Type} [Field k] [ValuativeRel k]

section Alg
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem fromBlocks_diag_mul {D' c d : Type} [Fintype c] [Fintype d] (S : Matrix D' D k) (W : Matrix (A ⊕ D) (c ⊕ d) k) :
    fromBlocks (1 : Matrix A A k) 0 0 S * W =
      fromBlocks W.toBlocks₁₁ W.toBlocks₁₂ (S * W.toBlocks₂₁) (S * W.toBlocks₂₂) := by
  conv_lhs => rw [← fromBlocks_toBlocks W]
  rw [fromBlocks_multiply]; simp

theorem mul_fromBlocks_diag {r s : Type} [Fintype r] [Fintype s] (W : Matrix (r ⊕ s) (A ⊕ D) k) (T : Matrix D D k) :
    W * fromBlocks (1 : Matrix A A k) 0 0 T =
      fromBlocks W.toBlocks₁₁ (W.toBlocks₁₂ * T) W.toBlocks₂₁ (W.toBlocks₂₂ * T) := by
  conv_lhs => rw [← fromBlocks_toBlocks W]
  rw [fromBlocks_multiply]; simp

theorem fromBlocks_unip_mul {c d : Type} (u : Matrix A D k) (W : Matrix (A ⊕ D) (c ⊕ d) k) :
    fromBlocks (1 : Matrix A A k) u 0 1 * W =
      fromBlocks (W.toBlocks₁₁ + u * W.toBlocks₂₁) (W.toBlocks₁₂ + u * W.toBlocks₂₂) W.toBlocks₂₁ W.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks W]
  rw [fromBlocks_multiply]; simp

variable (A) in

def dg : GL D k →* GL (A ⊕ D) k where
  toFun G := ⟨fromBlocks 1 0 0 G.val, fromBlocks 1 0 0 (G⁻¹).val, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩
  map_one' := by ext1; simp
  map_mul' G H := by ext1; simp [fromBlocks_multiply]

theorem val_dg (G : GL D k) : (dg A G).val = fromBlocks 1 0 0 G.val := rfl

theorem det_dg (G : GL D k) : (dg A G).val.det = G.val.det := by
  rw [val_dg, det_fromBlocks_zero₂₁, det_one, one_mul]

def nmat (u : Matrix A D k) : GL (A ⊕ D) k :=
  ⟨fromBlocks 1 u 0 1, fromBlocks 1 (-u) 0 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩

theorem val_nmat (u : Matrix A D k) : (nmat u).val = fromBlocks 1 u 0 1 := rfl

theorem det_nmat (u : Matrix A D k) : (nmat u).val.det = 1 := by
  rw [val_nmat, det_fromBlocks_zero₂₁, det_one, det_one, one_mul]

end Alg

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem mem_parahoric_of {g : GL (A ⊕ D) k} (hg : IsIntM g.val) (hd : valuation k g.val.det = 1)
    (hl : ∀ i j, valuation k (g.val (.inr i) (.inl j)) < 1) : g ∈ parahoric k A D :=
  mem_parahoric.2 ⟨mem_KO_of hg hd, hl⟩

theorem dg_mem {G : GL D k} (hG : G ∈ KO k D) : dg A G ∈ parahoric k A D := by
  refine mem_parahoric_of ?_ ?_ fun i j => by simp [val_dg]
  · rw [val_dg]; exact isIntM_fromBlocks_iff.2 ⟨isIntM_one, isIntM_zero, isIntM_zero, isIntM_of_mem_KO hG⟩
  · rw [det_dg]; exact val_det_of_mem_KO hG

theorem nmat_mem {u : Matrix A D k} (hu : IsIntM u) : nmat u ∈ parahoric k A D := by
  refine mem_parahoric_of ?_ ?_ fun i j => by simp [val_nmat]
  · rw [val_nmat]; exact isIntM_fromBlocks_iff.2 ⟨isIntM_one, hu, isIntM_zero, isIntM_one⟩
  · rw [det_nmat, map_one]

theorem mtor_eq_dg (ϖ : kˣ) (e : D → ℤ) : mtor (A := A) ϖ e = dg A (torusElt k D ϖ e) := by
  ext1
  rw [mtor, val_torusElt, val_dg, val_torusElt]
  ext (i | i) (j | j) <;> simp [diagonal_apply, one_apply]

end GlobalTheory.ParHeckeSource

namespace GlobalTheory.ParHeckeSource

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem isIntM_of_mem_parahoric {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) : IsIntM j.val :=
  fun i l => GlobalTheory.DatumEigen.int_of_mem hj i l

theorem val_lt_mul {l m n : Type} [Fintype m] {P : Matrix l m k} {c : Matrix m n k} (hP : IsIntM P)
    (hc : ∀ i j, valuation k (c i j) < 1) (i j) : valuation k ((P * c) i j) < 1 := by
  rw [mul_apply]
  exact Valuation.map_sum_lt _ one_ne_zero fun m _ => GlobalTheory.DatumEigen.val_mul_lt (hP _ _) (hc _ _)

theorem inv_torusElt_int {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) :
    IsIntM ((torusElt k D ϖ (-indic s))⁻¹).val := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have e : (torusElt k D ϖ (-indic s))⁻¹ = torusElt k D ϖ (indic s) := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, val_torusElt, val_torusElt, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
    congr 1; funext i
    rw [← zpow_add₀ (Units.ne_zero ϖ)]; simp
  rw [e, val_torusElt]
  intro i j
  rw [diagonal_apply]; split_ifs
  · show valuation k _ ≤ 1
    rw [map_zpow₀]
    exact zpow_le_one₀ (zero_lt_iff.2 (by simp)) hlt.le (by unfold indic; split_ifs <;> norm_num)
  · exact zero_mem _

theorem key_mem {j' : GL (A ⊕ D) k} (hj : j' ∈ parahoric k A D) {E T : GL D k} (hE : E ∈ KO k D)
    (hEj : E.val = j'.val.toBlocks₂₂) (hT : IsIntM (T⁻¹).val) (h12 : IsIntM (j'.val.toBlocks₁₂ * T.val)) :
    (dg A (E * T))⁻¹ * (j' * dg A T) ∈ parahoric k A D := by
  have hJ := isIntM_of_mem_parahoric hj
  obtain ⟨i11, -, i21, -⟩ := isIntM_toBlocks hJ
  have hQ : IsIntM ((E * T)⁻¹).val := by
    rw [_root_.mul_inv_rev, Units.val_mul]
    exact isIntM_mul hT (by rw [Matrix.coe_units_inv]; exact isIntM_inv (isIntM_of_mem_KO hE) (val_det_of_mem_KO hE))
  have hv : ((dg A (E * T))⁻¹ * (j' * dg A T)).val =
      fromBlocks j'.val.toBlocks₁₁ (j'.val.toBlocks₁₂ * T.val) (((E * T)⁻¹).val * j'.val.toBlocks₂₁) 1 := by
    rw [← map_inv, Units.val_mul, Units.val_mul, val_dg, val_dg, mul_fromBlocks_diag, fromBlocks_diag_mul]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    congr 1
    rw [← hEj, ← Matrix.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_assoc, inv_mul_cancel, Units.val_one]
  refine mem_parahoric_of ?_ ?_ ?_
  · rw [hv]; exact isIntM_fromBlocks_iff.2 ⟨i11, h12, isIntM_mul hQ i21, isIntM_one⟩
  · have h1 : valuation k (dg A (E * T)).val.det * valuation k ((dg A (E * T))⁻¹ * (j' * dg A T)).val.det =
        valuation k j'.val.det * valuation k (dg A T).val.det := by
      rw [← map_mul, ← map_mul, ← det_mul, ← det_mul, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left]
    rw [det_dg, det_dg, Units.val_mul, det_mul, map_mul, val_det_of_mem_KO hE, one_mul,
      val_det_of_mem_KO (mem_parahoric.1 hj).1, one_mul] at h1
    have hT0 : valuation k T.val.det ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact (Matrix.isUnit_iff_isUnit_det _ |>.1 T.isUnit).ne_zero
    exact mul_left_cancel₀ hT0 (h1.trans (mul_one _).symm)
  · intro i j
    rw [hv]
    exact val_lt_mul hQ (fun a b => (mem_parahoric.1 hj).2 a b) i j

end GlobalTheory.ParHeckeSource

namespace GlobalTheory.ParHeckeSource

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

open Classical in

def lowerDiagonalBlockAsGL (j : GL (A ⊕ D) k) : GL D k :=
  if h : IsUnit j.val.toBlocks₂₂.det then nonsingInvUnit _ h else 1

theorem lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) : (lowerDiagonalBlockAsGL j).val = j.val.toBlocks₂₂ := by
  have h : IsUnit j.val.toBlocks₂₂.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have := (GlobalTheory.DatumEigen.val_det_blocks hj).2
    rw [h0, map_zero] at this; exact zero_ne_one this
  rw [lowerDiagonalBlockAsGL, dif_pos h]; rfl

theorem lowerDiagonalBlockAsGL_mem_integralGeneralLinear {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) : lowerDiagonalBlockAsGL j ∈ KO k D := by
  refine mem_KO_of ?_ ?_
  · rw [lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hj]; exact (isIntM_toBlocks (isIntM_of_mem_parahoric hj)).2.2.2
  · rw [lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hj]; exact (GlobalTheory.DatumEigen.val_det_blocks hj).2

theorem val_nmat_mul_dg (u : Matrix A D k) (j : GL (A ⊕ D) k) (T : GL D k) :
    (nmat u * j * dg A T).val = fromBlocks (nmat u * j).val.toBlocks₁₁ ((nmat u * j).val.toBlocks₁₂ * T.val)
      j.val.toBlocks₂₁ (j.val.toBlocks₂₂ * T.val) := by
  rw [Units.val_mul (nmat u * j), val_dg, mul_fromBlocks_diag]
  have h : (nmat u * j).val = fromBlocks (j.val.toBlocks₁₁ + u * j.val.toBlocks₂₁)
      (j.val.toBlocks₁₂ + u * j.val.toBlocks₂₂) j.val.toBlocks₂₁ j.val.toBlocks₂₂ := by
    rw [Units.val_mul, val_nmat]; exact fromBlocks_unip_mul u j.val
  have h21 : (nmat u * j).val.toBlocks₂₁ = j.val.toBlocks₂₁ := by rw [h, toBlocks_fromBlocks₂₁]
  have h22 : (nmat u * j).val.toBlocks₂₂ = j.val.toBlocks₂₂ := by rw [h, toBlocks_fromBlocks₂₂]
  rw [h21, h22]

theorem nmat_mul_22 (u : Matrix A D k) (j : GL (A ⊕ D) k) : (nmat u * j).val.toBlocks₂₂ = j.val.toBlocks₂₂ := by
  rw [Units.val_mul, val_nmat, fromBlocks_unip_mul, toBlocks_fromBlocks₂₂]

end GlobalTheory.ParHeckeSource

namespace GlobalTheory.ParHeckeSource

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

open Classical in

theorem card_filter_eq {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D)
    {R : Finset (GL (A ⊕ D) k)} {d : GL (A ⊕ D) k → kˣ} (hR : IsReps (mtor ϖ (-indic s)) R d)
    {RK : Finset (GL D k)} (hRK : IsRepsK (torusElt k D ϖ (-indic s)) RK) {D' : Type}
    {u : Matrix A D k} (hu : IsIntM u) (S : Matrix D' D k) :
    (R.filter fun j => IsIntM (nmat u * j * mtor ϖ (-indic s)).val.toBlocks₁₂ ∧
        IsIntM (S * (nmat u * j * mtor ϖ (-indic s)).val.toBlocks₂₂)).card =
      (RK.filter fun g => IsIntM (S * g.val)).card := by
  rw [mtor_eq_dg] at hR ⊢
  set T := torusElt k D ϖ (-indic s) with hTdef
  have hTi : IsIntM (T⁻¹).val := inv_torusElt_int hϖ s
  have hW12 : ∀ j : GL (A ⊕ D) k, (nmat u * j * dg A T).val.toBlocks₁₂ = (nmat u * j).val.toBlocks₁₂ * T.val :=
    fun j => by rw [val_nmat_mul_dg, toBlocks_fromBlocks₁₂]
  have hW22 : ∀ j : GL (A ⊕ D) k, (nmat u * j * dg A T).val.toBlocks₂₂ = j.val.toBlocks₂₂ * T.val :=
    fun j => by rw [val_nmat_mul_dg, toBlocks_fromBlocks₂₂]
  have hJR : ∀ j ∈ R, j ∈ parahoric k A D := fun j hj => (hR.1 j hj).1
  let pick : GL (A ⊕ D) k → GL D k := fun j =>
    if h : ∃ g, g ∈ RK ∧ g⁻¹ * (lowerDiagonalBlockAsGL j * T) ∈ KO k D then h.choose else 1
  have spec : ∀ j ∈ parahoric k A D, pick j ∈ RK ∧ (pick j)⁻¹ * (lowerDiagonalBlockAsGL j * T) ∈ KO k D := fun j hj => by
    have h := (hRK.2 (lowerDiagonalBlockAsGL j) (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hj)).exists
    simp only [pick, dif_pos h]; exact h.choose_spec
  have uniq : ∀ j ∈ parahoric k A D, ∀ g ∈ RK, g⁻¹ * (lowerDiagonalBlockAsGL j * T) ∈ KO k D → pick j = g :=
    fun j hj g hg h => (hRK.2 (lowerDiagonalBlockAsGL j) (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hj)).unique (spec j hj) ⟨hg, h⟩
  have hY : ∀ j ∈ parahoric k A D, IsIntM (nmat u * j * dg A T).val.toBlocks₁₂ →
      (dg A (lowerDiagonalBlockAsGL j * T))⁻¹ * (nmat u * j * dg A T) ∈ parahoric k A D := fun j hj h12 => by
    have hNj : nmat u * j ∈ parahoric k A D := mul_mem (nmat_mem hu) hj
    have := key_mem hNj (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hj) (by rw [lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hj, nmat_mul_22]) hTi (by rw [← hW12]; exact h12)
    simpa [mul_assoc] using this
  apply Finset.card_nbij pick
  · intro j hj
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter] at hj ⊢
    obtain ⟨hjR, -, h22⟩ := hj
    have hJ := hJR j hjR
    obtain ⟨hg, hK⟩ := spec j hJ
    refine ⟨hg, ?_⟩
    have e : (pick j).val = (lowerDiagonalBlockAsGL j * T).val * (((pick j)⁻¹ * (lowerDiagonalBlockAsGL j * T))⁻¹).val := by
      rw [← Units.val_mul]; congr 1; group
    rw [e, ← Matrix.mul_assoc, Units.val_mul (lowerDiagonalBlockAsGL j), lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hJ, ← hW22]
    exact isIntM_mul h22 (isIntM_of_mem_KO (inv_mem hK))
  · intro j₁ hj₁ j₂ hj₂ he
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hj₁ hj₂
    obtain ⟨h1R, h1a, -⟩ := hj₁
    obtain ⟨h2R, h2a, -⟩ := hj₂
    have hJ1 := hJR _ h1R
    have hJ2 := hJR _ h2R
    obtain ⟨-, hK1⟩ := spec j₁ hJ1
    obtain ⟨-, hK2⟩ := spec j₂ hJ2
    rw [he] at hK1
    have hκ : dg A ((lowerDiagonalBlockAsGL j₁ * T)⁻¹ * (lowerDiagonalBlockAsGL j₂ * T)) ∈ parahoric k A D := by
      apply dg_mem
      have : (lowerDiagonalBlockAsGL j₁ * T)⁻¹ * (lowerDiagonalBlockAsGL j₂ * T) =
          ((pick j₂)⁻¹ * (lowerDiagonalBlockAsGL j₁ * T))⁻¹ * ((pick j₂)⁻¹ * (lowerDiagonalBlockAsGL j₂ * T)) := by group
      rw [this]; exact mul_mem (inv_mem hK1) hK2
    have hm : (j₁ * dg A T)⁻¹ * (j₂ * dg A T) ∈ parahoric k A D := by
      have := mul_mem (mul_mem (inv_mem (hY j₁ hJ1 h1a)) hκ) (hY j₂ hJ2 h2a)
      convert this using 1
      simp only [map_mul, map_inv]; group
    exact (hR.2 j₂ hJ2).unique ⟨h1R, hm⟩ ⟨h2R, by simp⟩
  · intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter] at hg
    obtain ⟨hgR, hSg⟩ := hg
    obtain ⟨κ, hκ, κ', hκ', hgdef⟩ := hRK.1 g hgR
    have hj₀ : (nmat u)⁻¹ * dg A κ ∈ parahoric k A D := mul_mem (inv_mem (nmat_mem hu)) (dg_mem hκ)
    obtain ⟨j, ⟨hjR, hm⟩, -⟩ := hR.2 _ hj₀
    set m' := ((j * dg A T)⁻¹ * ((nmat u)⁻¹ * dg A κ * dg A T))⁻¹ with hm'def
    have hm' : m' ∈ parahoric k A D := inv_mem hm
    have hJ := hJR j hjR
    have eW : nmat u * j * dg A T = dg A (κ * T) * m' := by
      rw [hm'def]; simp only [map_mul, map_inv]; group
    have hv : (nmat u * j * dg A T).val = fromBlocks m'.val.toBlocks₁₁ m'.val.toBlocks₁₂
        ((κ * T).val * m'.val.toBlocks₂₁) ((κ * T).val * m'.val.toBlocks₂₂) := by
      rw [eW, Units.val_mul, val_dg, fromBlocks_diag_mul]
    have hE : lowerDiagonalBlockAsGL j * T = κ * T * lowerDiagonalBlockAsGL m' := by
      ext1
      rw [Units.val_mul, lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hJ, ← hW22, hv, toBlocks_fromBlocks₂₂, Units.val_mul (κ * T), lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hm']
    have hE' : g⁻¹ * (lowerDiagonalBlockAsGL j * T) = κ'⁻¹ * lowerDiagonalBlockAsGL m' := by rw [hE, hgdef]; group
    refine ⟨j, ?_, uniq j hJ g hgR (by rw [hE']; exact mul_mem (inv_mem hκ') (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hm'))⟩
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
    refine ⟨hjR, ?_, ?_⟩
    · rw [hv, toBlocks_fromBlocks₁₂]; exact (isIntM_toBlocks (isIntM_of_mem_parahoric hm')).2.1
    · have e2 : lowerDiagonalBlockAsGL j * T = g * (κ'⁻¹ * lowerDiagonalBlockAsGL m') := by rw [← hE']; group
      rw [hW22, ← lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hJ, ← Units.val_mul, e2, Units.val_mul, ← Matrix.mul_assoc]
      exact isIntM_mul hSg (isIntM_of_mem_KO (mul_mem (inv_mem hκ') (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hm')))

end GlobalTheory.ParHeckeSource

namespace GlobalTheory.ParHeckeSource

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem inSupp_mul_diag {y : Matrix (A ⊕ D') (A ⊕ D) k} (hy : InSupp y) {Q : Matrix D D k} (hQ : IsIntM Q) :
    InSupp (y * (fromBlocks (1 : Matrix A A k) 0 0 Q : Matrix (A ⊕ D) (A ⊕ D) k)) := by
  obtain ⟨h1, h2, h3⟩ := hy
  have hyI : IsIntM y := h1
  obtain ⟨a, b, c, e⟩ := isIntM_toBlocks hyI
  rw [mul_fromBlocks_diag]
  refine ⟨isIntM_fromBlocks_iff.2 ⟨a, isIntM_mul b hQ, c, isIntM_mul e hQ⟩, by simpa using h2, fun i j => ?_⟩
  rw [fromBlocks_apply₂₁]; exact h3 i j

theorem inSupp_iff_int {x : Matrix (A ⊕ D') (A ⊕ D) k} (hx : InSupp x) {j : GL (A ⊕ D) k}
    (hj : j ∈ parahoric k A D) (T : GL D k) :
    InSupp (x * (j * dg A T).val) ↔ IsIntM (x * (j * dg A T).val) := by
  refine ⟨fun h => h.1, fun h => ?_⟩
  obtain ⟨-, h2, h3⟩ := (GlobalTheory.DatumEigen.inSupp_mul hx hj).1
  have e : x * (j * dg A T).val = fromBlocks (x * j.val).toBlocks₁₁ ((x * j.val).toBlocks₁₂ * T.val)
      (x * j.val).toBlocks₂₁ ((x * j.val).toBlocks₂₂ * T.val) := by
    rw [Units.val_mul, ← Matrix.mul_assoc, val_dg, mul_fromBlocks_diag]
  refine ⟨h, ?_, fun i l => ?_⟩
  · rw [e, toBlocks_fromBlocks₁₁]; exact h2
  · rw [e, fromBlocks_apply₂₁]; exact h3 i l

theorem isIntM_mul_iff {x : Matrix (A ⊕ D') (A ⊕ D) k} (hx : InSupp x) {c : Type} (M : Matrix (A ⊕ D) c k) :
    IsIntM (x * M) ↔ IsIntM (fromBlocks (1 : Matrix A A k) 0 0 (schur x) * (nmat (x.toBlocks₁₁⁻¹ * x.toBlocks₁₂)).val * M) := by
  have hxI : IsIntM x := hx.1
  obtain ⟨i11, i12, i21, i22⟩ := isIntM_toBlocks hxI
  have hu : IsUnit x.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hx.det_ne
  have inv11 : IsIntM x.toBlocks₁₁⁻¹ := isIntM_inv i11 hx.2.1
  set L : Matrix (A ⊕ D') (A ⊕ D') k := fromBlocks x.toBlocks₁₁ 0 x.toBlocks₂₁ 1 with hL
  set L' : Matrix (A ⊕ D') (A ⊕ D') k := fromBlocks x.toBlocks₁₁⁻¹ 0 (-(x.toBlocks₂₁ * x.toBlocks₁₁⁻¹)) 1 with hL'
  set Z : Matrix (A ⊕ D') (A ⊕ D) k := fromBlocks (1 : Matrix A A k) 0 0 (schur x) * (nmat (x.toBlocks₁₁⁻¹ * x.toBlocks₁₂)).val
    with hZ
  have e1 : L * Z = x := by
    rw [hL, hZ, val_nmat, fromBlocks_multiply, fromBlocks_multiply]
    conv_rhs => rw [← fromBlocks_toBlocks x]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    congr 1
    · rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
    · rw [schur, ← Matrix.mul_assoc]; abel
  have e2 : L' * L = 1 := by
    rw [hL, hL', fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      nonsing_inv_mul _ hu, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_one, neg_add_cancel, fromBlocks_one]
  have iL : IsIntM L := isIntM_fromBlocks_iff.2 ⟨i11, isIntM_zero, i21, isIntM_one⟩
  have iL' : IsIntM L' := isIntM_fromBlocks_iff.2 ⟨inv11, isIntM_zero, isIntM_neg (isIntM_mul i21 inv11), isIntM_one⟩
  constructor
  · intro h
    have : Z * M = L' * (x * M) := by rw [← e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul]
    rw [this]; exact isIntM_mul iL' h
  · intro h
    rw [← e1, Matrix.mul_assoc]; exact isIntM_mul iL h

end GlobalTheory.ParHeckeSource

namespace GlobalTheory.ParHeckeSource

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem schur_int {x : Matrix (A ⊕ D') (A ⊕ D) k} (hx : InSupp x) : IsIntM (schur x) := by
  obtain ⟨i11, i12, i21, i22⟩ := isIntM_toBlocks (show IsIntM x from hx.1)
  exact isIntM_sub i22 (isIntM_mul (isIntM_mul i21 (isIntM_inv i11 hx.2.1)) i12)

theorem unip_int {x : Matrix (A ⊕ D') (A ⊕ D) k} (hx : InSupp x) : IsIntM (x.toBlocks₁₁⁻¹ * x.toBlocks₁₂) := by
  obtain ⟨i11, i12, -, -⟩ := isIntM_toBlocks (show IsIntM x from hx.1)
  exact isIntM_mul (isIntM_inv i11 hx.2.1) i12

open Classical in

theorem term_eq {ξ : kˣ →* ℂˣ} (hξ : IsTame ξ) {x : Matrix (A ⊕ D') (A ⊕ D) k} (hx : InSupp x) {j : GL (A ⊕ D) k}
    (hj : j ∈ parahoric k A D) {d : kˣ} (hd : (d : k) = j.val.toBlocks₂₂.det) (T : GL D k) :
    ((ξ (GeneralLinearGroup.det j) * (ξ d)⁻¹ : ℂˣ) : ℂ) * datum ξ (x * (j * dg A T).val) =
      if IsIntM (nmat (x.toBlocks₁₁⁻¹ * x.toBlocks₁₂) * j * dg A T).val.toBlocks₁₂ ∧
          IsIntM (schur x * (nmat (x.toBlocks₁₁⁻¹ * x.toBlocks₁₂) * j * dg A T).val.toBlocks₂₂)
        then datum ξ x else 0 := by
  set u := x.toBlocks₁₁⁻¹ * x.toBlocks₁₂ with hudef
  have hu : IsIntM u := unip_int hx
  have hiff : InSupp (x * (j * dg A T).val) ↔ (IsIntM (nmat u * j * dg A T).val.toBlocks₁₂ ∧
      IsIntM (schur x * (nmat u * j * dg A T).val.toBlocks₂₂)) := by
    rw [inSupp_iff_int hx hj, isIntM_mul_iff hx, Matrix.mul_assoc, ← Units.val_mul, ← mul_assoc (nmat _),
      fromBlocks_diag_mul, isIntM_fromBlocks_iff]
    have w11 : IsIntM (nmat u * j * dg A T).val.toBlocks₁₁ := by
      rw [val_nmat_mul_dg, toBlocks_fromBlocks₁₁]
      exact (isIntM_toBlocks (isIntM_of_mem_parahoric (mul_mem (nmat_mem hu) hj))).1
    have w21 : IsIntM (schur x * (nmat u * j * dg A T).val.toBlocks₂₁) := by
      rw [val_nmat_mul_dg, toBlocks_fromBlocks₂₁]
      exact isIntM_mul (schur_int hx) (isIntM_toBlocks (isIntM_of_mem_parahoric hj)).2.2.1
    exact ⟨fun h => ⟨h.2.1, h.2.2.2⟩, fun h => ⟨w11, h.1, w21, h.2⟩⟩
  split_ifs with hP
  · have hs := hiff.2 hP
    obtain ⟨h11, h22⟩ := GlobalTheory.DatumEigen.val_det_blocks hj
    have hc := (GlobalTheory.DatumEigen.inSupp_mul hx hj).2
    have n11 : j.val.toBlocks₁₁.det ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
    set u₁ : kˣ := Units.mk0 _ n11 with hu₁
    have hdv : valuation k (d : k) = 1 := by rw [hd]; exact h22
    have hz11 : (x * (j * dg A T).val).toBlocks₁₁ = (x * j.val).toBlocks₁₁ := by
      rw [Units.val_mul, ← Matrix.mul_assoc, val_dg, mul_fromBlocks_diag, toBlocks_fromBlocks₁₁]
    have t1 : ξ (GeneralLinearGroup.det j) = ξ (u₁ * d) := by
      refine GlobalTheory.DatumEigen.tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_
      rw [Units.val_mul, hd, GeneralLinearGroup.val_det_apply]
      exact GlobalTheory.DatumEigen.det_cong hj
    have t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (Units.mk0 _ hx.det_ne * u₁) := by
      refine GlobalTheory.DatumEigen.tame_eq hξ (by rw [Units.val_mul, map_mul, Units.val_mk0, hx.2.1, one_mul]; exact h11) ?_
      show valuation k ((x * (j * dg A T).val).toBlocks₁₁.det - x.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1
      rw [hz11]
      exact hc
    simp only [datum, dif_pos hs, dif_pos hx]
    rw [t1, t2, ← Units.val_mul]
    congr 1
    simp only [map_mul]
    group
  · have hs : ¬ InSupp (x * (j * dg A T).val) := fun h => hP (hiff.1 h)
    simp only [datum, dif_neg hs, mul_zero]

end GlobalTheory.ParHeckeSource

namespace GlobalTheory.ParHeckeSource

theorem sum_reps_datum_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ∀ (s : Finset D) (R : Finset (GL (A ⊕ D) k)) d, IsReps (mtor ϖ (-indic s)) R d → ∀ RK, IsRepsK (torusElt k D ϖ (-indic s)) RK → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, ∑ j ∈ R, ((ξ (GeneralLinearGroup.det j) * (ξ (d j))⁻¹ : ℂˣ) : ℂ) * datum ξ (x * (j * mtor ϖ (-indic s)).1) = ∑ g ∈ RK, liftS ξ (fun y => intInd (y * g.1)) x := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ hξ s R d hR RK hRK x
  classical
  have hcard := card_filter_eq hϖ s hR hRK (u := x.toBlocks₁₁⁻¹ * x.toBlocks₁₂) (D' := D')
  rw [mtor_eq_dg] at hR hcard ⊢
  set T := torusElt k D ϖ (-indic s) with hTdef
  by_cases hx : InSupp x
  · have hL : ∀ j ∈ R, ((ξ (GeneralLinearGroup.det j) * (ξ (d j))⁻¹ : ℂˣ) : ℂ) * datum ξ (x * (j * dg A T).1) =
        if IsIntM (nmat (x.toBlocks₁₁⁻¹ * x.toBlocks₁₂) * j * dg A T).val.toBlocks₁₂ ∧
          IsIntM (schur x * (nmat (x.toBlocks₁₁⁻¹ * x.toBlocks₁₂) * j * dg A T).val.toBlocks₂₂)
        then datum ξ x else 0 := fun j hj => term_eq hξ hx (hR.1 j hj).1 (hR.1 j hj).2 T
    have hRt : ∀ g ∈ RK, liftS ξ (fun y => intInd (y * g.1)) x =
        if IsIntM (schur x * g.val) then datum ξ x else 0 := by
      intro g _
      simp only [liftS, intInd]
      by_cases h : ∀ i j, (schur x * g.val) i j ∈ 𝒪[k]
      · rw [if_pos h, if_pos (show IsIntM (schur x * g.val) from h), mul_one]
      · rw [if_neg h, if_neg (show ¬ IsIntM (schur x * g.val) from h), mul_zero]
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hRt, ← Finset.sum_filter, ← Finset.sum_filter,
      Finset.sum_const, Finset.sum_const, hcard (unip_int hx) (schur x)]
  · have hL : ∀ j ∈ R, ((ξ (GeneralLinearGroup.det j) * (ξ (d j))⁻¹ : ℂˣ) : ℂ) * datum ξ (x * (j * dg A T).1) = 0 := by
      intro j hjR
      have hj := (hR.1 j hjR).1
      have hs : ¬ InSupp (x * (j * dg A T).val) := fun h => hx (by
        have h1 := inSupp_mul_diag h (inv_torusElt_int hϖ s)
        have e : x * (j * dg A T).val * (fromBlocks (1 : Matrix A A k) 0 0 (T⁻¹).val : Matrix (A ⊕ D) (A ⊕ D) k) =
            x * j.val := by
          rw [← val_dg (A := A), Matrix.mul_assoc, ← Units.val_mul, map_inv, mul_inv_cancel_right]
        rw [e] at h1
        have h2 := (GlobalTheory.DatumEigen.inSupp_mul h1 (inv_mem hj)).1
        rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at h2)
      simp only [datum, dif_neg hs, mul_zero]
    rw [Finset.sum_eq_zero hL, Finset.sum_eq_zero]
    intro g _
    simp only [liftS, datum, dif_neg hx, zero_mul]

end GlobalTheory.ParHeckeSource
