import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormLeOpNormBlockDiagonal

set_option autoImplicit false

noncomputable section

open Set Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.AnForm.M (crd0 crd1 projectiveLineChartAtZero projectiveLineChartAtInfinity)
open GlobalTheory.HermFrame GlobalTheory.CxForm
open scoped ContDiff ComplexOrder ComplexConjugate

namespace GlobalTheory.BcUnique.Deform

section Algebra

variable {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

def dTr (u c : ℂ) (g : Matrix (m ⊕ l) (m ⊕ l) ℂ) : Matrix (m ⊕ l) (m ⊕ l) ℂ :=
  fromBlocks g.toBlocks₁₁ (u • g.toBlocks₁₂) 0 (c • g.toBlocks₂₂)

def dGram (u v : ℂ) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) (Q : Matrix l l ℂ) : Matrix (m ⊕ l) (m ⊕ l) ℂ :=
  fromBlocks H.toBlocks₁₁ (conj u • H.toBlocks₁₂) (u • H.toBlocks₂₁) ((u * conj u) • H.toBlocks₂₂ + (v * conj v) • Q)

omit [DecidableEq m] [DecidableEq l] in

theorem dTr_mul {g g' : Matrix (m ⊕ l) (m ⊕ l) ℂ} (h : g.toBlocks₂₁ = 0) (h' : g'.toBlocks₂₁ = 0)
    {u u' c c' : ℂ} (e : u * c' = u') : dTr u c g * dTr u' c' g' = dTr u' (c * c') (g * g') := by
  conv_rhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks g', h, h']
  subst e
  simp [dTr, fromBlocks_multiply, smul_smul, mul_comm]

omit [Fintype m] [Fintype l] in

theorem dTr_one (u : ℂ) : dTr u 1 (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ) = 1 := by
  ext (i | i) (j | j) <;> simp [dTr, toBlocks₁₁, toBlocks₁₂, toBlocks₂₂, one_apply]

omit [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] in

theorem dTr_one_one {g : Matrix (m ⊕ l) (m ⊕ l) ℂ} (h : g.toBlocks₂₁ = 0) : dTr 1 1 g = g := by
  conv_rhs => rw [← fromBlocks_toBlocks g, h]
  simp [dTr]

omit [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] in

theorem dGram_one_zero (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) (Q : Matrix l l ℂ) : dGram 1 0 H Q = H := by
  simp [dGram, fromBlocks_toBlocks]

omit [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] in

theorem dGram_zero_one (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) (Q : Matrix l l ℂ) :
    dGram 0 1 H Q = fromBlocks (subGram H) 0 0 Q := by
  simp [dGram, subGram]

theorem dGram_eq (u v : ℂ) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) (Q : Matrix l l ℂ) :
    dGram u v H Q = chg (fromBlocks 1 0 0 (u • 1)) H + fromBlocks 0 0 0 ((v * conj v) • Q) := by
  rw [chg_fromBlocks]
  simp [dGram, fromBlocks_add, smul_smul, conjTranspose_smul, mul_comm]

theorem dGram_chg {g : Matrix (m ⊕ l) (m ⊕ l) ℂ} (h : g.toBlocks₂₁ = 0) {u v u' v' c : ℂ} (e : u * c = u')
    (e' : v * c = v') (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) (Q : Matrix l l ℂ) :
    dGram u' v' (chg g H) (chg g.toBlocks₂₂ Q) = chg (dTr u' c g) (dGram u v H Q) := by
  have e₁ : g * fromBlocks 1 0 0 (u' • 1) = fromBlocks 1 0 0 (u • 1) * dTr u' c g := by
    conv_lhs => rw [← fromBlocks_toBlocks g, h]
    simp [dTr, fromBlocks_multiply, smul_smul, ← e, mul_comm]
  have e₂ (A X Y : Matrix (m ⊕ l) (m ⊕ l) ℂ) : chg A (X + Y) = chg A X + chg A Y := by
    simp [chg, Matrix.mul_add, Matrix.add_mul]
  rw [dGram_eq, dGram_eq, e₂, chg_chg, chg_chg, e₁, dTr, chg_fromBlocks _ _ _ (fromBlocks _ _ _ _)]
  subst e'
  simp [chg, smul_smul, conjTranspose_smul, Matrix.mul_assoc, mul_comm, mul_left_comm, mul_assoc]

omit [Fintype l] [DecidableEq l] in

theorem quotGram_dGram (u v : ℂ) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    quotGram (dGram u v H (quotGram H)) = (u * conj u + v * conj v) • quotGram H := by
  simp only [dGram, quotGram, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, Matrix.smul_mul, Matrix.mul_smul, smul_smul, add_smul, smul_sub, mul_comm u]
  abel

theorem posDef_dGram {H : Matrix (m ⊕ l) (m ⊕ l) ℂ} {Q : Matrix l l ℂ} (hH : H.PosDef) (hQ : Q.PosDef) {u v : ℂ}
    (h : u = 1 ∨ v = 1) : (dGram u v H Q).PosDef := by
  by_cases hu : u = 0
  · obtain rfl : v = 1 := h.resolve_left (by simp [hu])
    rw [hu, dGram_zero_one]
    exact posDef_fromBlocks_diag (posDef_subGram hH) hQ
  · rw [dGram_eq]
    refine (posDef_chg ((isUnit_iff_isUnit_det _).2 ?_) hH).add_posSemidef
      (posSemidef_fromBlocks_diag PosSemidef.zero (hQ.posSemidef.smul (mul_star_self_nonneg v)))
    simp [hu]

end Algebra

def dom : Bool → Set (OnePoint ℂ)
  | false => range ((↑) : ℂ → OnePoint ℂ)
  | true => {x | x ≠ ((0 : ℂ) : OnePoint ℂ)}

def hu : Bool → OnePoint ℂ → ℂ
  | false => crd0
  | true => fun _ => 1

def hv : Bool → OnePoint ℂ → ℂ
  | false => fun _ => 1
  | true => crd1

def lam : Bool → Bool → OnePoint ℂ → ℂ
  | false, true => crd1
  | true, false => crd0
  | _, _ => fun _ => 1

theorem crd_mul {x : OnePoint ℂ} (h : x ∈ dom false) (h' : x ∈ dom true) : crd0 x * crd1 x = 1 := by
  obtain ⟨z, rfl⟩ := h
  exact mul_inv_cancel₀ fun e => h' (congrArg _ e)

theorem lam_rules {i j : Bool} {x : OnePoint ℂ} (h : x ∈ dom i) (h' : x ∈ dom j) :
    hu i x * lam i j x = hu j x ∧ hv i x * lam i j x = hv j x ∧
      ∀ k, x ∈ dom k → lam i j x * lam j k x = lam i k x := by
  refine ⟨?_, ?_, fun k h'' => ?_⟩
  · cases i <;> cases j <;> simp [hu, lam]
    exact crd_mul h h'
  · cases i <;> cases j <;> simp [hv, lam]
    rw [mul_comm, crd_mul h' h]
  · cases i <;> cases j <;> cases k <;> simp [lam]
    · exact (mul_comm _ _).trans (crd_mul h h')
    · exact crd_mul h' h

def SphOn (U : Set (OnePoint ℂ)) (f : OnePoint ℂ → ℂ) : Prop :=
  ∀ i, ContDiffOn ℂ ∞ (f ∘ (sphere.e i).symm) ((sphere.e i).target ∩ (sphere.e i).symm ⁻¹' U)

theorem sphOn_one (U : Set (OnePoint ℂ)) : SphOn U fun _ => 1 := fun _ => contDiffOn_const

theorem SphOn.mono {U U' : Set (OnePoint ℂ)} {f : OnePoint ℂ → ℂ} (h : SphOn U f) (e : U' ⊆ U) : SphOn U' f :=
  fun i => (h i).mono fun _ hv => ⟨hv.1, e hv.2⟩

theorem sphOn_crd : SphOn (dom false) crd0 ∧ SphOn (dom true) crd1 := by
  have p : ContDiff ℂ ∞ fun v : V 1 => v 0 := (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ).contDiff
  refine ⟨fun i : Fin 2 => ?_, fun i : Fin 2 => ?_⟩
  · fin_cases i
    · exact p.contDiffOn
    · refine (p.contDiffOn.inv fun v hv => ReciprocityTheory.AnForm.M.projLineChart1_symm_mem_range.1 hv.2).congr fun v _ => ?_
      exact ReciprocityTheory.AnForm.M.finiteCoord_projLineChart1_symm _
  · fin_cases i
    · exact p.contDiffOn.inv fun v hv => ReciprocityTheory.AnForm.M.projLineChart0_symm_ne_zero.1 hv.2
    · exact p.contDiffOn.congr fun v _ => ReciprocityTheory.AnForm.M.infiniteCoord_projLineChart1_symm _

theorem sphOn_all (i j : Bool) : SphOn (dom i) (hu i) ∧ SphOn (dom i) (hv i) ∧ SphOn (dom i ∩ dom j) (lam i j) := by
  refine ⟨?_, ?_, ?_⟩
  · cases i
    exacts [sphOn_crd.1, sphOn_one _]
  · cases i
    exacts [sphOn_one _, sphOn_crd.2]
  · cases i <;> cases j
    exacts [sphOn_one _, sphOn_crd.2.mono inter_subset_right, sphOn_crd.1.mono inter_subset_right, sphOn_one _]

variable {M : Type} [TopologicalSpace M] {n r s : ℕ} {A : HolAtlas M n}

theorem contDiff_proj : ContDiff ℂ ∞ (fun z => ((appendV n 1).symm z).1) ∧
    ContDiff ℂ ∞ (fun z => ((appendV n 1).symm z).2) :=
  ⟨(appendV n 1).symm.contDiff.fst, (appendV n 1).symm.contDiff.snd⟩

theorem holOn_fst {U : Set M} {f : M → ℂ} (h : A.HolOn U f) {W : Set (M × OnePoint ℂ)} (e : ∀ y ∈ W, y.1 ∈ U) :
    (famAtlas A).HolOn W fun y => f y.1 := fun i =>
  (h i.1).comp (contDiff_proj.1.differentiable (by simp)).differentiableOn fun _ hz => ⟨hz.1.1, e _ hz.2⟩

theorem smoothOn_fst {U : Set M} {f : M → ℂ} (h : A.SmoothOn U f) {W : Set (M × OnePoint ℂ)} (e : ∀ y ∈ W, y.1 ∈ U) :
    (famAtlas A).SmoothOn W fun y => f y.1 := fun i =>
  (h i.1).comp (contDiff_proj.1.restrict_scalars ℝ).contDiffOn fun _ hz => ⟨hz.1.1, e _ hz.2⟩

theorem SphOn.snd {U : Set (OnePoint ℂ)} {f : OnePoint ℂ → ℂ} (h : SphOn U f) {W : Set (M × OnePoint ℂ)}
    (e : ∀ y ∈ W, y.2 ∈ U) : ((famAtlas A).HolOn W fun y => f y.2) ∧ ((famAtlas A).SmoothOn W fun y => f y.2) ∧
      (famAtlas A).SmoothOn W fun y => conj (f y.2) := by
  have k (i : (famAtlas A).ι) : ContDiffOn ℂ ∞ ((fun y : M × OnePoint ℂ => f y.2) ∘ ((famAtlas A).e i).symm)
      (((famAtlas A).e i).target ∩ ((famAtlas A).e i).symm ⁻¹' W) :=
    (h i.2).comp contDiff_proj.2.contDiffOn fun _ hz => ⟨hz.1.2, e _ hz.2⟩
  exact ⟨fun i => (k i).differentiableOn (by simp), fun i => (k i).restrict_scalars ℝ,
    fun i => Complex.conjCLE.contDiff.comp_contDiffOn ((k i).restrict_scalars ℝ)⟩

theorem g_blocks (T : HermSeq A r s) {a b c : T.κ} {y : M} (ha : y ∈ T.U a) (hb : y ∈ T.U b) (hc : y ∈ T.U c)
    {u u' k k' : ℂ} (e : u * k' = u') : dTr u k (T.g a b y) * dTr u' k' (T.g b c y) = dTr u' (k * k') (T.g a c y) := by
  rw [dTr_mul (T.tri a b y ⟨ha, hb⟩) (T.tri b c y ⟨hb, hc⟩) e, T.g_mul a b c y ⟨⟨ha, hb⟩, hc⟩]

theorem holOn_diag (T : HermSeq A r s) (a b : T.κ) (i j : Fin r ⊕ Fin s) :
    A.HolOn (T.U a ∩ T.U b) fun y => dTr 0 1 (T.g a b y) i j := by
  rcases i with i | i <;> rcases j with j | j
  · exact T.holo a b (.inl i) (.inl j)
  · exact fun c => (differentiableOn_const 0).congr fun v _ => zero_mul _
  · exact fun c => differentiableOn_const 0
  · exact fun c => (T.holo a b (.inr i) (.inr j) c).congr fun v _ => one_mul _

theorem diag_trans (T : HermSeq A r s) {a b : T.κ} {y : M} (h : y ∈ T.U a ∩ T.U b) :
    fromBlocks (T.sub b y) 0 0 (T.quot b y) =
      chg (dTr 0 1 (T.g a b y)) (fromBlocks (T.sub a y) 0 0 (T.quot a y)) := by
  rw [dTr, chg_fromBlocks, (T.trans a b y h).1, (T.trans a b y h).2.2]
  simp [chg, Matrix.mul_assoc]

def graded (T : HermSeq A r s) : HermSeq A r s where
  κ := T.κ
  U := T.U
  isOpen := T.isOpen
  cover := T.cover
  g a b y := dTr 0 1 (T.g a b y)
  holo := holOn_diag T
  tri _ _ _ _ := toBlocks_fromBlocks₂₁ _ _ _ _
  g_self a y hy := by rw [T.g_self a y hy, dTr_one]
  g_mul a b c y hy := by rw [g_blocks T hy.1.1 hy.1.2 hy.2 (zero_mul 1), one_mul]
  sub := T.sub
  mid a y := fromBlocks (T.sub a y) 0 0 (T.quot a y)
  quot := T.quot
  smooth a := by
    refine ⟨(T.smooth a).1, ?_, (T.smooth a).2.2⟩
    rintro (i | i) (j | j)
    exacts [(T.smooth a).1 i j, fun _ => contDiffOn_const (c := 0), fun _ => contDiffOn_const (c := 0),
      (T.smooth a).2.2 i j]
  posDef a y hy := ⟨(T.posDef a y hy).1, posDef_fromBlocks_diag (T.posDef a y hy).1 (T.posDef a y hy).2.2,
    (T.posDef a y hy).2.2⟩
  trans a b y hy := ⟨(T.trans a b y hy).1, diag_trans T hy, by simpa [dTr] using (T.trans a b y hy).2.2⟩

theorem isSplit_graded (T : HermSeq A r s) : (graded T).IsSplit := fun _ =>
  ⟨fun _ => 0, fun _ _ _ => differentiableOn_const 0, fun _ _ => by rw [fromBlocks_one, chg_one]; rfl⟩

def family (T : HermSeq A r s) : HermSeq (famAtlas A) r s where
  κ := T.κ × Bool
  U a := T.U a.1 ×ˢ dom a.2
  isOpen a := (T.isOpen a.1).prod (by
    rcases a with ⟨_, _ | _⟩
    exacts [OnePoint.isOpen_range_coe, isOpen_compl_singleton])
  cover y := by
    obtain ⟨a, ha⟩ := T.cover y.1
    by_cases h : y.2 = ((0 : ℂ) : OnePoint ℂ)
    exacts [⟨(a, false), ha, 0, h.symm⟩, ⟨(a, true), ha, h⟩]
  g a b y := dTr (hu b.2 y.2) (lam a.2 b.2 y.2) (T.g a.1 b.1 y.1)
  holo a b := by
    have h (i j) : (famAtlas A).HolOn (T.U a.1 ×ˢ dom a.2 ∩ T.U b.1 ×ˢ dom b.2) fun y => T.g a.1 b.1 y.1 i j :=
      holOn_fst (T.holo a.1 b.1 i j) fun y hy => ⟨hy.1.1, hy.2.1⟩
    have h₁ := ((sphOn_all b.2 b.2).1.snd (A := A) (W := T.U a.1 ×ˢ dom a.2 ∩ T.U b.1 ×ˢ dom b.2)
      fun y hy => hy.2.2).1
    have h₂ := ((sphOn_all a.2 b.2).2.2.snd (A := A) (W := T.U a.1 ×ˢ dom a.2 ∩ T.U b.1 ×ˢ dom b.2)
      fun y hy => ⟨hy.1.2, hy.2.2⟩).1
    rintro (i | i) (j | j)
    exacts [h (.inl i) (.inl j), fun c => (h₁ c).mul (h (.inl i) (.inr j) c), fun c => differentiableOn_const 0,
      fun c => (h₂ c).mul (h (.inr i) (.inr j) c)]
  tri _ _ _ _ := toBlocks_fromBlocks₂₁ _ _ _ _
  g_self a y hy := by
    have : lam a.2 a.2 y.2 = 1 := by cases a.2 <;> rfl
    rw [T.g_self a.1 y.1 hy.1, this, dTr_one]
  g_mul a b c y hy := by
    rw [g_blocks T hy.1.1.1 hy.1.2.1 hy.2.1 (lam_rules hy.1.2.2 hy.2.2).1, (lam_rules hy.1.1.2 hy.1.2.2).2.2 _ hy.2.2]
  sub a y := T.sub a.1 y.1
  mid a y := dGram (hu a.2 y.2) (hv a.2 y.2) (T.mid a.1 y.1) (T.quot a.1 y.1)
  quot a y := (hu a.2 y.2 * conj (hu a.2 y.2) + hv a.2 y.2 * conj (hv a.2 y.2)) • T.quot a.1 y.1
  smooth a := by
    have e : ∀ y ∈ T.U a.1 ×ˢ dom a.2, y.1 ∈ T.U a.1 := fun y hy => hy.1
    have h (i j) := smoothOn_fst ((T.smooth a.1).2.1 i j) e
    have hq (i j) := smoothOn_fst ((T.smooth a.1).2.2 i j) e
    have h₁ := ((sphOn_all a.2 a.2).1.snd (A := A) (W := T.U a.1 ×ˢ dom a.2) fun y hy => hy.2).2
    have h₂ := ((sphOn_all a.2 a.2).2.1.snd (A := A) (W := T.U a.1 ×ˢ dom a.2) fun y hy => hy.2).2
    refine ⟨fun i j => smoothOn_fst ((T.smooth a.1).1 i j) e, ?_,
      fun i j c => (((h₁.1 c).mul (h₁.2 c)).add ((h₂.1 c).mul (h₂.2 c))).mul (hq i j c)⟩
    rintro (i | i) (j | j)
    exacts [h (.inl i) (.inl j), fun c => (h₁.2 c).mul (h (.inl i) (.inr j) c),
      fun c => (h₁.1 c).mul (h (.inr i) (.inl j) c),
      fun c => (((h₁.1 c).mul (h₁.2 c)).mul (h (.inr i) (.inr j) c)).add (((h₂.1 c).mul (h₂.2 c)).mul (hq i j c))]
  posDef a y hy := by
    obtain ⟨p₁, p₂, p₃⟩ := T.posDef a.1 y.1 hy.1
    have h : hu a.2 y.2 = 1 ∨ hv a.2 y.2 = 1 := by
      cases a.2
      exacts [.inr rfl, .inl rfl]
    refine ⟨p₁, posDef_dGram p₂ p₃ h, p₃.smul ?_⟩
    rcases h with h | h <;> rw [h, map_one, mul_one]
    exacts [add_pos_of_pos_of_nonneg one_pos (mul_star_self_nonneg _),
      add_pos_of_nonneg_of_pos (mul_star_self_nonneg _) one_pos]
  trans a b y hy := by
    obtain ⟨p₁, p₂, p₃⟩ := T.trans a.1 b.1 y.1 ⟨hy.1.1, hy.2.1⟩
    obtain ⟨q₁, q₂, -⟩ := lam_rules hy.1.2 hy.2.2
    refine ⟨p₁, ?_, ?_⟩
    · rw [p₂, p₃, dGram_chg (T.tri a.1 b.1 y.1 ⟨hy.1.1, hy.2.1⟩) q₁ q₂]
    · rw [p₃, dTr, toBlocks_fromBlocks₂₂, ← q₁, ← q₂]
      simp only [chg, transpose_smul, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_mul,
        RCLike.star_def]
      congr 1
      ring

theorem isInduced_family {T : HermSeq A r s} (h : IsInduced T) : IsInduced (family T) := fun a y hy => by
  obtain ⟨p₁, p₂⟩ := h a.1 y.1 hy.1
  refine ⟨p₁, ?_⟩
  change _ • T.quot a.1 y.1 = quotGram (dGram _ _ _ (T.quot a.1 y.1))
  rw [p₂, quotGram_dGram]

theorem isPull_infty (T : HermSeq A r s) : T.IsPull (family T) (fib OnePoint.infty) := by
  refine ⟨fun a b => T.g a.1 b, fun a b i j c => (T.holo a.1 b i j c).mono fun v hv => ⟨hv.1, hv.2.1.1, hv.2.2⟩, ?_⟩
  have k (i : Bool) (h : OnePoint.infty ∈ dom i) : i = true := by
    cases i
    exacts [(OnePoint.infty_notMem_range_coe h).elim, rfl]
  rintro ⟨a, i⟩ b y ⟨ha, hi⟩ hb
  obtain rfl := k i hi
  obtain ⟨p₁, p₂, p₃⟩ := T.trans a b y ⟨ha, hb⟩
  refine ⟨T.tri a b y ⟨ha, hb⟩, ?_, fun b' h => T.g_mul a b b' y ⟨⟨ha, hb⟩, h⟩, p₁, ?_, ?_⟩
  · rintro ⟨a', i⟩ ⟨ha', hi⟩
    obtain rfl := k i hi
    change dTr 1 1 (T.g a' a y) * _ = _
    rw [dTr_one_one (T.tri a' a y ⟨ha', ha⟩), T.g_mul a' a b y ⟨⟨ha', ha⟩, hb⟩]
  · change _ = chg _ (dGram 1 0 _ _)
    rw [dGram_one_zero]
    exact p₂
  · change _ = chg _ ((1 * conj 1 + 0 * conj 0 : ℂ) • T.quot a y)
    simpa using p₃

theorem isPull_zero {T : HermSeq A r s} (hT : IsInduced T) :
    (graded T).IsPull (family T) (fib ((0 : ℂ) : OnePoint ℂ)) := by
  refine ⟨fun a b => (graded T).g a.1 b,
    fun a b i j c => ((graded T).holo a.1 b i j c).mono fun v hv => ⟨hv.1, hv.2.1.1, hv.2.2⟩, ?_⟩
  have k (i : Bool) (h : ((0 : ℂ) : OnePoint ℂ) ∈ dom i) : i = false := by
    cases i
    exacts [rfl, (h rfl).elim]
  rintro ⟨a, i⟩ b y ⟨ha, hi⟩ hb
  obtain rfl := k i hi
  obtain ⟨p₁, p₂, p₃⟩ := (graded T).trans a b y ⟨ha, hb⟩
  refine ⟨(graded T).tri a b y ⟨ha, hb⟩, ?_, fun b' h => (graded T).g_mul a b b' y ⟨⟨ha, hb⟩, h⟩, p₁, ?_, ?_⟩
  · rintro ⟨a', i⟩ ⟨ha', hi⟩
    obtain rfl := k i hi
    exact (graded T).g_mul a' a b y ⟨⟨ha', ha⟩, hb⟩
  · change _ = chg _ (dGram 0 1 (T.mid a y) (T.quot a y))
    rw [dGram_zero_one, ← (hT a y ha).1]
    exact p₂
  · change _ = chg _ ((0 * conj 0 + 1 * conj 1 : ℂ) • T.quot a y)
    rw [zero_mul, zero_add, map_one, mul_one, one_smul]
    exact p₃

end GlobalTheory.BcUnique.Deform

namespace GlobalTheory.BcUnique

theorem exists_deformation {M : Type} [TopologicalSpace M] {n r s : ℕ} (A : HolAtlas M n) (T : HermSeq A r s)
    (h : IsInduced T) : ∃ (T' : HermSeq (famAtlas A) r s) (T₀ : HermSeq A r s), T₀.IsSplit ∧
      T.IsPull T' (fib OnePoint.infty) ∧ T₀.IsPull T' (fib ((0 : ℂ) : OnePoint ℂ)) ∧ IsInduced T' :=
  ⟨Deform.family T, Deform.graded T, Deform.isSplit_graded T, Deform.isPull_infty T, Deform.isPull_zero h,
    Deform.isInduced_family h⟩

end GlobalTheory.BcUnique
