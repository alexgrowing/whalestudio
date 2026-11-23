import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingPiProdSplit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat

section Local
variable {k : Type} [Field k] {n n' : Type} {c : ℕ}

def colIx (hc : Even c) (r : n) : KeptVar n c n' := ⟨(.inl r, .inr ⟨c / 2, by omega⟩), hc, rfl⟩

def rowIx (hc : Odd c) (s : n') : KeptVar n c n' := ⟨(.inr ⟨c / 2, by have := hc.pos; omega⟩, .inl s), hc, rfl⟩

def colEquiv (hc : Even c) : n ≃ KeptVar n c n' where
  toFun := colIx hc
  invFun
    | ⟨(.inl r, _), _⟩ => r
    | ⟨(.inr _, .inl _), h⟩ => absurd hc (Nat.not_even_iff_odd.2 h.1)
    | ⟨(.inr _, .inr _), h⟩ => h.elim
  left_inv r := rfl
  right_inv := by
    rintro ⟨⟨r | l, s | i⟩, h⟩
    · exact h.elim
    · obtain ⟨_, hi⟩ := h
      obtain ⟨i, _⟩ := i
      obtain rfl : i = c / 2 := hi
      rfl
    · exact absurd hc (Nat.not_even_iff_odd.2 h.1)
    · exact h.elim

def rowEquiv (hc : Odd c) : n' ≃ KeptVar n c n' where
  toFun := rowIx hc
  invFun
    | ⟨(.inr _, .inl s), _⟩ => s
    | ⟨(.inl _, .inr _), h⟩ => absurd h.1 (Nat.not_even_iff_odd.2 hc)
    | ⟨(.inl _, .inl _), h⟩ => h.elim
    | ⟨(.inr _, .inr _), h⟩ => h.elim
  left_inv s := rfl
  right_inv := by
    rintro ⟨⟨r | l, s | i⟩, h⟩
    · exact h.elim
    · exact absurd h.1 (Nat.not_even_iff_odd.2 hc)
    · obtain ⟨_, hl⟩ := h
      obtain ⟨l, _⟩ := l
      obtain rfl : l = c / 2 := hl
      rfl
    · exact h.elim

theorem keptPt_eq_colAt (hc : Even c) (w : KeptVar n c n' → k) :
    keptPt w = colAt n' c (c / 2 + 1) fun r => w (colIx hc r) := by
  classical
  ext (r | l) (s | i)
  · simp [keptPt, colAt, Kept]
  · by_cases hi : i.val = c / 2
    · obtain ⟨i, hi'⟩ := i
      obtain rfl : i = c / 2 := hi
      simp [keptPt, colAt, Kept, hc, colIx]
    · simp [keptPt, colAt, Kept, hi]
  · simp [keptPt, colAt, Kept, Nat.not_odd_iff_even.2 hc]
  · simp [keptPt, colAt, Kept]

theorem keptPt_eq_rowAt (hc : Odd c) (w : KeptVar n c n' → k) :
    keptPt w = rowAt n c (c / 2 + 1) fun s => w (rowIx hc s) := by
  classical
  ext (r | l) (s | i)
  · simp [keptPt, rowAt, Kept]
  · simp [keptPt, rowAt, Kept, Nat.not_even_iff_odd.2 hc]
  · by_cases hl : l.val = c / 2
    · obtain ⟨l, hl'⟩ := l
      obtain rfl : l = c / 2 := hl
      simp [keptPt, rowAt, Kept, hc, rowIx]
    · simp [keptPt, rowAt, Kept, hl]
  · simp [keptPt, rowAt, Kept]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar k Circle) (ν : Measure k)

theorem flatStep_eq_flCol (hc : Even c) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k)
    (w : KeptVar n c n' → k) :
    flatStep ψ ν Φ x₀ w = flCol ψ ν (c / 2 + 1) Φ (fromCols x₀ (Matrix.of fun r _ => w (colIx hc r))) := by
  simp only [flatStep, flCol, keptPt_eq_colAt hc, toCols₁_fromCols, fromCols_apply_inr, of_apply]

theorem flatStep_eq_flRow (hc : Odd c) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k)
    (w : KeptVar n c n' → k) :
    flatStep ψ ν Φ x₀ w = flRow ψ ν (c / 2 + 1) Φ (fromRows x₀ (Matrix.of fun _ s => w (rowIx hc s))) := by
  simp only [flatStep, flRow, keptPt_eq_rowAt hc, toRows₁_fromRows]
  rfl

end Local

section Abstract

def consEquiv {n : ℕ} (E : Fin (n + 1) → Type) [∀ j, MeasurableSpace (E j)] :
    (E 0 × ∀ j : Fin n, E j.succ) ≃ᵐ ∀ j, E j := (MeasurableEquiv.piFinSuccAbove E 0).symm

theorem consEquiv_apply {n : ℕ} (E : Fin (n + 1) → Type) [∀ j, MeasurableSpace (E j)]
    (p : E 0 × ∀ j : Fin n, E j.succ) : consEquiv E p = Fin.cons p.1 p.2 :=
  (Fin.insertNth_zero p.1 p.2).trans rfl

theorem measurePreserving_consEquiv {n : ℕ} {E : Fin (n + 1) → Type} [∀ j, MeasurableSpace (E j)]
    (μ : ∀ j, Measure (E j)) [∀ j, SigmaFinite (μ j)] :
    MeasurePreserving (consEquiv E) ((μ 0).prod (Measure.pi fun j => μ j.succ)) (Measure.pi μ) :=
  (measurePreserving_piFinSuccAbove μ 0).symm

theorem integral_pi_succ_succ {n : ℕ} {E : Fin (n + 2) → Type} [∀ j, MeasurableSpace (E j)] (μ : ∀ j, Measure (E j))
    [∀ j, SigmaFinite (μ j)] (F : (∀ j, E j) → ℂ) :
    ∫ w, F w ∂(Measure.pi μ) =
      ∫ p : (E 0 × E (Fin.succ 0)) × (∀ j : Fin n, E j.succ.succ), F (Fin.cons p.1.1 (Fin.cons p.1.2 p.2))
        ∂(((μ 0).prod (μ (Fin.succ 0))).prod (Measure.pi fun j => μ j.succ.succ)) := by
  have h : MeasurePreserving (MeasurableEquiv.prodAssoc.trans (((MeasurableEquiv.refl (E 0)).prodCongr
      (consEquiv fun j : Fin (n + 1) => E j.succ)).trans (consEquiv E)))
      (((μ 0).prod (μ (Fin.succ 0))).prod (Measure.pi fun j : Fin n => μ j.succ.succ)) (Measure.pi μ) :=
    (measurePreserving_consEquiv μ).comp (((MeasurePreserving.id (μ 0)).prod
      (measurePreserving_consEquiv fun j : Fin (n + 1) => μ j.succ)).comp (measurePreserving_prodAssoc _ _ _))
  rw [← h.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show F (consEquiv E (p.1.1, consEquiv (fun j : Fin (n + 1) => E j.succ) (p.1.2, p.2))) = _
  simp only [consEquiv_apply]

theorem prod_even_succ_succ (n : ℕ) (f : Fin (n + 2) → ℂ) : (∏ j : Fin (n + 2), if Even j.1 then f j else 1) =
    f 0 * ∏ j : Fin n, if Even j.1 then f j.succ.succ else 1 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [Nat.even_add_one]

theorem integral_pi_pairs (q : ℕ) : ∀ (E : ℕ → Type) [∀ j, MeasurableSpace (E j)] (μ : ∀ j, Measure (E j))
    [∀ j, SigmaFinite (μ j)] (H : ∀ j : Fin (2 * q), E j → E (j + 1) → ℂ) (L : E (2 * q) → ℂ),
    ∫ w : ∀ j : Fin (2 * q + 1), E j, (∏ j : Fin (2 * q), if Even j.1 then H j (w ⟨j, by omega⟩) (w ⟨j + 1, by omega⟩) else 1) *
      L (w ⟨2 * q, by omega⟩) ∂(Measure.pi fun j : Fin (2 * q + 1) => μ j) =
    (∏ j : Fin (2 * q), if Even j.1 then ∫ p : E j × E (j + 1), H j p.1 p.2 ∂((μ j).prod (μ (j + 1))) else 1) *
      ∫ u, L u ∂(μ (2 * q)) := by
  induction q with
  | zero =>
    intro E _ μ _ H L
    have := integral_fintype_prod_eq_prod (μ := fun j : Fin 1 => μ j) (E := fun j : Fin 1 => E j)
      (fun j : Fin 1 => (Fin.cons L finZeroElim : ∀ j : Fin 1, E j → ℂ) j)
    simpa using this
  | succ q ih =>
    intro E _ μ _ H L
    have h := ih (fun j => E (j + 2)) (fun j => μ (j + 2)) (fun j => H (j.succ.succ : Fin (2 * q + 2))) L
    refine (integral_pi_succ_succ (n := 2 * q + 1) (E := fun j => E j) (fun j => μ j) _).trans ?_
    refine Eq.trans ?_ (congrArg (· * _) (prod_even_succ_succ (2 * q) _).symm)
    rw [mul_assoc]
    refine Eq.trans ?_ (congrArg (_ * ·) h)
    refine Eq.trans ?_ (integral_prod_mul _ _)
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    refine (congrArg (· * _) (prod_even_succ_succ (2 * q) _)).trans ?_
    rw [mul_assoc]
    rfl

theorem prod_pairs (q : ℕ) (a : Fin (2 * q + 1) → ℂ) :
    ∏ j : Fin (2 * q + 1), a j = (∏ j : Fin (2 * q), if Even j.1 then a ⟨j, by omega⟩ * a ⟨j + 1, by omega⟩ else 1) *
      a ⟨2 * q, by omega⟩ := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h := ih (fun j => a (j.succ.succ : Fin (2 * q + 3)))
    erw [prod_even_succ_succ (2 * q), Fin.prod_univ_succ (n := 2 * q + 2), Fin.prod_univ_succ (n := 2 * q + 1), h]
    simp only [← mul_assoc]
    rfl

theorem integral_pi_pairs_even {m : ℕ} (hm : 2 ≤ m) (he : Even m) (E : ℕ → Type) [∀ j, MeasurableSpace (E j)]
    (μ : ∀ j, Measure (E j)) [∀ j, SigmaFinite (μ j)] (H : ∀ j : Fin (m - 2), E j → E (j + 1) → ℂ) (L : E (m - 2) → ℂ) :
    ∫ w : ∀ j : Fin (m - 1), E j, (∏ j : Fin (m - 2), if Even j.1 then H j (w ⟨j, by omega⟩) (w ⟨j + 1, by omega⟩) else 1) *
      L (w ⟨m - 2, by omega⟩) ∂(Measure.pi fun j : Fin (m - 1) => μ j) =
    (∏ j : Fin (m - 2), if Even j.1 then ∫ p : E j × E (j + 1), H j p.1 p.2 ∂((μ j).prod (μ (j + 1))) else 1) *
      ∫ u, L u ∂(μ (m - 2)) := by
  obtain ⟨q, rfl⟩ : ∃ q, m = 2 * q + 2 := by
    obtain ⟨r, hr⟩ := he
    exact ⟨r - 1, by omega⟩
  exact integral_pi_pairs q E μ H L

theorem prod_pairs_even {m : ℕ} (hm : 2 ≤ m) (he : Even m) (a b : Fin (m - 1) → ℂ) :
    (∏ j, a j) * (∏ j : Fin (m - 1), if Even (m - 2 - j) then b j else 1) =
      (∏ j : Fin (m - 2), if Even j.1 then a ⟨j, by omega⟩ * a ⟨j + 1, by omega⟩ * b ⟨j, by omega⟩ else 1) *
      (a ⟨m - 2, by omega⟩ * b ⟨m - 2, by omega⟩) := by
  obtain ⟨q, rfl⟩ : ∃ q, m = 2 * q + 2 := by
    obtain ⟨r, hr⟩ := he
    exact ⟨r - 1, by omega⟩
  rw [← Finset.prod_mul_distrib]
  refine (prod_pairs q _).trans ?_
  congr 1
  · refine Finset.prod_congr rfl fun j _ => if_ctx_congr Iff.rfl (fun hj => ?_) fun _ => rfl
    have h2 := j.2
    rw [Nat.even_iff] at hj
    rw [if_pos (by rw [Nat.even_iff]; simp only; omega), if_neg (by rw [Nat.even_iff]; simp only; omega)]
    ring
  · rw [if_pos (by simp)]; rfl

end Abstract

section Pair
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
  {ψ : AddChar k Circle} (ν : Measure k) [ν.IsAddHaarMeasure]

omit [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k] [ν.IsAddHaarMeasure] in

theorem measurePreserving_comp_equiv {A B : Type} [Fintype A] [Fintype B] [SigmaFinite ν] (e : A ≃ B) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : B => k) e).symm (Measure.pi fun _ => ν)
      (Measure.pi fun _ => ν) := (measurePreserving_piCongrLeft (fun _ : B => ν) e).symm

omit [DecidableEq n] [DecidableEq n'] in

theorem integrable_col {Ψ : Matrix n (n' ⊕ Unit) k → ℂ} (hΨ : Ψ ∈ SB _) (x : Matrix n n' k) :
    Integrable (fun y : n → k => Ψ (fromCols x (Matrix.of fun r _ => y r))) (Measure.pi fun _ => ν) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have h : Topology.IsClosedEmbedding fun y : n → k => fromCols x (Matrix.of fun r (_ : Unit) => y r) := by
    refine Function.LeftInverse.isClosedEmbedding (f := fun z r => z r (.inr ())) (fun y => rfl)
      (continuous_pi fun r => continuous_id.matrix_elem _ _) (continuous_matrix fun r s => ?_)
    rcases s with s | s
    · exact continuous_const
    · exact continuous_apply r
  exact (hΨ.1.continuous.comp h.continuous).integrable_of_hasCompactSupport (hΨ.2.comp_isClosedEmbedding h)

omit [DecidableEq n] [DecidableEq n''] in

theorem integrable_row {Ψ : Matrix (n'' ⊕ Unit) n k → ℂ} (hΨ : Ψ ∈ SB _) (x : Matrix n'' n k) :
    Integrable (fun u : n → k => Ψ (fromRows x (Matrix.of fun _ => u))) (Measure.pi fun _ => ν) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have h : Topology.IsClosedEmbedding fun u : n → k => fromRows x (Matrix.of fun (_ : Unit) => u) := by
    refine Function.LeftInverse.isClosedEmbedding (f := fun z => z (.inr ())) (fun y => rfl)
      (continuous_pi fun r => continuous_id.matrix_elem _ _) (continuous_matrix fun r s => ?_)
    rcases r with r | r
    · exact continuous_const
    · exact continuous_apply s
  exact (hΨ.1.continuous.comp h.continuous).integrable_of_hasCompactSupport (hΨ.2.comp_isClosedEmbedding h)

theorem integral_pair_eq_contr (hψ : Continuous ψ) {Ψ₁ : Matrix n (n' ⊕ Unit) k → ℂ} {Ψ₂ : Matrix (n'' ⊕ Unit) n k → ℂ}
    (h₁ : Ψ₁ ∈ SB _) (h₂ : Ψ₂ ∈ SB _) (x₁ : Matrix n n' k) (x₂ : Matrix n'' n k) :
    ∫ p : (n → k) × (n → k), Ψ₁ (fromCols x₁ (Matrix.of fun r _ => p.1 r)) * Ψ₂ (fromRows x₂ (Matrix.of fun _ => p.2)) *
      (ψ (-∑ r, p.2 r * p.1 r) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) =
      contr ψ ν Ψ₁ Ψ₂ (x₁, x₂) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : Continuous fun p : (n → k) × (n → k) => (ψ (-∑ r, p.2 r * p.1 r) : ℂ) :=
    continuous_subtype_val.comp (hψ.comp (by fun_prop))
  have hI := ((integrable_col ν h₁ x₁).mul_prod (integrable_row ν h₂ x₂)).mul_bdd (c := 1) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => (Circle.norm_coe _).le)
  rw [integral_prod_symm _ hI, contr]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [GlobalTheory.StepData.hat, ← integral_const_mul, neg_mul, one_mul, dotProduct]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

open Classical in

theorem integral_double_step (hψ : Continuous ψ) {c c' : ℕ} (hc : Even c) (hc' : Odd c')
    {Φ₁ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {Φ₂ : Matrix (n'' ⊕ Fin c') (n ⊕ Fin (c' + 1)) k → ℂ}
    (h₁ : Φ₁ ∈ SB _) (h₂ : Φ₂ ∈ SB _) (x₁ : Matrix n n' k) (x₂ : Matrix n'' n k) :
    ∫ p : (KeptVar n c n' → k) × (KeptVar n'' c' n → k), flatStep ψ ν Φ₁ x₁ p.1 * flatStep ψ ν Φ₂ x₂ p.2 *
      (ψ (-∑ r, p.2 (rowIx hc' r) * p.1 (colIx hc r)) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) =
      contr ψ ν (flCol ψ ν (c / 2 + 1) Φ₁) (flRow ψ ν (c' / 2 + 1) Φ₂) (x₁, x₂) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hp := hc'.pos
  rw [← integral_pair_eq_contr ν hψ
    (((flat_SB_onto k ψ ν hψ inferInstance n n' c (c / 2 + 1) (by omega)).1 (by omega)).1 Φ₁ h₁)
    (((flat_SB_onto k ψ ν hψ inferInstance n'' n c' (c' / 2 + 1) (by omega)).2 (by omega)).1 Φ₂ h₂)]
  have h : MeasurePreserving ((MeasurableEquiv.piCongrLeft (fun _ => k) (colEquiv (n := n) (n' := n') hc)).symm.prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ => k) (rowEquiv (n := n'') (n' := n) hc')).symm) _ _ :=
    (measurePreserving_comp_equiv ν (colEquiv hc)).prod (measurePreserving_comp_equiv ν (rowEquiv hc'))
  rw [← h.integral_comp']
  simp only [flatStep_eq_flCol ψ ν hc, flatStep_eq_flRow ψ ν hc']
  rfl

open Classical in

theorem integral_last_step {c : ℕ} (hc : Even c) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix n n' k)
    (z : n → k) :
    ∫ w : KeptVar n c n' → k, flatStep ψ ν Φ x w * (ψ (-∑ r, z r * w (colIx hc r)) : ℂ) ∂(Measure.pi fun _ => ν) =
      GlobalTheory.StepData.hat ψ ν (-1) (fun u => flCol ψ ν (c / 2 + 1) Φ (fromCols x (Matrix.of fun r _ => u r))) z := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [GlobalTheory.StepData.hat, ← (measurePreserving_comp_equiv ν (colEquiv (n := n) (n' := n') hc)).integral_comp']
  simp only [flatStep_eq_flCol ψ ν hc, neg_mul, one_mul, dotProduct]
  rfl

end Pair

theorem flatTensor_pureTensor_eq_prod_contr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (hm : 2 ≤ G.m), Even G.m → ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ j < G.m - 1, φ (.theta G.m j) ∈ SB _) → ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (G.lines₂ (oppositePath G.m) φ) x y = (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) * (φ (.theta G.m (G.m - 1)) (lastMap hs (by omega) x)ᵀ * GlobalTheory.StepData.hat ψ ν (-1) (fun u => flCol ψ ν 1 (stepDatum hs φ ⟨G.m - 2, by omega⟩) (fromCols (x (G.m - 2)) (Matrix.of fun r _ => u r))) (x (G.m - 2 + 1) (topLast G (G.m - 2 + 1 + 1)))) * ∏ j : Fin (G.m - 2), if Even j.1 then contr ψ ν (flCol ψ ν ((G.m - 2 - j) / 2 + 1) (stepDatum hs φ ⟨j, by omega⟩)) (flRow ψ ν ((G.m - 2 - (j + 1)) / 2 + 1) (stepDatum hs φ ⟨j + 1, by omega⟩)) (x j, x (j + 1)) else 1 := by
  intro k _ _ _ _ _ _ G hs hm he ψ ν hψ _ hν φ hφ x y
  classical
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hchar : ∀ (s : Finset (Fin (G.m - 1))) (f : Fin (G.m - 1) → k),
      (ψ (-∑ j ∈ s, f j) : ℂ) = ∏ j ∈ s, (ψ (-f j) : ℂ) := fun s f => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, neg_add, AddChar.map_add_eq_mul,
        Circle.coe_mul, ih]
  have he' := Nat.even_iff.1 he
  have ev : ∀ j : Fin (G.m - 2), Even j.1 → Even (G.m - 2 - j) := fun j hj => by
    have := j.2; rw [Nat.even_iff] at hj ⊢; omega
  have od : ∀ j : Fin (G.m - 2), Even j.1 → Odd (G.m - 2 - (j + 1)) := fun j hj => by
    have := j.2; rw [Nat.even_iff] at hj; rw [Nat.odd_iff]; omega
  have el : Even (G.m - 2 - (G.m - 2)) := by simp
  have key := integral_pi_pairs_even hm he
    (fun j => KeptVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)) → k)
    (fun _ => Measure.pi fun _ => ν)
    (fun j a b => if hj : Even j.1 then flatStep ψ ν (stepDatum hs φ ⟨j, by omega⟩) (x j) a *
      flatStep ψ ν (stepDatum hs φ ⟨j + 1, by omega⟩) (x (j + 1)) b *
      (ψ (-∑ r, b (rowIx (od j hj) r) * a (colIx (ev j hj) r)) : ℂ) else 1)
    (fun a => flatStep ψ ν (stepDatum hs φ ⟨G.m - 2, by omega⟩) (x (G.m - 2)) a *
      (ψ (-∑ r, x (G.m - 2 + 1) (topLast G (G.m - 2 + 1 + 1)) r * a (colIx el r)) : ℂ))
  rw [(flatTensor_pureTensor hs ν (by omega) hψ φ hφ x y).2.2, mul_assoc, mul_assoc, mul_assoc]
  congr 2
  rw [mul_comm]
  refine Eq.trans ?_ (key.trans ?_)
  · unfold keptVol
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have h1 : (ψ (-pairPhase x w) : ℂ) = ∏ j : Fin (G.m - 1),
        if Even (G.m - 2 - j) then (ψ (-∑ r, keptRow x w (j + 1) r * keptCol w j r) : ℂ) else 1 := by
      rw [pairPhase, hchar]
      refine Finset.prod_congr rfl fun j _ => ?_
      split_ifs <;> simp
    simp only
    rw [contractIntegrand, h1, prod_pairs_even hm he]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => if_ctx_congr Iff.rfl (fun hj => ?_) fun _ => rfl
      rw [dif_pos hj]
      congr 4
      refine Finset.sum_congr rfl fun r _ => ?_
      exact congrArg₂ (· * ·) (keptRow_eq x w ⟨j + 1, by omega⟩ (od j hj) r) (keptCol_eq w ⟨j, by omega⟩ (ev j hj) r)
    · congr 4
      refine Finset.sum_congr rfl fun r _ => ?_
      exact congrArg₂ (· * ·) (dif_neg (by simp only; omega)) (keptCol_eq w ⟨G.m - 2, by omega⟩ el r)
  · congr 1
    · refine Finset.prod_congr rfl fun j _ => if_ctx_congr Iff.rfl (fun hj => ?_) fun _ => rfl
      simp only [dif_pos hj]
      convert integral_double_step ν hψ (ev j hj) (od j hj)
        (stepDatum_mem_SB hs ⟨j, by omega⟩ (hφ j (by omega)))
        (stepDatum_mem_SB hs ⟨j + 1, by omega⟩ (hφ (j + 1) (by omega))) (x j) (x (j + 1))
    · have h := integral_last_step (ψ := ψ) ν el (stepDatum hs φ ⟨G.m - 2, by omega⟩) (x (G.m - 2))
        (x (G.m - 2 + 1) (topLast G (G.m - 2 + 1 + 1)))
      rw [show (G.m - 2 - (G.m - 2)) / 2 + 1 = 1 by omega] at h
      convert h

end GlobalTheory.FunObj
