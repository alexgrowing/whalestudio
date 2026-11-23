import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.ContinuousAtInvOfUh

open Matrix MeasureTheory Measure Topology
open scoped ENNReal

noncomputable section

namespace PI.AmpOrbQuot

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon

variable {k r : ℕ}

theorem continuous_ofM {X : Type*} [TopologicalSpace X] {f : X → Mt k r} (hf : Continuous f) :
    Continuous (fun x => Matrix.of (f x)) := hf

theorem continuous_toMt {X : Type*} [TopologicalSpace X]
    {M : X → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hM : Continuous M) :
    Continuous (fun x => (fun i j => M x i j : Mt k r)) := hM

instance instBorelMt2 : BorelSpace (Mt k r × Mt k r) := Prod.borelSpace
instance instBorelPair : BorelSpace (PairSp k r) := Prod.borelSpace
instance instBorelMtPair : BorelSpace (Mt k r × PairSp k r) := Prod.borelSpace

def minv (x : Mt k r) : Mt k r := fun i j => (Matrix.of x)⁻¹ i j

theorem measurable_minv : Measurable (minv (k := k) (r := r)) := by
  have hof : Continuous (fun x : Mt k r => Matrix.of x) := continuous_id
  have hdet : Continuous (fun x : Mt k r => (Matrix.of x).det) := hof.matrix_det
  rw [measurable_pi_iff]; intro i
  rw [measurable_pi_iff]; intro j
  have hadj : Continuous (fun x : Mt k r => (Matrix.of x).adjugate i j) :=
    (hof.matrix_adjugate.matrix_elem i j)
  have e : (fun x : Mt k r => minv x i j) =
      fun x => ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate i j := by
    funext x
    simp only [minv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [e]
  exact (measurable_inv.comp hdet.measurable).mul hadj.measurable

theorem continuous_stabAct (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (fun p : Mt k r × PairSp k r => stabAct g (Matrix.of p.1) p.2) := by
  have hof : Continuous (fun x : Mt k r => Matrix.of x) := continuous_id
  unfold stabAct
  first
    | fun_prop
    | continuity

theorem measurable_stabAct (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (fun p : Mt k r × PairSp k r => stabAct g (Matrix.of p.1) p.2) := (continuous_stabAct g).measurable

theorem measurable_stabAct_inv (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (fun p : Mt k r × PairSp k r => stabAct g (Matrix.of p.1)⁻¹ p.2) := by
  have hf : Measurable (fun p : Mt k r × PairSp k r => (minv p.1, p.2)) := by
    first
      | exact (measurable_minv.comp measurable_fst).prodMk measurable_snd
      | exact (measurable_minv.comp measurable_fst).prod_mk measurable_snd
  exact (measurable_stabAct g).comp hf

theorem measurable_stabAct_one (g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (stabAct (k := k) (r := r) g a) := by
  have hof : Continuous (fun x : Mt k r => Matrix.of x) := continuous_id
  have hc : Continuous (stabAct (k := k) (r := r) g a) := by
    unfold stabAct
    first
      | fun_prop
      | continuity
  exact hc.measurable

private theorem hpk_sq_lemma (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hs : (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) < 2 * r + k + 1 := by
    split_ifs <;> omega
  rw [Finset.sum_eq_single (⟨_, hs⟩ : Fin (2 * r + k + 1))]
  · by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, eq_self_iff_true, and_true]
      split_ifs <;> first | (exfalso; (try simp only [Fin.val_mk] at *); omega) | (simp_all; done) | norm_num
    · rw [if_neg hij]
      rw [Fin.ext_iff] at hij
      simp only [Hpk, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | (exfalso; (try simp only [Fin.val_mk] at *); omega) | (simp_all; done) | norm_num
  · intro l _ hl
    rw [Ne, Fin.ext_iff, Fin.val_mk] at hl
    simp only [Hpk, Fin.ext_iff]
    split_ifs at * <;> first | (exfalso; (try simp only [Fin.val_mk] at *); omega) | (simp_all; done) | norm_num
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem isUnit_det_of_mem_UH' {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    IsUnit g.det := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h : Hpk k r * gᴴ * Hpk k r * g = 1 := by
    calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hpk_sq_lemma k r]
  exact Matrix.isUnit_det_of_left_inverse h

theorem stabAct_comp {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : PairSp k r) :
    stabAct g b (stabAct g a x) = stabAct g (b * a) x := by
  have hd := isUnit_det_of_mem_UH' hg
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
  · funext i j
    show (b * (a * Matrix.of x.1.2)) i j = (b * a * Matrix.of x.1.2) i j
    rw [Matrix.mul_assoc]
  · funext i j
    show (g⁻¹ * b * g * (g⁻¹ * a * g * Matrix.of x.2.2)) i j = (g⁻¹ * (b * a) * g * Matrix.of x.2.2) i j
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left g _ hd]

theorem stabAct_one {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    (x : PairSp k r) : stabAct g 1 x = x := by
  have hd := isUnit_det_of_mem_UH' hg
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
  · funext i j
    show ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * Matrix.of x.1.2) i j = x.1.2 i j
    rw [Matrix.one_mul]
    rfl
  · funext i j
    show (g⁻¹ * (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * g * Matrix.of x.2.2) i j = x.2.2 i j
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul g hd, Matrix.one_mul]
    rfl

theorem stabAct_inv_cancel {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r)) (x : PairSp k r) :
    stabAct g a⁻¹ (stabAct g a x) = x := by
  rw [stabAct_comp hg, Matrix.nonsing_inv_mul a (isUnit_det_of_mem_UH' ha), stabAct_one hg]

theorem stabAct_eq_map (g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    stabAct (k := k) (r := r) g a = Prod.map (Prod.map id (lmulM a)) (Prod.map id (lmulM (g⁻¹ * a * g))) := by
  funext p
  rfl

theorem pairMeas_inv (L : LocBessel k r) [SFinite L.μN]
    (hN : ∀ s ∈ Nset k r, L.μN.map (lmulM s) = L.μN)
    {g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ RStab k r g) :
    (pairMeas L).map (stabAct g a) = pairMeas L := by
  obtain ⟨⟨h1, -⟩, -⟩ := L.hμW
  obtain ⟨⟨h2, -⟩, -⟩ := L.hμW'
  have hof : Continuous (fun x : Mt k r => Matrix.of x) := continuous_id
  have hl : ∀ s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Measurable (lmulM (k := k) (r := r) s) := by
    intro s
    have hc : Continuous (lmulM (k := k) (r := r) s) := by
      unfold lmulM
      first
        | fun_prop
        | continuity
    exact hc.measurable
  have hp : ∀ s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Measurable (Prod.map (id : Mt k r → Mt k r) (lmulM (k := k) (r := r) s)) := by
    intro s
    first
      | exact measurable_id.prodMap (hl s)
      | exact measurable_id.prod_map (hl s)
  rw [stabAct_eq_map, pairMeas, ← Measure.map_prod_map _ _ (hp a) (hp _),
    ← Measure.map_prod_map _ _ measurable_id (hl a), ← Measure.map_prod_map _ _ measurable_id (hl _),
    Measure.map_id, Measure.map_id, hN a ha.1, hN _ ha.2]

def NS (k r : ℕ) : Set (Mt k r) := {x | Matrix.of x ∈ Nset k r}

theorem isClosed_NS : IsClosed (NS k r) := by
  have hof : Continuous (fun x : Mt k r => Matrix.of x) := continuous_id
  have h1 : IsClosed {x : Mt k r | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r} :=
    isClosed_eq (by fun_prop) continuous_const
  have h2 : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), IsClosed {x : Mt k r | a.val ≤ i.val →
      x i (eI k r a) = if i = eI k r a then 1 else 0} := by
    intro a i
    by_cases h : a.val ≤ i.val
    · simp only [h, true_implies]
      exact isClosed_eq (by fun_prop) continuous_const
    · simp only [h, false_implies, Set.setOf_true]
      exact isClosed_univ
  have h3 : ∀ i j : Fin (2 * r + k + 1), IsClosed {x : Mt k r | r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      x i j = if i = j then 1 else 0} := by
    intro i j
    by_cases h : r ≤ j.val ∧ j.val ≤ r + k ∧ r ≤ i.val
    · simp only [h.1, h.2.1, h.2.2, true_implies]
      exact isClosed_eq (by fun_prop) continuous_const
    · have e : {x : Mt k r | r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
          x i j = if i = j then 1 else 0} = Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h1 h2 h3
        exact absurd ⟨h1, h2, h3⟩ h
      rw [e]
      exact isClosed_univ
  have e : NS k r = {x : Mt k r | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r} ∩
      ((⋂ a : Fin r, ⋂ i : Fin (2 * r + k + 1), {x : Mt k r | a.val ≤ i.val →
          x i (eI k r a) = if i = eI k r a then 1 else 0}) ∩
        (⋂ i : Fin (2 * r + k + 1), ⋂ j : Fin (2 * r + k + 1), {x : Mt k r | r ≤ j.val → j.val ≤ r + k →
          r ≤ i.val → x i j = if i = j then 1 else 0})) := by
    ext x
    simp only [NS, Nset, UH, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rfl
  rw [e]
  exact h1.inter ((isClosed_iInter fun a => isClosed_iInter fun i => h2 a i).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => h3 i j))

theorem pairMeas_null (L : LocBessel k r) [SFinite L.μN] (hc : L.μN (NS k r)ᶜ = 0) :
    pairMeas L {y | y.1.2 ∉ NS k r} = 0 := by
  obtain ⟨⟨h1, -⟩, -⟩ := L.hμW
  obtain ⟨⟨h2, -⟩, -⟩ := L.hμW'
  have e : {y : PairSp k r | y.1.2 ∉ NS k r} = (Set.univ ×ˢ (NS k r)ᶜ) ×ˢ Set.univ := by
    ext y; simp
  rw [e, pairMeas, Measure.prod_prod, Measure.prod_prod, hc, mul_zero, zero_mul]

end PI.AmpOrbQuot
