import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HCReprodM

noncomputable section

open MeasureTheory Matrix Topology
open scoped ENNReal NNReal

namespace WlocSk.HM

open Formalism.QuantumDeterminants Formalism.MainNotions.S

abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

structure ClSub {k r : ℕ} (U : Set (Mx k r)) : Prop where
  one_mem : (1 : Mx k r) ∈ U
  mul_mem : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U
  inv_mem : ∀ a ∈ U, a⁻¹ ∈ U
  unit : ∀ a ∈ U, IsUnit a.det
  closed : IsClosed U

def Grp {k r : ℕ} (U : Set (Mx k r)) (_h : ClSub U) : Type := U

namespace Grp
variable {k r : ℕ} {U : Set (Mx k r)} {h : ClSub U}

def val (a : Grp U h) : Mx k r := Subtype.val a
lemma mem (a : Grp U h) : a.val ∈ U := Subtype.property a
def mk (x : Mx k r) (hx : x ∈ U) : Grp U h := (⟨x, hx⟩ : U)
lemma ext' {a b : Grp U h} (e : a.val = b.val) : a = b := Subtype.ext e

instance : Group (Grp U h) where
  mul a b := mk (a.val * b.val) (h.mul_mem _ a.mem _ b.mem)
  one := mk 1 h.one_mem
  inv a := mk (a.val⁻¹) (h.inv_mem _ a.mem)
  mul_assoc a b c := ext' (Matrix.mul_assoc _ _ _)
  one_mul a := ext' (Matrix.one_mul _)
  mul_one a := ext' (Matrix.mul_one _)
  inv_mul_cancel a := ext' (Matrix.nonsing_inv_mul _ (h.unit _ a.mem))

instance : TopologicalSpace (Grp U h) := inferInstanceAs (TopologicalSpace U)
instance : MeasurableSpace (Grp U h) := borel _
instance : BorelSpace (Grp U h) := ⟨rfl⟩

lemma val_mul (a b : Grp U h) : (a * b).val = a.val * b.val := rfl
lemma val_one : (1 : Grp U h).val = 1 := rfl

lemma emb : IsClosedEmbedding (val : Grp U h → Mx k r) := h.closed.isClosedEmbedding_subtypeVal

lemma range_val : Set.range (val : Grp U h → Mx k r) = U := Subtype.range_val

instance : IsTopologicalGroup (Grp U h) where
  continuous_mul := by
    rw [emb.isInducing.continuous_iff]
    exact Continuous.matrix_mul (emb.continuous.comp continuous_fst) (emb.continuous.comp continuous_snd)
  continuous_inv := by
    rw [emb.isInducing.continuous_iff]
    have : (val ∘ fun a : Grp U h => a⁻¹) = fun a : Grp U h => (a.val.det)⁻¹ • a.val.adjugate := by
      funext a
      show a.val⁻¹ = _
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [this]
    have hv : Continuous (val : Grp U h → Mx k r) := emb.continuous
    exact Continuous.smul (Continuous.inv₀ hv.matrix_det fun a => (h.unit _ a.mem).ne_zero) hv.matrix_adjugate

instance : LocallyCompactSpace (Grp U h) :=
  have : LocallyCompactSpace (Mx k r) := inferInstanceAs (LocallyCompactSpace (Mt k r))
  emb.locallyCompactSpace

instance : T2Space (Grp U h) := emb.isEmbedding.t2Space

def vt (a : Grp U h) : Mt k r := a.val

lemma embt : IsClosedEmbedding (vt : Grp U h → Mt k r) := emb

instance : SecondCountableTopology (Grp U h) :=
  have : SecondCountableTopology (Mx k r) := inferInstanceAs (SecondCountableTopology (Mt k r))
  emb.isEmbedding.secondCountableTopology

end Grp

variable {k r : ℕ}

def hmeas (U : Set (Mx k r)) (h : ClSub U) : Measure (Mt k r) :=
  (Measure.haar : Measure (Grp U h)).map Grp.vt

lemma val_cemb (U : Set (Mx k r)) (h : ClSub U) :
    IsClosedEmbedding (Grp.vt : Grp U h → Mt k r) := Grp.embt

lemma val_memb (U : Set (Mx k r)) (h : ClSub U) :
    MeasurableEmbedding (Grp.vt : Grp U h → Mt k r) := (val_cemb U h).measurableEmbedding

lemma hmeas_compact (U : Set (Mx k r)) (h : ClSub U) (K : Set (Mt k r)) (hK : IsCompact K) :
    hmeas U h K < ⊤ := by
  unfold hmeas
  rw [Measure.map_apply (val_cemb U h).continuous.measurable hK.isClosed.measurableSet]
  exact ((val_cemb U h).isCompact_preimage hK).measure_lt_top

instance hmeas_fc (U : Set (Mx k r)) (h : ClSub U) : IsFiniteMeasureOnCompacts (hmeas U h) :=
  ⟨fun K hK => hmeas_compact U h K hK⟩

lemma sigma_of_compact (μ : Measure (Mt k r)) (hμ : ∀ K : Set (Mt k r), IsCompact K → μ K < ⊤) :
    SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨hμ⟩
  infer_instance

theorem hmeas_haar (U : Set (Mx k r)) (h : ClSub U) : IsHaarOn U (hmeas U h) := by
  have hφ := val_cemb U h
  have hmeas' : Measurable (Grp.vt : Grp U h → Mt k r) := hφ.continuous.measurable
  have hUc : @IsClosed (Mt k r) _ U := h.closed
  refine ⟨sigma_of_compact _ (hmeas_compact U h), ?_, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun μ : Measure (Mt k r) => μ Set.univ) h0
    simp only [hmeas, Measure.map_apply hmeas' MeasurableSet.univ, Measure.coe_zero,
      Pi.zero_apply] at h1
    rw [Set.preimage_univ] at h1
    exact (NeZero.ne (Measure.haar : Measure (Grp U h))) (Measure.measure_univ_eq_zero.mp h1)
  · have hm : MeasurableSet {x : Mt k r | Matrix.of x ∉ U} := hUc.measurableSet.compl
    unfold hmeas
    rw [Measure.map_apply hmeas' hm]
    have : (Grp.vt : Grp U h → Mt k r) ⁻¹' {x : Mt k r | Matrix.of x ∉ U} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro a ha
      exact ha a.mem
    rw [this, measure_empty]
  · intro s hs
    have hl : Measurable (lmulM (k := k) (r := r) s) := by
      have : Continuous (lmulM (k := k) (r := r) s) := by
        unfold lmulM
        exact Continuous.matrix_mul continuous_const continuous_id
      exact this.measurable
    unfold hmeas
    rw [Measure.map_map hl hmeas']
    have : lmulM s ∘ (Grp.vt : Grp U h → Mt k r) =
        (Grp.vt : Grp U h → Mt k r) ∘ (fun x => Grp.mk s hs * x) := by
      funext x
      rfl
    rw [this, ← Measure.map_map hmeas' (measurable_const_mul _), map_mul_left_eq_self]

theorem haar_unique (U : Set (Mx k r)) (h : ClSub U) (μ : Measure (Mt k r)) (hμ : IsHaarOn U μ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • hmeas U h := by
  obtain ⟨hσ, h0, hconc, hinv⟩ := hμ
  have hE := val_memb U h
  set ψ := (Grp.vt : Grp U h → Mt k r) with hψdef
  set ν := μ.comap ψ with hνdef
  have hmapν : ν.map ψ = μ := by
    rw [hνdef, hE.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    refine measure_mono_null ?_ hconc
    intro x hx
    by_contra hc
    apply hx
    refine ⟨Grp.mk (h := h) (Matrix.of x) ?_, rfl⟩
    by_contra h'
    exact hc h'
  have hσν : SigmaFinite ν := SigmaFinite.of_map ν hE.measurable.aemeasurable (by rw [hmapν]; exact hσ)
  have hinj : ∀ a b : Measure (Grp U h), a.map ψ = b.map ψ → a = b := by
    intro a b hab
    rw [← hE.comap_map a, ← hE.comap_map b, hab]
  have hleft : ν.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    apply hinj
    have hcomp : ψ ∘ (fun x : Grp U h => g * x) = lmulM (k := k) (r := r) g.val ∘ ψ := by
      funext x
      rfl
    have hmul : Measurable (fun x : Grp U h => g * x) := measurable_const_mul g
    have hlm : Measurable (lmulM (k := k) (r := r) g.val) := by
      have : Continuous (lmulM (k := k) (r := r) g.val) := by
        unfold lmulM
        exact Continuous.matrix_mul continuous_const continuous_id
      exact this.measurable
    rw [Measure.map_map hE.measurable hmul, hcomp, ← Measure.map_map hlm hE.measurable, hmapν]
    exact hinv _ g.mem
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : Grp U h)
  have hK0 : (Measure.haar : Measure (Grp U h)) K ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds _ hKn).ne'
  have hKt : (Measure.haar : Measure (Grp U h)) K ≠ ∞ := hK.measure_lt_top.ne
  have heq := measure_eq_div_smul ν (Measure.haar : Measure (Grp U h)) hK0 hKt
  set c := ν K / (Measure.haar : Measure (Grp U h)) K with hc
  have hcne0 : c ≠ 0 := by
    intro hc0
    apply h0
    rw [← hmapν, heq, hc0, zero_smul, Measure.map_zero]
  have hcnetop : c ≠ ∞ := by
    intro htop
    have hnull : ∀ i, (Measure.haar : Measure (Grp U h)) (spanningSets ν i) = 0 := by
      intro i
      have hlt := measure_spanningSets_lt_top ν i
      have hS : ν (spanningSets ν i) = (c • (Measure.haar : Measure (Grp U h))) (spanningSets ν i) :=
        congrArg (fun m : Measure (Grp U h) => m (spanningSets ν i)) heq
      rw [hS, Measure.smul_apply, smul_eq_mul, htop] at hlt
      by_contra hne
      rw [ENNReal.top_mul hne] at hlt
      exact lt_irrefl _ hlt
    have : (Measure.haar : Measure (Grp U h)) Set.univ = 0 := by
      rw [← iUnion_spanningSets ν]
      exact measure_iUnion_null hnull
    exact (NeZero.ne (Measure.haar : Measure (Grp U h))) (Measure.measure_univ_eq_zero.mp this)
  refine ⟨c, hcne0, hcnetop, ?_⟩
  rw [← hmapν, heq, Measure.map_smul]
  rfl

def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_row (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  unfold Hpk tau sgn
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mul_apply (A : Mx k r) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm
    rw [hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  unfold tau
  apply Fin.ext
  simp only
  split_ifs <;> omega

theorem sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  unfold sgn tau
  simp only
  split_ifs <;> first | rfl | (exfalso; omega)

theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, sgn_mul_self]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

theorem isUnit_of_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * gᴴ * Hpk k r)
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

theorem uh_one : (1 : Mx k r) ∈ UH (Hpk k r) := by
  show (1 : Mx k r)ᴴ * Hpk k r * 1 = Hpk k r
  rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem uh_mul {g h : Mx k r} (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) : g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem uh_inv {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hu := isUnit_of_uh hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem uh_closed : IsClosed (UH (Hpk k r) : Set (Mx k r)) := by
  have hc : Continuous fun g : Mx k r => gᴴ * Hpk k r * g :=
    ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_singleton.preimage hc

theorem uh_clsub : ClSub (UH (Hpk k r) : Set (Mx k r)) :=
  ⟨uh_one, fun _ ha _ hb => uh_mul ha hb, fun _ ha => uh_inv ha, fun _ ha => isUnit_of_uh ha, uh_closed⟩

def col (k r : ℕ) (g : Mx k r) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → (j.val ≤ i.val ∨ r ≤ i.val) →
    g i j = if i = j then 1 else 0

theorem nset_iff (g : Mx k r) : g ∈ Nset k r ↔ g ∈ UH (Hpk k r) ∧ col k r g := by
  constructor
  · rintro ⟨hU, h2, h3⟩
    refine ⟨hU, fun i j hj hi => ?_⟩
    by_cases hjr : j.val < r
    · have e : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
      have := h2 ⟨j.val, hjr⟩ i (by simp only [eI] at *; omega)
      rw [e] at this
      exact this
    · exact h3 i j (by omega) hj (by omega)
  · rintro ⟨hU, hc⟩
    refine ⟨hU, fun a i hi => ?_, fun i j h1 h2 h3 => ?_⟩
    · exact hc i (eI k r a) (by simp only [eI]; omega) (by simp only [eI]; omega)
    · exact hc i j h2 (by omega)

theorem col_one : col k r (1 : Mx k r) := by
  intro i j _ _
  rw [Matrix.one_apply]

theorem col_mul {g h : Mx k r} (hg : col k r g) (hh : col k r h) : col k r (g * h) := by
  intro i j hj hi
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hh j j hj (by omega), if_pos rfl, mul_one]
    exact hg i j hj hi
  · intro m _ hmj
    by_cases hm : j.val ≤ m.val ∨ r ≤ m.val
    · rw [hh m j hj hm, if_neg hmj, mul_zero]
    · push Not at hm
      have hne : i ≠ m := by
        intro e
        subst e
        omega
      rw [hg i m (by omega) (by omega), if_neg hne, zero_mul]
  · intro hj'
    exact absurd (Finset.mem_univ j) hj'

theorem col_of_left_inv {g g' : Mx k r} (hg : col k r g) (hm : g' * g = 1) : col k r g' := by
  have key : ∀ n : ℕ, ∀ i j : Fin (2 * r + k + 1), j.val < n → j.val ≤ r + k →
      (j.val ≤ i.val ∨ r ≤ i.val) → g' i j = if i = j then 1 else 0 := by
    intro n
    induction n with
    | zero => intro i j h; omega
    | succ n ih =>
      intro i j hjn hj hi
      have e := congrFun (congrFun hm i) j
      rw [Matrix.mul_apply, Finset.sum_eq_single j] at e
      · rw [hg j j hj (by omega), if_pos rfl, mul_one] at e
        rw [e, Matrix.one_apply]
      · intro m _ hmj
        by_cases hmc : j.val ≤ m.val ∨ r ≤ m.val
        · rw [hg m j hj hmc, if_neg hmj, mul_zero]
        · push Not at hmc
          have hne : i ≠ m := by
            intro e
            subst e
            omega
          rw [ih i m (by omega) (by omega) (by omega), if_neg hne, zero_mul]
      · intro hj'
        exact absurd (Finset.mem_univ j) hj'
  intro i j hj hi
  exact key (j.val + 1) i j (by omega) hj hi

theorem n_closed : IsClosed (Nset k r : Set (Mx k r)) := by
  have he : ∀ i j : Fin (2 * r + k + 1), Continuous fun g : Mx k r => g i j := fun i j =>
    continuous_id.matrix_elem i j
  have e : Nset k r = UH (Hpk k r) ∩ ((⋂ (a : Fin r) (i : Fin (2 * r + k + 1)) (_ : a.val ≤ i.val),
        {g : Mx k r | g i (eI k r a) = if i = eI k r a then 1 else 0}) ∩
      (⋂ (i : Fin (2 * r + k + 1)) (j : Fin (2 * r + k + 1)) (_ : r ≤ j.val) (_ : j.val ≤ r + k) (_ : r ≤ i.val),
        {g : Mx k r | g i j = if i = j then 1 else 0})) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [e]
  refine uh_closed.inter (IsClosed.inter ?_ ?_)
  · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (he _ _) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_eq (he _ _) continuous_const

theorem n_clsub : ClSub (Nset k r : Set (Mx k r)) := by
  refine ⟨(nset_iff _).2 ⟨uh_one, col_one⟩, ?_, ?_, fun a ha => isUnit_of_uh ha.1, n_closed⟩
  · intro g hg h hh
    rw [nset_iff] at *
    exact ⟨uh_mul hg.1 hh.1, col_mul hg.2 hh.2⟩
  · intro g hg
    rw [nset_iff] at *
    exact ⟨uh_inv hg.1, col_of_left_inv hg.2 (Matrix.nonsing_inv_mul _ (isUnit_of_uh hg.1))⟩

def haarNm (k r : ℕ) : Measure (Mt k r) := hmeas (Nset k r) n_clsub

theorem haarNm_eq : haarNm k r = (Measure.haar : Measure (Grp (Nset k r : Set (Mx k r)) n_clsub)).map Grp.vt := rfl

theorem haarNm_haar : IsHaarOn (Nset k r) (haarNm k r) := hmeas_haar _ _

theorem haarNm_compact (K : Set (Mt k r)) (hK : IsCompact K) : haarNm k r K < ⊤ := hmeas_compact _ _ K hK

theorem n_unique (μ : Measure (Mt k r)) (hμ : IsHaarOn (Nset k r) μ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • haarNm k r :=
  haar_unique _ _ μ hμ

end WlocSk.HM
