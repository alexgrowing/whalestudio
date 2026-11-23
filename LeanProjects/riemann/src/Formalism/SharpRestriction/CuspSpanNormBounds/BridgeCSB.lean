import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

section

open MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.BridgeCSB

def HaarLieN : Prop :=
  ∀ (k r : ℕ) (κ : ℝ≥0∞), κ ≠ 0 → κ ≠ ⊤ →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) (Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) κ)

def ShearMP : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ht : ι → ℕ) (S : (ι → ℝ) → (ι → ℝ)), Measurable S →
    (∀ (i : ι) (x y : ι → ℝ), (∀ j, ht j < ht i → x j = y j) → S x i - x i = S y i - y i) →
    MeasurePreserving S volume volume

end Formalism.MainNotions.BridgeCSB

end

section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.MainNotions.BridgeCSB

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

def mulP (p : Mt k r × Mt k r) : Mt k r := fun i j => (Matrix.of p.1 * Matrix.of p.2) i j

theorem continuous_mulP : Continuous (mulP (k := k) (r := r)) := by
  unfold mulP
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

def hPart (x : Mt k r) : Mt k r := fun i j =>
  if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then x i j else if i = j then 1 else 0

theorem continuous_hPart : Continuous (hPart (k := k) (r := r)) := by
  unfold hPart
  refine continuous_pi fun i => continuous_pi fun j => ?_
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact continuous_const
  · exact continuous_const

def dag (x : Mt k r) : Mt k r := fun i j => (Hpk k r * (Matrix.of x)ᴴ * Hpk k r) i j

theorem continuous_dag : Continuous (dag (k := k) (r := r)) := by
  have h : (dag (k := k) (r := r)) = fun x => fun i j => sgn k r i * (star (x (tau k r j) (tau k r i)) * sgn k r j) := by
    funext x i j
    unfold dag
    rw [Matrix.mul_assoc, hpk_mul_apply, Matrix.mul_apply, Finset.sum_eq_single (tau k r j)]
    · rw [hpk_row, tau_tau, if_pos rfl, sgn_tau]; rfl
    · intro m _ hm
      rw [hpk_row, if_neg, mul_zero]
      intro e; apply hm; rw [e, tau_tau]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  rw [h]
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fun_prop

theorem dag_mul_self {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    Matrix.of (dag (k := k) (r := r) g) * g = 1 := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  show Hpk k r * gᴴ * Hpk k r * g = 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, hpk_sq]

theorem self_mul_dag {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g * Matrix.of (dag (k := k) (r := r) g) = 1 := mul_eq_one_comm.1 (dag_mul_self hg)

theorem dag_eq_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    Matrix.of (dag (k := k) (r := r) g) = g⁻¹ := (Matrix.inv_eq_left_inv (dag_mul_self hg)).symm

theorem hPart_mul {h n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : block k r h) (hn : col k r n) :
    hPart (k := k) (r := r) (h * n) = h := by
  funext i j
  unfold hPart
  split_ifs with h1 h2
  · rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hn j j h1.2.2 (Or.inl le_rfl), if_pos rfl, mul_one]
    · intro l _ hl
      by_cases hlW : r ≤ l.val
      · rw [hn l j h1.2.2 (Or.inr hlW), if_neg hl, mul_zero]
      · rw [hh.1 i l (Or.inl (by omega)), if_neg, zero_mul]
        intro e; rw [e] at h1; omega
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · subst h2
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hh.1 i i hi, if_pos rfl]
    · exfalso; apply h1; omega
  · by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hh.2 i j hi, if_neg h2]
    · have hj : j.val < r ∨ r + k < j.val := by
        by_contra hj; apply h1; omega
      rw [hh.1 i j hj, if_neg h2]

def splitP (x : Mt k r) : Mt k r × Mt k r := (hPart x, mulP (dag (hPart x), x))

theorem continuous_splitP : Continuous (splitP (k := k) (r := r)) :=
  continuous_hPart.prodMk (continuous_mulP.comp ((continuous_dag.comp continuous_hPart).prodMk continuous_id))

theorem splitPair_mulPair {z : Fin (2 * r + k + 1) → ℂ} {p : Mt k r × Mt k r} (h1 : Matrix.of p.1 ∈ UWset k r z)
    (h2 : Matrix.of p.2 ∈ Nset k r) : splitP (mulP p) = p := by
  have e1 : hPart (mulP p) = p.1 := hPart_mul (uw_block h1) ((nset_iff _).1 h2).2
  unfold splitP
  rw [e1]
  refine Prod.ext rfl ?_
  show (Matrix.of (dag p.1) * (Matrix.of p.1 * Matrix.of p.2) : Matrix _ _ ℂ) = Matrix.of p.2
  rw [← Matrix.mul_assoc]
  have := dag_mul_self h1.1
  rw [show Matrix.of (dag p.1) * Matrix.of p.1 = (1 : Matrix _ _ ℂ) from this, Matrix.one_mul]

theorem isClosed_UH : IsClosed {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := by
  have : {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} = {x | mulP (dag x, x) = (1 : Matrix _ _ ℂ)} := by
    ext x
    constructor
    · intro h; exact dag_mul_self h
    · intro h
      have h' : Hpk k r * (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = 1 := h
      show (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r
      have := congrArg (fun M => Hpk k r * M) h'
      simp only [Matrix.mul_one] at this
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Hpk k r) (Hpk k r), hpk_sq, Matrix.one_mul,
        ← Matrix.mul_assoc] at this
      exact this
  rw [this]
  exact isClosed_eq (continuous_mulP.comp (continuous_dag.prodMk continuous_id)) continuous_const

theorem isClosed_N : IsClosed {x : Mt k r | Matrix.of x ∈ Nset k r} := by
  have : {x : Mt k r | Matrix.of x ∈ Nset k r} = {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} ∩
      ⋂ (i : Fin (2 * r + k + 1)) (j : Fin (2 * r + k + 1)),
        {x : Mt k r | j.val ≤ r + k → (j.val ≤ i.val ∨ r ≤ i.val) → x i j = if i = j then 1 else 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, nset_iff]
    rfl
  rw [this]
  refine isClosed_UH.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
  by_cases hc : j.val ≤ r + k ∧ (j.val ≤ i.val ∨ r ≤ i.val)
  · have : {x : Mt k r | j.val ≤ r + k → (j.val ≤ i.val ∨ r ≤ i.val) → x i j = if i = j then 1 else 0} =
        {x | x i j = if i = j then 1 else 0} := by
      ext x; exact ⟨fun h => h hc.1 hc.2, fun h _ _ => h⟩
    rw [this]
    exact isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  · have : {x : Mt k r | j.val ≤ r + k → (j.val ≤ i.val ∨ r ≤ i.val) → x i j = if i = j then 1 else 0} = Set.univ := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro a b; exact absurd ⟨a, b⟩ hc
    rw [this]; exact isClosed_univ

theorem continuous_mulVecM (v : Fin (2 * r + k + 1) → ℂ) : Continuous fun x : Mt k r => Matrix.of x *ᵥ v := by
  refine continuous_pi fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  fun_prop

theorem isClosed_UW (z : Fin (2 * r + k + 1) → ℂ) : IsClosed {x : Mt k r | Matrix.of x ∈ UWset k r z} := by
  have : {x : Mt k r | Matrix.of x ∈ UWset k r z} = {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} ∩
      ((⋂ a : Fin r, ({x : Mt k r | Matrix.of x *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
        {x : Mt k r | Matrix.of x *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {x : Mt k r | Matrix.of x *ᵥ z = z}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, UWset]
  rw [this]
  exact isClosed_UH.inter ((isClosed_iInter fun a => (isClosed_eq (continuous_mulVecM _) continuous_const).inter
    (isClosed_eq (continuous_mulVecM _) continuous_const)).inter (isClosed_eq (continuous_mulVecM _) continuous_const))

end Formalism.MainNotions.BridgeCSB

end

section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.MainNotions.BridgeCSB

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem continuous_lmulM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (lmulM (k := k) (r := r) a) := by
  have : (lmulM (k := k) (r := r) a) = fun x => mulP (a, x) := rfl
  rw [this]
  exact continuous_mulP.comp (continuous_const.prodMk continuous_id)

theorem haarS {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {μW μN : Measure (Mt k r)}
    (hW : IsHaarOn (UWset k r z) μW) (hN : IsHaarOn (Nset k r) μN) :
    IsHaarOn (Sset k r z) ((μW.prod μN).map mulP) := by
  have := hW.1
  have := hN.1
  have mP : Measurable (mulP (k := k) (r := r)) := continuous_mulP.measurable
  have aW : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
  have aN : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := by rw [ae_iff]; exact hN.2.2.1
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae aW).and (Measure.quasiMeasurePreserving_snd.ae aN)
  have hmap : ((μW.prod μN).map mulP).map splitP = μW.prod μN := by
    rw [Measure.map_map continuous_splitP.measurable mP]
    conv_rhs => rw [← Measure.map_id (μ := μW.prod μN)]
    exact Measure.map_congr (hae.mono fun p hp => splitPair_mulPair hp.1 hp.2)
  refine ⟨SigmaFinite.of_map _ continuous_splitP.aemeasurable (by rw [hmap]; infer_instance), ?_, ?_, ?_⟩
  · intro h0
    rw [h0, Measure.map_zero] at hmap
    have h1 : (μW.prod μN) (Set.univ ×ˢ Set.univ) = 0 := by rw [← hmap]; rfl
    rw [Measure.prod_prod, mul_eq_zero, Measure.measure_univ_eq_zero, Measure.measure_univ_eq_zero] at h1
    exact h1.elim hW.2.1 hN.2.1
  · set M : Set (Mt k r) := splitP ⁻¹' ({x : Mt k r | Matrix.of x ∈ UWset k r z} ×ˢ {x : Mt k r | Matrix.of x ∈ Nset k r}) with hM
    have hMm : MeasurableSet M :=
      continuous_splitP.measurable ((isClosed_UW z).measurableSet.prod isClosed_N.measurableSet)
    have hsub : {x : Mt k r | Matrix.of x ∉ Sset k r z} ⊆ Mᶜ := by
      intro x hx hxM
      apply hx
      obtain ⟨h1, h2⟩ := hxM
      refine ⟨_, h1, _, h2, ?_⟩
      show Matrix.of x = Matrix.of (hPart x) * (Matrix.of (dag (hPart x)) * Matrix.of x)
      rw [← Matrix.mul_assoc]
      have := self_mul_dag h1.1
      rw [show Matrix.of (hPart x) * Matrix.of (dag (hPart x)) = (1 : Matrix _ _ ℂ) from this, Matrix.one_mul]
    refine measure_mono_null hsub ?_
    rw [Measure.map_apply mP hMm.compl]
    have : ∀ᵐ p ∂(μW.prod μN), (mulP p : Mt k r) ∈ M := hae.mono fun p hp => by
      show splitP (mulP p) ∈ ({x : Mt k r | Matrix.of x ∈ UWset k r z} ×ˢ {x : Mt k r | Matrix.of x ∈ Nset k r})
      rw [splitPair_mulPair hp.1 hp.2]
      exact ⟨hp.1, hp.2⟩
    rw [ae_iff] at this
    exact this
  · intro s hs
    obtain ⟨h0, hh0, n0, hn0, rfl⟩ := hs
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    have hl : Measurable (lmulM (k := k) (r := r) (h0 * n0)) := (continuous_lmulM _).measurable
    rw [lintegral_map hf hl, lintegral_map (f := fun x => f (lmulM (h0 * n0) x)) (hf.comp hl) mP, lintegral_map hf mP,
      lintegral_prod (fun p => f (lmulM (h0 * n0) (mulP p))) ((hf.comp hl).comp mP).aemeasurable,
      lintegral_prod (fun p => f (mulP p)) (hf.comp mP).aemeasurable]
    set F : Mt k r → ℝ≥0∞ := fun h => ∫⁻ n, f (mulP (h, n)) ∂μN with hFd
    have hF : Measurable F := (hf.comp mP).lintegral_prod_right'
    have step1 : ∀ᵐ h ∂μW, ∫⁻ n, f (lmulM (h0 * n0) (mulP (h, n))) ∂μN = F (lmulM h0 h) := by
      refine aW.mono fun h hh => ?_
      have hu := isUnit_of_uh hh.1
      have hn1 : (Matrix.of h)⁻¹ * n0 * Matrix.of h ∈ Nset k r := by
        have := (uWNormal k r z hz _ (uw_inv hh) n0 hn0).1
        rwa [Matrix.nonsing_inv_nonsing_inv _ hu] at this
      have hm1 : Measurable fun n : Mt k r => f (mulP (lmulM h0 h, n)) :=
        hf.comp (mP.comp (measurable_const.prodMk measurable_id))
      show _ = ∫⁻ n, f (mulP (lmulM h0 h, n)) ∂μN
      conv_rhs => rw [← hN.2.2.2 _ hn1, lintegral_map hm1 (continuous_lmulM _).measurable]
      refine lintegral_congr fun n => congrArg f ?_
      show (h0 * n0 * (Matrix.of h * Matrix.of n) : Matrix _ _ ℂ) =
        h0 * Matrix.of h * ((Matrix.of h)⁻¹ * n0 * Matrix.of h * Matrix.of n)
      have e : Matrix.of h * (Matrix.of h)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
      calc (h0 * n0 * (Matrix.of h * Matrix.of n) : Matrix _ _ ℂ)
          = h0 * (1 * n0) * (Matrix.of h * Matrix.of n) := by rw [Matrix.one_mul]
        _ = h0 * (Matrix.of h * (Matrix.of h)⁻¹ * n0) * (Matrix.of h * Matrix.of n) := by rw [e]
        _ = _ := by simp only [Matrix.mul_assoc]
    calc ∫⁻ h, ∫⁻ n, f (lmulM (h0 * n0) (mulP (h, n))) ∂μN ∂μW = ∫⁻ h, F (lmulM h0 h) ∂μW := lintegral_congr_ae step1
      _ = ∫⁻ h, F h ∂(μW.map (lmulM h0)) := (lintegral_map hF (continuous_lmulM _).measurable).symm
      _ = ∫⁻ h, F h ∂μW := by rw [hW.2.2.2 h0 hh0]

end Formalism.MainNotions.BridgeCSB

end

section

open MeasureTheory

namespace Formalism.MainNotions.BridgeCSB

theorem shear_step {ι : Type} [Fintype ι] [DecidableEq ι] (ht : ι → ℕ) (S : (ι → ℝ) → (ι → ℝ)) (hS : Measurable S)
    (hsh : ∀ (i : ι) (x y : ι → ℝ), (∀ j, ht j < ht i → x j = y j) → S x i - x i = S y i - y i) (p : ℕ) :
    MeasurePreserving (fun y : ι → ℝ => fun i => if ht i = p then S y i else y i) volume volume := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun i => ht i ≠ p)
  have he : MeasurePreserving e volume volume := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℝ) _
  let gg : ({i // ht i ≠ p} → ℝ) → ({i // ¬ ht i ≠ p} → ℝ) := fun v i => S (e.symm (v, 0)) i - e.symm (v, 0) i
  have hgg : Measurable gg := by
    refine measurable_pi_lambda _ fun i => ?_
    exact ((measurable_pi_apply _).comp (hS.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))).sub
      ((measurable_pi_apply _).comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))
  have hF : MeasurePreserving (fun q : ({i // ht i ≠ p} → ℝ) × ({i // ¬ ht i ≠ p} → ℝ) => (id q.1, q.2 + gg q.1))
      volume volume := by
    refine MeasurePreserving.skew_product (μc := (volume : Measure ({i // ¬ ht i ≠ p} → ℝ)))
      (μd := (volume : Measure ({i // ¬ ht i ≠ p} → ℝ))) (MeasurePreserving.id (volume : Measure ({i // ht i ≠ p} → ℝ)))
      (g := fun v u => u + gg v) ?_ ?_
    · exact measurable_snd.add (hgg.comp measurable_fst)
    · exact Filter.Eventually.of_forall fun v => map_add_right_eq_self (volume : Measure ({i // ¬ ht i ≠ p} → ℝ)) (gg v)
  have hcomp := (he.symm.comp hF).comp he
  convert hcomp using 1
  funext y i
  simp only [Function.comp, e, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply,
    id, gg]
  by_cases hi : ht i = p
  · have hni : ¬ ht i ≠ p := fun h => h hi
    have := hsh i y (e.symm ((fun j : {j // ht j ≠ p} => y j), 0)) (fun j hj => by
      have hj' : ht j ≠ p := by omega
      simp [e, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, hj'])
    simp only [e] at this
    simp [hi] at this ⊢
    linarith
  · simp only [hi, if_false, dif_pos hi]

theorem shearMP : ShearMP := by
  intro ι _ _ ht S hS hsh
  classical
  let Sp : ℕ → (ι → ℝ) → (ι → ℝ) := fun p x i => if p ≤ ht i then S x i else x i
  have hSp0 : Sp 0 = S := by funext x i; simp [Sp]
  obtain ⟨P, hP⟩ : ∃ P, ∀ i, ht i < P :=
    ⟨Finset.univ.sup ht + 1, fun i => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))⟩
  have hSpP : Sp P = id := by funext x i; simp [Sp, not_le.2 (hP i)]
  have hmeas : ∀ p, Measurable (Sp p) := fun p => measurable_pi_lambda _ fun i => by
    by_cases h : p ≤ ht i
    · simp only [Sp, h, if_true]; exact (measurable_pi_apply i).comp hS
    · simp only [Sp, h, if_false]; exact measurable_pi_apply i
  have hfac : ∀ p, Sp p = (fun y : ι → ℝ => fun i => if ht i = p then S y i else y i) ∘ Sp (p + 1) := by
    intro p
    funext x i
    simp only [Function.comp, Sp]
    by_cases hi : ht i = p
    · simp only [hi, le_refl, if_true, show ¬ (p + 1 ≤ p) by omega, if_false]
      have := hsh i x (fun j => if p + 1 ≤ ht j then S x j else x j) (fun j hj => by
        simp only [show ¬ (p + 1 ≤ ht j) by omega, if_false])
      simp only [show ¬ (p + 1 ≤ ht i) by omega, if_false] at this
      linarith
    · by_cases h2 : p + 1 ≤ ht i
      · simp only [hi, if_false, h2, if_true, show p ≤ ht i by omega]
      · simp only [hi, if_false, h2, show ¬ p ≤ ht i by omega]
  have key : ∀ q, q ≤ P → MeasurePreserving (Sp (P - q)) volume volume := by
    intro q
    induction q with
    | zero => intro _; simpa [hSpP] using MeasurePreserving.id (volume : Measure (ι → ℝ))
    | succ q ih =>
      intro hq
      have e1 : P - q = P - (q + 1) + 1 := by omega
      have h := ih (by omega)
      rw [e1] at h
      rw [hfac]
      exact (shear_step ht S hS hsh _).comp h
  have := key P le_rfl
  simpa [hSp0] using this

end Formalism.MainNotions.BridgeCSB

end

section

open Matrix

namespace Formalism.MainNotions.BridgeCSB

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

def dg (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k

theorem dg_le (i : Fin (2 * r + k + 1)) : dg k r i ≤ 2 * r := by
  have := i.isLt; unfold dg; split_ifs <;> omega

theorem tau_val (i : Fin (2 * r + k + 1)) :
    (tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl

theorem dg_tau (i : Fin (2 * r + k + 1)) : dg k r (tau k r i) = 2 * r - dg k r i := by
  have := i.isLt
  unfold dg
  rw [tau_val]
  split_ifs <;> omega

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def Fil (p : ℕ) (X : Mat k r) : Prop := ∀ i j, dg k r j < dg k r i + p → X i j = 0

theorem Fil.mono {p q : ℕ} {X : Mat k r} (hpq : p ≤ q) (h : Fil q X) : Fil p X :=
  fun i j hij => h i j (by omega)

theorem Fil.zero (p : ℕ) : Fil p (0 : Mat k r) := fun _ _ _ => rfl

theorem Fil.add {p : ℕ} {X Y : Mat k r} (hX : Fil p X) (hY : Fil p Y) : Fil p (X + Y) :=
  fun i j h => by rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]

theorem Fil.neg {p : ℕ} {X : Mat k r} (hX : Fil p X) : Fil p (-X) :=
  fun i j h => by rw [Matrix.neg_apply, hX i j h, neg_zero]

theorem Fil.sub {p : ℕ} {X Y : Mat k r} (hX : Fil p X) (hY : Fil p Y) : Fil p (X - Y) :=
  fun i j h => by rw [Matrix.sub_apply, hX i j h, hY i j h, sub_zero]

theorem Fil.smul {p : ℕ} {X : Mat k r} (c : ℂ) (hX : Fil p X) : Fil p (c • X) :=
  fun i j h => by rw [Matrix.smul_apply, hX i j h, smul_zero]

theorem Fil.sum {p : ℕ} {ι : Type*} (s : Finset ι) (X : ι → Mat k r) (h : ∀ a ∈ s, Fil p (X a)) :
    Fil p (∑ a ∈ s, X a) := by
  intro i j hij
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero fun a ha => h a ha i j hij

theorem Fil.mul {a b : ℕ} {X Y : Mat k r} (hX : Fil a X) (hY : Fil b Y) : Fil (a + b) (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : dg k r l < dg k r i + a
  · rw [hX i l hl, zero_mul]
  · rw [hY l j (by omega), mul_zero]

theorem Fil.one : Fil 0 (1 : Mat k r) := by
  intro i j h
  rw [Matrix.one_apply, if_neg]
  intro e; rw [e] at h; omega

theorem Fil.eq_zero {X : Mat k r} {p : ℕ} (hp : 2 * r + 1 ≤ p) (h : Fil p X) : X = 0 := by
  ext i j
  exact h i j (by have := dg_le (k := k) (r := r) j; omega)

theorem Fil.pow {X : Mat k r} (hX : Fil 1 X) (m : ℕ) : Fil m (X ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact Fil.one
  | succ m ih => rw [pow_succ]; exact ih.mul hX

theorem exp_eq_sum {X : Mat k r} (hX : Fil 1 X) :
    NormedSpace.exp X = ∑ m ∈ Finset.range (2 * r + 2), ((m.factorial : ℂ)⁻¹) • X ^ m := by
  have h : X ^ (2 * r + 2) = 0 := (hX.pow _).eq_zero (by omega)
  rw [NormedSpace.exp_eq_tsum ℂ]
  simp only []
  rw [tsum_eq_sum (s := Finset.range (2 * r + 2))]
  intro m hm
  have hm2 : 2 * r + 2 ≤ m := by simpa using hm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm2
  rw [pow_add, h]
  simp

theorem Fil.exp_sub_one {X : Mat k r} (hX : Fil 1 X) : Fil 1 (NormedSpace.exp X - 1) := by
  rw [exp_eq_sum hX, Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, add_sub_cancel_right]
  refine Fil.sum _ _ fun m _ => Fil.smul _ ?_
  exact (hX.pow (m + 1)).mono (by omega)

theorem Fil.pow_sub_pow {X Y : Mat k r} {p : ℕ} (hX : Fil 1 X) (hY : Fil 1 Y) (h : Fil p (X - Y)) (m : ℕ) :
    Fil (p + m) (X ^ (m + 1) - Y ^ (m + 1)) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    have e : X ^ (m + 1 + 1) - Y ^ (m + 1 + 1) = X * (X ^ (m + 1) - Y ^ (m + 1)) + (X - Y) * Y ^ (m + 1) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← pow_succ', ← pow_succ']; abel
    rw [e]
    refine Fil.add ?_ ?_
    · exact (hX.mul ih).mono (by omega)
    · exact (h.mul (hY.pow (m + 1))).mono (by omega)

theorem Fil.exp_sub_exp {X Y : Mat k r} {p : ℕ} (hX : Fil 1 X) (hY : Fil 1 Y) (h : Fil p (X - Y)) :
    Fil (p + 1) ((NormedSpace.exp X - NormedSpace.exp Y) - (X - Y)) := by
  rw [exp_eq_sum hX, exp_eq_sum hY, ← Finset.sum_sub_distrib, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, sub_self, add_zero, zero_add, pow_one,
    Nat.factorial_one]
  have e : ∀ s : Mat k r, s + (X - Y) - (X - Y) = s := fun s => by abel
  rw [e]
  refine Fil.sum _ _ fun m _ => ?_
  rw [← smul_sub]
  exact Fil.smul _ ((Fil.pow_sub_pow hX hY h (m + 1)).mono (by omega))

theorem Fil.of_exp {X Y : Mat k r} {p : ℕ} (hX : Fil 1 X) (hY : Fil 1 Y)
    (h : Fil p (NormedSpace.exp X - NormedSpace.exp Y)) : Fil p (X - Y) := by
  have key : ∀ q, q ≤ p → Fil q (X - Y) := by
    intro q
    induction q with
    | zero => intro _; exact (hX.sub hY).mono (Nat.zero_le 1)
    | succ q ih =>
      intro hq
      have h1 := Fil.exp_sub_exp hX hY (ih (by omega))
      have h2 : Fil (q + 1) (NormedSpace.exp X - NormedSpace.exp Y) := h.mono hq
      have := h2.sub h1
      simpa using this
  exact key p le_rfl

theorem exp_injOn {X Y : Mat k r} (hX : Fil 1 X) (hY : Fil 1 Y) (h : NormedSpace.exp X = NormedSpace.exp Y) :
    X = Y := by
  have : Fil (2 * r + 1) (X - Y) := Fil.of_exp hX hY (by rw [h, sub_self]; exact Fil.zero _)
  exact sub_eq_zero.1 (this.eq_zero le_rfl)

def adjH (X : Mat k r) : Mat k r := Hpk k r * Xᴴ * Hpk k r

theorem adjH_apply (X : Mat k r) (i j : Fin (2 * r + k + 1)) :
    adjH X i j = sgn k r i * star (X (tau k r j) (tau k r i)) * sgn k r j := by
  unfold adjH
  rw [Matrix.mul_assoc, hpk_mul_apply, Matrix.mul_apply, Finset.sum_eq_single (tau k r j)]
  · rw [hpk_row, tau_tau, if_pos rfl, sgn_tau, Matrix.conjTranspose_apply]; ring
  · intro m _ hm
    rw [hpk_row, if_neg, mul_zero]
    intro e; apply hm; rw [e, tau_tau]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem star_sgn (i : Fin (2 * r + k + 1)) : star (sgn k r i) = sgn k r i := by
  unfold sgn; split_ifs <;> simp

theorem adjH_mul (X Y : Mat k r) : adjH (X * Y) = adjH Y * adjH X := by
  unfold adjH
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), hpk_sq, Matrix.one_mul]

theorem adjH_adjH (X : Mat k r) : adjH (adjH X) = X := by
  ext i j
  rw [adjH_apply, adjH_apply, tau_tau, tau_tau, sgn_tau, sgn_tau, star_mul, star_mul, star_star, star_sgn, star_sgn]
  have hi := sgn_mul_self (k := k) (r := r) i
  have hj := sgn_mul_self (k := k) (r := r) j
  calc sgn k r i * (sgn k r i * (X i j * sgn k r j)) * sgn k r j = (sgn k r i * sgn k r i) * (sgn k r j * sgn k r j) * X i j := by ring
    _ = X i j := by rw [hi, hj]; ring

theorem adjH_one : adjH (1 : Mat k r) = 1 := by
  unfold adjH; rw [Matrix.conjTranspose_one, Matrix.mul_one, hpk_sq]

theorem adjH_add (X Y : Mat k r) : adjH (X + Y) = adjH X + adjH Y := by
  unfold adjH; rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem adjH_sub (X Y : Mat k r) : adjH (X - Y) = adjH X - adjH Y := by
  unfold adjH; rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem adjH_neg (X : Mat k r) : adjH (-X) = -adjH X := by
  unfold adjH; rw [Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul]

theorem adjH_smul (c : ℂ) (X : Mat k r) : adjH (c • X) = star c • adjH X := by
  unfold adjH; rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem adjH_pow (X : Mat k r) (m : ℕ) : adjH (X ^ m) = adjH X ^ m := by
  induction m with
  | zero => simp [adjH_one]
  | succ m ih => rw [pow_succ, adjH_mul, ih, ← pow_succ']

theorem adjH_sum {ι : Type*} (s : Finset ι) (X : ι → Mat k r) : adjH (∑ a ∈ s, X a) = ∑ a ∈ s, adjH (X a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [adjH]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, adjH_add, ih]

theorem Fil.adjH {p : ℕ} {X : Mat k r} (h : Fil p X) : Fil p (adjH X) := by
  intro i j hij
  rw [adjH_apply, h (tau k r j) (tau k r i) (by
    rw [dg_tau, dg_tau]; have := dg_le (k := k) (r := r) i; have := dg_le (k := k) (r := r) j; omega), star_zero,
    mul_zero, zero_mul]

theorem mem_UH_iff (g : Mat k r) : g ∈ UH (Hpk k r) ↔ adjH g * g = 1 := by
  constructor
  · intro h; exact dag_mul_self h
  · intro h
    show gᴴ * Hpk k r * g = Hpk k r
    have := congrArg (fun M => Hpk k r * M) h
    simp only [Matrix.mul_one, adjH] at this
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Hpk k r) (Hpk k r), hpk_sq, Matrix.one_mul,
      ← Matrix.mul_assoc] at this
    exact this

theorem adjH_exp {X : Mat k r} (hX : Fil 1 X) : adjH (NormedSpace.exp X) = NormedSpace.exp (adjH X) := by
  rw [exp_eq_sum hX, exp_eq_sum hX.adjH, adjH_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [adjH_smul, adjH_pow]
  congr 1
  simp

end Formalism.MainNotions.BridgeCSB

end

section

open Matrix

namespace Formalism.MainNotions.BridgeCSB

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem mem_N_iff (g : Mat k r) : g ∈ Nset k r ↔ g ∈ UH (Hpk k r) ∧ Fil 1 (g - 1) := by
  rw [nset_iff]
  constructor
  · rintro ⟨hU, hc⟩
    refine ⟨hU, fun i j hij => ?_⟩
    rw [Matrix.sub_apply, Matrix.one_apply]
    have hi := i.isLt
    have hj := j.isLt
    by_cases hjk : j.val ≤ r + k
    · rw [hc i j hjk (by unfold dg at hij; split_ifs at hij <;> omega), sub_self]
    · have hg' : adjH g ∈ Nset k r := by
        have := mem_n_inv ((nset_iff g).2 ⟨hU, hc⟩)
        rwa [← dag_eq_inv hU] at this
      have hc' := ((nset_iff _).1 hg').2
      have hi2 : r + k < i.val := by unfold dg at hij; split_ifs at hij <;> omega
      have e : g i j = adjH (adjH g) i j := by rw [adjH_adjH]
      have hτi : (tau k r i).val = 2 * r + k - i.val := by
        rw [tau_val, if_pos (Or.inr (by unfold dg at hij; split_ifs at hij <;> omega))]
      have hτj : (tau k r j).val = 2 * r + k - j.val := by rw [tau_val, if_pos (Or.inr (by omega))]
      rw [e, adjH_apply, hc' (tau k r j) (tau k r i) (by omega) (by unfold dg at hij; split_ifs at hij <;> omega)]
      by_cases hij' : i = j
      · subst hij'
        rw [if_pos rfl, if_pos rfl, star_one, mul_one, sgn_mul_self, sub_self]
      · rw [if_neg (fun e' => hij' (by rw [← tau_tau (k := k) (r := r) i, ← e', tau_tau])), if_neg hij', star_zero,
          mul_zero, zero_mul, sub_zero]
  · rintro ⟨hU, hF⟩
    refine ⟨hU, fun i j hj hi => ?_⟩
    have := hF i j (by unfold dg; split_ifs <;> omega)
    rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero] at this
    exact this

def lieN (k r : ℕ) : Set (Mat k r) := {X | Fil 1 X ∧ adjH X + X = 0}

theorem lieN_smul {X : Mat k r} (hX : X ∈ lieN k r) (t : ℝ) : ((t : ℂ) • X) ∈ lieN k r := by
  refine ⟨hX.1.smul _, ?_⟩
  rw [adjH_smul, Complex.star_def, Complex.conj_ofReal, ← smul_add, hX.2, smul_zero]

theorem exp_mem_N {X : Mat k r} (hX : X ∈ lieN k r) : NormedSpace.exp X ∈ Nset k r := by
  rw [mem_N_iff]
  refine ⟨?_, hX.1.exp_sub_one⟩
  rw [mem_UH_iff, adjH_exp hX.1, eq_neg_of_add_eq_zero_left hX.2, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_exp X).map Matrix.detMonoidHom)

theorem exp_smul_inj {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • A) = NormedSpace.exp ((t : ℂ) • B)) : A = B := by
  letI : SeminormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
  have hA : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A)) (NormedSpace.exp ((0 : ℝ) • A) * A) 0 :=
    hasDerivAt_exp_smul_const A 0
  have hB : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • B)) (NormedSpace.exp ((0 : ℝ) • B) * B) 0 :=
    hasDerivAt_exp_smul_const B 0
  have e : (fun u : ℝ => NormedSpace.exp (u • A)) = fun u : ℝ => NormedSpace.exp (u • B) := by
    funext u
    have hu : ∀ M : Matrix (Fin d) (Fin d) ℂ, u • M = ((u : ℂ) • M) := fun M => (Complex.coe_smul u M).symm
    rw [hu, hu]
    exact h u
  rw [e] at hA
  have := hA.unique hB
  simpa using this

theorem entry_zero_of_const' {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) (c : ℂ)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) i j = c) : X i j = 0 := by
  letI : SeminormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const X 0
  let L : Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 : (L ∘ fun u : ℝ => NormedSpace.exp (u • X)) = fun _ => c := by
    funext u
    have hu : (u • X) = ((u : ℂ) • X) := (Complex.coe_smul u X).symm
    simp only [Function.comp, hu]
    exact h u
  rw [h3] at h2
  have h4 := h2.unique (hasDerivAt_const (0 : ℝ) c)
  have h5 : (NormedSpace.exp ((0 : ℝ) • X) * X) i j = 0 := h4
  simpa using h5

theorem hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hpk_sq

theorem isUnit_hpk : IsUnit (Hpk k r) := ⟨⟨Hpk k r, Hpk k r, hpk_sq, hpk_sq⟩, rfl⟩

theorem adjH_exp_gen (A : Mat k r) : adjH (NormedSpace.exp A) = NormedSpace.exp (adjH A) := by
  unfold adjH
  rw [← Matrix.exp_conjTranspose]
  conv_lhs => rw [← hpk_inv (k := k) (r := r)]
  conv_rhs => rw [show Hpk k r * Aᴴ * Hpk k r = Hpk k r * Aᴴ * (Hpk k r)⁻¹ by rw [hpk_inv]]
  rw [Matrix.exp_conj _ _ isUnit_hpk, hpk_inv]

theorem lieOf_N : lieOf (Nset k r) = lieN k r := by
  ext X
  constructor
  · intro hX
    have hadj : adjH X = -X := by
      apply exp_smul_inj
      intro t
      have hg := hX t
      have hU := ((mem_N_iff _).1 hg).1
      have h1 : adjH (NormedSpace.exp ((t : ℂ) • X)) = (NormedSpace.exp ((t : ℂ) • X))⁻¹ :=
        Matrix.inv_eq_left_inv ((mem_UH_iff _).1 hU) |>.symm
      rw [adjH_exp_gen, adjH_smul, Complex.star_def, Complex.conj_ofReal, ← Matrix.exp_neg] at h1
      rw [h1, smul_neg]
    have hcol : ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → (j.val ≤ i.val ∨ r ≤ i.val) → X i j = 0 := by
      intro i j hj hi
      exact entry_zero_of_const' X i j (if i = j then 1 else 0) fun t => ((nset_iff _).1 (hX t)).2 i j hj hi
    refine ⟨fun i j hij => ?_, by rw [hadj, neg_add_cancel]⟩
    have hi := i.isLt
    have hj := j.isLt
    by_cases hjk : j.val ≤ r + k
    · exact hcol i j hjk (by unfold dg at hij; split_ifs at hij <;> omega)
    · have hi2 : r + k < i.val := by unfold dg at hij; split_ifs at hij <;> omega
      have hτi : (tau k r i).val = 2 * r + k - i.val := by
        rw [tau_val, if_pos (Or.inr (by unfold dg at hij; split_ifs at hij <;> omega))]
      have hτj : (tau k r j).val = 2 * r + k - j.val := by rw [tau_val, if_pos (Or.inr (by omega))]
      have e : X i j = -(adjH X i j) := by rw [hadj, Matrix.neg_apply, neg_neg]
      rw [e, adjH_apply, hcol (tau k r j) (tau k r i) (by omega) (by unfold dg at hij; split_ifs at hij <;> omega),
        star_zero, mul_zero, zero_mul, neg_zero]
  · intro hX t
    exact exp_mem_N (lieN_smul hX t)

def Pg (p : ℕ) (M : Mat k r) : Mat k r := fun i j => if dg k r j = dg k r i + p then M i j else 0

theorem Fil.sub_Pg {p : ℕ} {M : Mat k r} (h : Fil p M) : Fil (p + 1) (M - Pg p M) := by
  intro i j hij
  rw [Matrix.sub_apply]
  unfold Pg
  by_cases e : dg k r j = dg k r i + p
  · rw [if_pos e, sub_self]
  · rw [if_neg e, h i j (by omega), sub_zero]

theorem Fil.Pg (p : ℕ) (M : Mat k r) : Fil p (Pg p M) := by
  intro i j hij
  unfold Formalism.MainNotions.BridgeCSB.Pg
  rw [if_neg (by omega)]

theorem Pg_of_Fil {p : ℕ} {M : Mat k r} (h : Fil (p + 1) M) : Pg p M = 0 := by
  ext i j
  unfold Pg
  split_ifs with e
  · exact h i j (by omega)
  · rfl

theorem Pg_add (p : ℕ) (A B : Mat k r) : Pg p (A + B) = Pg p A + Pg p B := by
  ext i j
  rw [Matrix.add_apply]
  unfold Pg
  split_ifs
  · rfl
  · rw [add_zero]

theorem Pg_adjH (p : ℕ) (M : Mat k r) : Pg p (adjH M) = adjH (Pg p M) := by
  ext i j
  rw [adjH_apply]
  unfold Pg
  have hi := dg_le (k := k) (r := r) i
  have hj := dg_le (k := k) (r := r) j
  by_cases e : dg k r j = dg k r i + p
  · rw [if_pos e, if_pos (by rw [dg_tau, dg_tau]; omega), adjH_apply]
  · rw [if_neg e, if_neg (by rw [dg_tau, dg_tau]; omega), star_zero, mul_zero, zero_mul]

theorem lieN_add {X Y : Mat k r} (hX : X ∈ lieN k r) (hY : Y ∈ lieN k r) : X + Y ∈ lieN k r := by
  refine ⟨hX.1.add hY.1, ?_⟩
  rw [adjH_add]
  have := congrArg₂ (· + ·) hX.2 hY.2
  simp only [add_zero] at this
  rw [← this]; abel

theorem zero_mem_lieN : (0 : Mat k r) ∈ lieN k r := ⟨Fil.zero _, by simp [adjH]⟩

theorem exp_surj {g : Mat k r} (hg : g ∈ Nset k r) : ∃ X ∈ lieN k r, NormedSpace.exp X = g := by
  obtain ⟨hgU, hg1⟩ := (mem_N_iff g).1 hg
  have key : ∀ p, 1 ≤ p → ∃ X ∈ lieN k r, Fil p (g - NormedSpace.exp X) := by
    intro p hp
    induction p with
    | zero => omega
    | succ p ih =>
      rcases Nat.eq_zero_or_pos p with h0 | hpos
      · subst h0
        exact ⟨0, zero_mem_lieN, by rw [NormedSpace.exp_zero]; exact hg1⟩
      obtain ⟨X, hX, hM⟩ := ih hpos
      obtain ⟨h, hhd⟩ : ∃ h, h = NormedSpace.exp X := ⟨_, rfl⟩
      obtain ⟨M, hMd⟩ : ∃ M, M = g - h := ⟨_, rfl⟩
      rw [← hhd, ← hMd] at hM
      have hhN : h ∈ Nset k r := hhd ▸ exp_mem_N hX
      obtain ⟨hhU, hh1⟩ := (mem_N_iff h).1 hhN
      obtain ⟨Z, hZd⟩ : ∃ Z, Z = Pg p M := ⟨_, rfl⟩
      have hgM : g = h + M := by rw [hMd]; abel

      have hsum : Fil (p + 1) (adjH M + M) := by
        have e1 := (mem_UH_iff g).1 hgU
        have e2 := (mem_UH_iff h).1 hhU
        rw [hgM, adjH_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e2] at e1
        have e3 : adjH M + M = -((adjH h - 1) * M + adjH M * (h - 1) + adjH M * M) := by
          have h0 : adjH h * M + (adjH M * h + adjH M * M) = 0 := by
            rw [show adjH h * M + (adjH M * h + adjH M * M) = (1 + adjH h * M + (adjH M * h + adjH M * M)) - 1 by abel,
              e1, sub_self]
          have h5 : (adjH h - 1) * M + adjH M * (h - 1) + adjH M * M =
              (adjH h * M + (adjH M * h + adjH M * M)) - M - adjH M := by
            simp only [sub_mul, mul_sub, one_mul, mul_one]; abel
          rw [h5, h0]; abel
        rw [e3]
        refine Fil.neg (Fil.add (Fil.add ?_ ?_) ?_)
        · have := (show Fil 1 (adjH h - 1) by rw [← adjH_one, ← adjH_sub]; exact hh1.adjH).mul hM
          exact this.mono (by omega)
        · exact (hM.adjH.mul hh1).mono (by omega)
        · exact (hM.adjH.mul hM).mono (by omega)
      have hZ : Z ∈ lieN k r := by
        refine ⟨hZd ▸ (Fil.Pg p M).mono hpos, ?_⟩
        have := Pg_of_Fil hsum
        rwa [Pg_add, Pg_adjH, ← hZd] at this
      refine ⟨X + Z, lieN_add hX hZ, ?_⟩
      have e4 : g - NormedSpace.exp (X + Z) = (M - Z) -
          ((NormedSpace.exp (X + Z) - NormedSpace.exp X) - ((X + Z) - X)) := by
        rw [hMd, ← hhd]; abel
      rw [e4]
      refine Fil.sub (hZd ▸ hM.sub_Pg) (Fil.exp_sub_exp (hX.1.add hZ.1) hX.1 ?_)
      rw [add_sub_cancel_left, hZd]
      exact Fil.Pg p M
  obtain ⟨X, hX, h⟩ := key (2 * r + 1) (by omega)
  exact ⟨X, hX, (sub_eq_zero.1 (h.eq_zero le_rfl)).symm⟩

end Formalism.MainNotions.BridgeCSB

end

section

set_option linter.style.haveILetI false

open Matrix

namespace Formalism.MainNotions.BridgeCSB

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

def lieNS (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := lieN k r
  add_mem' := lieN_add
  zero_mem' := zero_mem_lieN
  smul_mem' := fun c X hX => by
    show c • X ∈ lieN k r
    rw [← Complex.coe_smul]; exact lieN_smul hX c

theorem Pg_apply (p : ℕ) (M : Mat k r) (i j : Fin (2 * r + k + 1)) :
    Pg p M i j = if dg k r j = dg k r i + p then M i j else 0 := rfl

theorem Pg_smul (p : ℕ) (c : ℝ) (M : Mat k r) : Pg p (c • M) = c • Pg p M := by
  ext i j
  rw [Matrix.smul_apply, Pg_apply, Pg_apply, Matrix.smul_apply]
  split_ifs
  · rfl
  · rw [smul_zero]

theorem Pg_Pg (p q : ℕ) (M : Mat k r) : Pg q (Pg p M) = if p = q then Pg p M else 0 := by
  by_cases h : p = q
  · subst h
    rw [if_pos rfl]
    ext i j
    rw [Pg_apply, Pg_apply]
    split_ifs <;> rfl
  · rw [if_neg h]
    ext i j
    rw [Pg_apply, Pg_apply, Matrix.zero_apply]
    split_ifs <;> first | rfl | omega

theorem Pg_zero (p : ℕ) : Pg p (0 : Mat k r) = 0 := by
  ext i j; rw [Pg_apply, Matrix.zero_apply]; split_ifs <;> rfl

theorem Pg_mem {X : Mat k r} (hX : X ∈ lieN k r) (p : ℕ) : Pg p X ∈ lieN k r := by
  refine ⟨fun i j hij => ?_, ?_⟩
  · rw [Pg_apply]
    split_ifs with h
    · exact hX.1 i j hij
    · rfl
  · have := congrArg (Pg p) hX.2
    rw [Pg_add, Pg_adjH, Pg_zero] at this
    exact this

def PgL (p : ℕ) : Mat k r →ₗ[ℝ] Mat k r where
  toFun := Pg p
  map_add' := Pg_add p
  map_smul' := Pg_smul p

def nP (p : ℕ) : Submodule ℝ (Mat k r) := (lieNS k r).map (PgL p)

theorem nP_le_nW (p : ℕ) : nP (k := k) (r := r) p ≤ lieNS k r := by
  rintro _ ⟨X, hX, rfl⟩
  exact Pg_mem hX p

theorem Pg_of_mem_nP {p q : ℕ} {Y : Mat k r} (hY : Y ∈ nP (k := k) (r := r) p) :
    Pg q Y = if p = q then Y else 0 := by
  obtain ⟨X, _, rfl⟩ := hY
  exact Pg_Pg p q X

abbrev Ix (k r : ℕ) := Σ p : Fin (2 * r + 1), Fin (Module.finrank ℝ (nP (k := k) (r := r) p))

def bs (p : Fin (2 * r + 1)) : Module.Basis (Fin (Module.finrank ℝ (nP (k := k) (r := r) p))) ℝ (nP (k := k) (r := r) p) :=
  Module.finBasis ℝ _

def htI (i : Ix k r) : ℕ := i.1.val

def bv (i : Ix k r) : Mat k r := ((bs i.1 i.2 : nP (k := k) (r := r) i.1) : Mat k r)

theorem bv_mem (i : Ix k r) : bv i ∈ nP (k := k) (r := r) i.1 := (bs i.1 i.2).2

def Lc : (Ix k r → ℝ) →ₗ[ℝ] Mat k r := ∑ i : Ix k r, (LinearMap.proj i).smulRight (bv i)

theorem Lc_apply (x : Ix k r → ℝ) : Lc x = ∑ i, x i • bv i := by
  simp [Lc, LinearMap.sum_apply]

theorem Lc_mem (x : Ix k r → ℝ) : Lc x ∈ lieN k r := by
  rw [Lc_apply]
  exact Submodule.sum_mem (lieNS k r) fun i _ => Submodule.smul_mem _ _ (nP_le_nW _ (bv_mem i))

theorem Pg_Lc (q : Fin (2 * r + 1)) (x : Ix k r → ℝ) :
    Pg q.val (Lc x) = ∑ a, x ⟨q, a⟩ • bv (⟨q, a⟩ : Ix k r) := by
  rw [Lc_apply]
  have : Pg q.val (∑ i, x i • bv i) = PgL q.val (∑ i, x i • bv (k := k) (r := r) i) := rfl
  rw [this, map_sum]
  simp only [map_smul]
  have e : ∀ i : Ix k r, PgL q.val (bv i) = if i.1 = q then bv i else 0 := by
    intro i
    show Pg q.val (bv i) = _
    rw [Pg_of_mem_nP (bv_mem i)]
    by_cases h : i.1 = q
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (fun e => h (Fin.ext e)), if_neg h]
  simp only [e, smul_ite, smul_zero]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single q]
  · simp
  · intro p _ hp; simp [hp]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem Fil_Lc_iff (p : ℕ) (v : Ix k r → ℝ) : Fil p (Lc v) ↔ ∀ i, htI i < p → v i = 0 := by
  constructor
  · intro h i hi
    obtain ⟨q, a⟩ := i
    have h0 : Pg q.val (Lc v) = 0 := Pg_of_Fil (h.mono (by unfold htI at hi; simp at hi; omega))
    rw [Pg_Lc] at h0
    have h1 : (∑ b, v ⟨q, b⟩ • (bs (k := k) (r := r) q b)) = 0 := by
      apply Subtype.ext
      simpa [bv] using h0
    exact Fintype.linearIndependent_iff.1 (bs q).linearIndependent _ h1 a
  · intro h a b hab
    rw [Lc_apply, Matrix.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : htI i < p
    · rw [h i hi, zero_smul, Matrix.zero_apply]
    · have hY : bv i = Pg i.1.val (bv i) := by rw [Pg_of_mem_nP (bv_mem i), if_pos rfl]
      rw [Matrix.smul_apply, hY, Pg_apply, if_neg (by unfold htI at hi; omega), smul_zero]

theorem Lc_injective : Function.Injective (Lc (k := k) (r := r)) := by
  intro x y h
  have : Fil (2 * r + 1) (Lc (x - y)) := by rw [map_sub, h, sub_self]; exact Fil.zero _
  funext i
  have := (Fil_Lc_iff _ _).1 this i (by unfold htI; exact i.1.isLt)
  simpa [sub_eq_zero] using this

theorem sum_Pg {X : Mat k r} (hX : Fil 0 X) : ∑ q : Fin (2 * r + 1), Pg q.val X = X := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Pg_apply]
  by_cases h : dg k r i ≤ dg k r j
  · have hb := dg_le (k := k) (r := r) j
    rw [Finset.sum_eq_single ⟨dg k r j - dg k r i, by omega⟩]
    · rw [if_pos (by simp; omega)]
    · intro q _ hq
      rw [if_neg]
      intro e; apply hq; ext; simp; omega
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [hX i j (by omega)]
    exact Finset.sum_eq_zero fun q _ => by split_ifs <;> rfl

theorem Lc_surj {X : Mat k r} (hX : X ∈ lieN k r) : ∃ x, Lc x = X := by
  have hm : ∀ q : Fin (2 * r + 1), Pg q.val X ∈ nP (k := k) (r := r) q := fun q => ⟨X, hX, rfl⟩
  refine ⟨fun i => (bs i.1).repr ⟨Pg i.1.val X, hm i.1⟩ i.2, ?_⟩
  rw [Lc_apply, Fintype.sum_sigma]
  conv_rhs => rw [← sum_Pg (hX.1.mono (Nat.zero_le 1))]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h2 := congrArg (fun y : nP (k := k) (r := r) q => (y : Mat k r)) ((bs q).sum_repr ⟨Pg q.val X, hm q⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  exact h2

end Formalism.MainNotions.BridgeCSB

end

section

set_option linter.style.haveILetI false

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace Formalism.MainNotions.BridgeCSB

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

def Ex (x : Ix k r → ℝ) : Mt k r := fun i j => NormedSpace.exp (Lc x) i j

section Cont

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem continuous_Ex : Continuous (Ex (k := k) (r := r)) := by
  have h1 : Continuous fun x : Ix k r → ℝ => Lc (k := k) (r := r) x := LinearMap.continuous_of_finiteDimensional _
  have h2 : Continuous fun M : Mat k r => NormedSpace.exp M := NormedSpace.exp_continuous
  exact h2.comp h1

end Cont

theorem of_Ex (x : Ix k r → ℝ) : Matrix.of (Ex x) = NormedSpace.exp (Lc x) := rfl

theorem Ex_mem (x : Ix k r → ℝ) : Matrix.of (Ex x) ∈ Nset k r := exp_mem_N (Lc_mem x)

theorem Ex_injective : Function.Injective (Ex (k := k) (r := r)) := by
  intro x y h
  have h' : NormedSpace.exp (Lc x) = NormedSpace.exp (Lc (k := k) (r := r) y) := by
    rw [← of_Ex, ← of_Ex, h]
  exact Lc_injective (exp_injOn (Lc_mem x).1 (Lc_mem y).1 h')

theorem Ex_surj {m : Mt k r} (hm : Matrix.of m ∈ Nset k r) : ∃ x, Ex x = m := by
  obtain ⟨X, hX, he⟩ := exp_surj hm
  obtain ⟨x, rfl⟩ := Lc_surj hX
  exact ⟨x, by funext i j; exact congrFun (congrFun he i) j⟩

theorem exists_Einv : ∃ E' : Mt k r → (Ix k r → ℝ), Measurable E' ∧ E' ∘ Ex = id :=
  (continuous_Ex.measurableEmbedding Ex_injective).exists_measurable_extend measurable_id fun _ => ⟨0⟩

theorem shear_translate {n0 : Mat k r} (hn0 : n0 ∈ Nset k r) (T : (Ix k r → ℝ) → (Ix k r → ℝ))
    (hT : ∀ x, Ex (T x) = lmulM n0 (Ex x)) (i : Ix k r) (x y : Ix k r → ℝ)
    (hxy : ∀ j, htI j < htI i → x j = y j) : T x i - x i = T y i - y i := by
  set p := htI i
  have hXY : Fil p (Lc x - Lc y) := by
    rw [← map_sub, Fil_Lc_iff]
    intro j hj; simp [hxy j hj]
  have eX : NormedSpace.exp (Lc (T x)) = n0 * NormedSpace.exp (Lc x) := by rw [← of_Ex, hT]; rfl
  have eY : NormedSpace.exp (Lc (T y)) = n0 * NormedSpace.exp (Lc y) := by rw [← of_Ex, hT]; rfl
  have hX := (Lc_mem x).1
  have hY := (Lc_mem y).1
  have hX' := (Lc_mem (T x)).1
  have hY' := (Lc_mem (T y)).1
  have h1 := Fil.exp_sub_exp hX hY hXY
  have h2 : Fil p (NormedSpace.exp (Lc x) - NormedSpace.exp (Lc y)) := by
    have := (h1.mono (Nat.le_succ p)).add hXY
    simpa using this
  have hn1 : Fil 1 (n0 - 1) := ((mem_N_iff n0).1 hn0).2
  have h4 : Fil (p + 1) ((n0 - 1) * (NormedSpace.exp (Lc x) - NormedSpace.exp (Lc y))) := by
    have := hn1.mul h2; rwa [add_comm] at this
  have h3 : NormedSpace.exp (Lc (T x)) - NormedSpace.exp (Lc (T y)) =
      (NormedSpace.exp (Lc x) - NormedSpace.exp (Lc y)) + (n0 - 1) * (NormedSpace.exp (Lc x) - NormedSpace.exp (Lc y)) := by
    rw [eX, eY, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub]; abel
  have h5 : Fil p (NormedSpace.exp (Lc (T x)) - NormedSpace.exp (Lc (T y))) := by
    rw [h3]; exact h2.add (h4.mono (Nat.le_succ p))
  have h6 := Fil.of_exp hX' hY' h5
  have h7 := Fil.exp_sub_exp hX' hY' h6
  have h8 : Fil (p + 1) (Lc (((T x) - x) - ((T y) - y))) := by
    have e : Lc (((T x) - x) - ((T y) - y)) =
        ((NormedSpace.exp (Lc x) - NormedSpace.exp (Lc y) - (Lc x - Lc y)) +
          (n0 - 1) * (NormedSpace.exp (Lc x) - NormedSpace.exp (Lc y))) -
        ((NormedSpace.exp (Lc (T x)) - NormedSpace.exp (Lc (T y))) - (Lc (T x) - Lc (T y))) := by
      rw [h3]; simp only [map_sub]; abel
    rw [e]
    exact (h1.add h4).sub h7
  have := (Fil_Lc_iff (p + 1) _).1 h8 i (Nat.lt_succ_self p)
  simp only [Pi.sub_apply] at this
  linarith

def nuN (k r : ℕ) : Measure (Mt k r) := (volume : Measure (Ix k r → ℝ)).map Ex

theorem isHaarOn_nuN : IsHaarOn (Nset k r) (nuN k r) := by
  obtain ⟨E', hE'm, hE'⟩ := exists_Einv (k := k) (r := r)
  have mEx : Measurable (Ex (k := k) (r := r)) := continuous_Ex.measurable
  have hback : (nuN k r).map E' = volume := by
    rw [nuN, Measure.map_map hE'm mEx, hE', Measure.map_id]
  refine ⟨SigmaFinite.of_map _ hE'm.aemeasurable (by rw [hback]; infer_instance), ?_, ?_, ?_⟩
  · intro h
    have h1 : (nuN k r) Set.univ = 0 := by rw [h]; rfl
    rw [nuN, Measure.map_apply mEx MeasurableSet.univ, Set.preimage_univ] at h1
    exact (Measure.measure_univ_ne_zero.2 (NeZero.ne _)) h1
  · have hm : MeasurableSet {x : Mt k r | Matrix.of x ∉ Nset k r} := isClosed_N.measurableSet.compl
    rw [nuN, Measure.map_apply mEx hm]
    have : Ex ⁻¹' {x : Mt k r | Matrix.of x ∉ Nset k r} = ∅ := by
      ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Ex_mem x
    rw [this, measure_empty]
  · intro n0 hn0
    have hsurj : ∀ x, ∃ y, Ex y = lmulM n0 (Ex x) := fun x =>
      Ex_surj (mem_n_mul hn0 (Ex_mem x))
    let T : (Ix k r → ℝ) → (Ix k r → ℝ) := fun x => E' (lmulM n0 (Ex x))
    have hT : ∀ x, Ex (T x) = lmulM n0 (Ex x) := by
      intro x
      obtain ⟨y, hy⟩ := hsurj x
      have : T x = y := by
        show E' (lmulM n0 (Ex x)) = y
        rw [← hy]; exact congrFun hE' y
      rw [this, hy]
    have hTm : Measurable T := hE'm.comp ((continuous_lmulM n0).measurable.comp mEx)
    have hmp : MeasurePreserving T volume volume :=
      shearMP (Ix k r) htI T hTm (shear_translate hn0 T hT)
    rw [nuN, Measure.map_map (continuous_lmulM n0).measurable mEx]
    have e : lmulM n0 ∘ Ex = Ex ∘ T := by funext x; exact (hT x).symm
    rw [e, ← Measure.map_map mEx hTm, hmp.map_eq]

end Formalism.MainNotions.BridgeCSB

end

section

set_option linter.style.haveILetI false

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace Formalism.MainNotions.BridgeCSB

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

open MeasureTheory.Measure

theorem continuous_unrealify' (m : ℕ) : Continuous (unrealify (m := m)) := by
  refine continuous_matrix fun i j => ?_
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin m × Fin m × Bool) => x (i, j, false) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (i, j, false)).continuous
  have h2 : Continuous fun x : EuclideanSpace ℝ (Fin m × Fin m × Bool) => x (i, j, true) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (i, j, true)).continuous
  have : (fun x : EuclideanSpace ℝ (Fin m × Fin m × Bool) => unrealify x i j) =
      fun x => ((x (i, j, false) : ℝ) : ℂ) + ((x (i, j, true) : ℝ) : ℂ) * Complex.I := by
    funext x
    apply Complex.ext <;> simp [unrealify]
  rw [this]
  exact (Complex.continuous_ofReal.comp h1).add ((Complex.continuous_ofReal.comp h2).mul continuous_const)

section Cont2

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem continuous_expLie (S : Set (Mat k r)) :
    Continuous fun x : lieE S => (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j : Mt k r) := by
  have h2 : Continuous fun M : Mat k r => NormedSpace.exp M := NormedSpace.exp_continuous
  exact h2.comp ((continuous_unrealify' _).comp continuous_subtype_val)

end Cont2

def RL : Mat k r →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) where
  toFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  map_add' X Y := by
    ext p
    rcases p with ⟨i, j, b⟩
    cases b <;> simp [realifyFun]
  map_smul' c X := by
    ext p
    rcases p with ⟨i, j, b⟩
    cases b <;> simp [realifyFun]

theorem unrealify_RL (X : Mat k r) : unrealify (RL X) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, RL, realifyFun]

theorem lieE_N : lieE (Nset k r) = (lieNS k r).map RL := by
  unfold lieE
  rw [lieOf_N]
  have : (fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieN k r = (RL : Mat k r → _) '' (lieNS k r : Set (Mat k r)) := rfl
  rw [this, Submodule.span_image, Submodule.span_eq]

theorem RL_injective : Function.Injective (RL (k := k) (r := r)) := fun X Y h => by
  rw [← unrealify_RL X, ← unrealify_RL Y, h]

def eL : (Ix k r → ℝ) →ₗ[ℝ] lieE (Nset k r) :=
  (RL ∘ₗ Lc).codRestrict (lieE (Nset k r)) fun x => by rw [lieE_N]; exact ⟨Lc x, Lc_mem x, rfl⟩

theorem eL_bijective : Function.Bijective (eL (k := k) (r := r)) := by
  constructor
  · intro x y h
    have := congrArg Subtype.val h
    exact Lc_injective (RL_injective this)
  · rintro ⟨y, hy⟩
    rw [lieE_N] at hy
    obtain ⟨X, hX, rfl⟩ := hy
    obtain ⟨x, rfl⟩ := Lc_surj hX
    exact ⟨x, rfl⟩

theorem IsHaarOn.smul_nnreal {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) {a : ℝ≥0} (ha : a ≠ 0) :
    IsHaarOn S (a • μ) := by
  have := h.1
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · intro h0
    have h1 : (a • μ) Set.univ = 0 := by rw [h0]; rfl
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact ha (by exact_mod_cast h1)
    · exact h.2.1 (Measure.measure_univ_eq_zero.1 h1)
  · rw [Measure.smul_apply, h.2.2.1, smul_zero]
  · intro s hs
    rw [Measure.map_smul, h.2.2.2 s hs]

theorem haarLie_N_eq : ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ κ : ℝ≥0∞, haarLie (Nset k r) κ = κ • (c • nuN k r) := by
  let E := (LinearEquiv.ofBijective (eL (k := k) (r := r)) eL_bijective).toContinuousLinearEquiv
  have hE : IsAddHaarMeasure ((volume : Measure (Ix k r → ℝ)).map E) := E.isAddHaarMeasure_map _
  set c := addHaarScalarFactor ((volume : Measure (Ix k r → ℝ)).map E) (volume : Measure (lieE (Nset k r))) with hc
  have hcpos : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hμ : (volume : Measure (Ix k r → ℝ)).map E = c • (volume : Measure (lieE (Nset k r))) :=
    isAddLeftInvariant_eq_smul _ _
  let F : lieE (Nset k r) → Mt k r := fun x => fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j
  have hFE : F ∘ E = Ex := by
    funext x
    show (fun i j => NormedSpace.exp (unrealify (RL (Lc x))) i j) = Ex x
    rw [unrealify_RL]; rfl
  have hFm : Measurable F := (continuous_expLie (Nset k r)).measurable
  refine ⟨c⁻¹, inv_ne_zero hcpos.ne', fun κ => ?_⟩
  have h2 : (volume : Measure (lieE (Nset k r))).map F = c⁻¹ • nuN k r := by
    have h3 : ((volume : Measure (Ix k r → ℝ)).map E).map F = nuN k r := by
      rw [Measure.map_map hFm E.continuous.measurable, hFE]; rfl
    rw [hμ, Measure.map_smul] at h3
    rw [← h3, smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
  rw [← h2]
  rfl

end Formalism.MainNotions.BridgeCSB

end

section

open MeasureTheory
open scoped ENNReal NNReal

namespace Formalism.MainNotions.BridgeCSB

open Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem haarLieN : HaarLieN := by
  intro k r κ h0 htop
  obtain ⟨c, hc, he⟩ := haarLie_N_eq (k := k) (r := r)
  rw [he κ]
  have e : κ • (c • nuN k r) = (κ.toNNReal * c) • nuN k r := by
    ext s _
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal htop]
    ring
  rw [e]
  refine IsHaarOn.smul_nnreal (isHaarOn_nuN (k := k) (r := r)) (mul_ne_zero ?_ hc)
  intro h
  exact h0 ((ENNReal.toNNReal_eq_zero_iff κ).1 h |>.resolve_right htop)

end Formalism.MainNotions.BridgeCSB

end

section

open MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.BridgeCSB

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.BasicNotions

theorem muSHaar_of (D : D7) : Formalism.MainNotions.S.Bridge.MuSHaar D := by
  intro τ w w' θ W hW
  obtain ⟨_, _, hz, _, _, _, hG, hUW, _, _, _, hN, hQ, _⟩ := hW
  have hκtop : kapN D θ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hκ0 : kapN D θ ≠ 0 := by
    intro h0
    have hμN : W.μN = 0 := by rw [hN, h0]; unfold haarLie; rw [zero_smul]
    have hS : muS W.μW W.μN = 0 := by unfold muS; rw [hμN, Measure.prod_zero, Measure.map_zero]
    have h1 := hQ (fun _ => 1) measurable_const
    rw [hS] at h1
    simp at h1
    exact hG.2.1 h1
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by rw [hN]; exact haarLieN _ _ _ hκ0 hκtop
  exact haarS hz hUW hNH

def vmOfGm (V0 : ∀ r, ValMap 0 r) (Gm : Formalism.MainNotions.HereditaryPositivity.GM) : ∀ k r, ValMap k r
  | 0, r => V0 r
  | k0 + 1, r => (Gm k0 r).toValMap

end Formalism.MainNotions.BridgeCSB

end
