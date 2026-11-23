import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.DifferentiableUpdate
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType

noncomputable section

open scoped ContDiff
open Formalism.L2.Theta

namespace Formalism.IndefR.Tow.OrbStPf

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (ρ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)) (Lie U : Set (Matrix (Fin n) (Fin n) ℂ))

section SV

variable {ρ Lie}

lemma smoothVec_zero : SmoothVec Lie ρ 0 := by
  intro k Xs _
  simp only [map_zero]
  exact contDiff_const

lemma smoothVec_add {a b : E} (ha : SmoothVec Lie ρ a) (hb : SmoothVec Lie ρ b) : SmoothVec Lie ρ (a + b) := by
  intro k Xs hXs
  simp only [map_add]
  exact (ha k Xs hXs).add (hb k Xs hXs)

lemma smoothVec_smul (c : ℂ) {a : E} (ha : SmoothVec Lie ρ a) : SmoothVec Lie ρ (c • a) := by
  intro k Xs hXs
  simp only [map_smul]
  exact (ha k Xs hXs).const_smul c

lemma smoothVec_rsmul (c : ℝ) {a : E} (ha : SmoothVec Lie ρ a) : SmoothVec Lie ρ (c • a) := by
  rw [← Complex.coe_smul]
  exact smoothVec_smul (c : ℂ) ha

lemma mem_span_smoothVec {a : E} : a ∈ Submodule.span ℂ {w | SmoothVec Lie ρ w} ↔ SmoothVec Lie ρ a := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact smoothVec_zero
    | add x y _ _ hx hy => exact smoothVec_add hx hy
    | smul c x _ hx => exact smoothVec_smul c hx
  · intro h
    exact Submodule.subset_span h

end SV

variable {ρ Lie U}
variable (hU1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U) (hUm : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U)
  (hρ : ∀ a ∈ U, ∀ b ∈ U, ρ (a * b) = (ρ a).comp (ρ b))
  (hexp : ∀ Y ∈ Lie, ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ U)

include hU1 hUm in
lemma list_prod_mem (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ a ∈ l, a ∈ U) : l.prod ∈ U := by
  induction l with
  | nil => simpa using hU1
  | cons a l ih =>
    rw [List.prod_cons]
    exact hUm a (hl a (by simp)) _ (ih (fun b hb => hl b (by simp [hb])))

include hU1 hUm hexp in
lemma prod_drop_mem {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie) (r : Fin N → ℝ) (j : ℕ) :
    ((List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop j).prod ∈ U := by
  refine list_prod_mem hU1 hUm _ ?_
  intro a ha
  have ha' := List.mem_of_mem_drop ha
  simp only [List.mem_ofFn] at ha'
  obtain ⟨i, rfl⟩ := ha'
  exact hexp _ (hZ i) _

include hU1 hUm hρ hexp in

lemma smoothVec_rep_exp {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Lie) (s : ℝ) {w : E} (hw : SmoothVec Lie ρ w) :
    SmoothVec Lie ρ (ρ (NormedSpace.exp (s • X)) w) := by
  intro k Xs hXs
  have hX' : ∀ i, (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) i ∈ Lie := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j
  have hsn : ContDiff ℝ ∞ (fun t : Fin k → ℝ => (Fin.snoc t s : Fin (k + 1) → ℝ)) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Fin k → ℝ => s)
    · simpa using (contDiff_pi.1 contDiff_id j : ContDiff ℝ ∞ fun t : Fin k → ℝ => t j)
  have h := (hw (k + 1) (Fin.snoc Xs X) hX').comp hsn
  convert h using 1
  funext t
  simp only [Function.comp_apply]
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hP : (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ U := by
    refine list_prod_mem hU1 hUm _ (fun a ha => ?_)
    simp only [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact hexp _ (hXs i) _
  rw [hρ _ hP _ (hexp _ hX _)]
  rfl

variable (ρ) in

def orb {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (u : E) (j : ℕ) (r : Fin N → ℝ) : E :=
  ρ (((List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop j).prod) u

def mask {N : ℕ} (j : ℕ) (r : Fin N → ℝ) : Fin N → ℝ := fun i => if i.val < j then 0 else r i

lemma prod_mask {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (j : ℕ) (r : Fin N → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (mask j r i • Z i)).prod =
      ((List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop j).prod := by
  have hd : (List.ofFn fun i => NormedSpace.exp (mask j r i • Z i)).drop j =
      (List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop j := by
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.getElem_drop, List.getElem_ofFn, mask]
      rw [if_neg (by simp)]
  have ht : ((List.ofFn fun i => NormedSpace.exp (mask j r i • Z i)).take j).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    have hkj : k < j := by simp at hk; omega
    simp [List.getElem_take, mask, hkj]
  rw [← List.prod_take_mul_prod_drop (List.ofFn fun i => NormedSpace.exp (mask j r i • Z i)) j, ht, one_mul, hd]

lemma contDiff_mask {N : ℕ} (j : ℕ) : ContDiff ℝ ∞ (mask (N := N) j) := by
  refine contDiff_pi.2 fun i => ?_
  by_cases h : i.val < j
  · simp only [mask, h, if_true]
    exact contDiff_const
  · simp only [mask, h, if_false]
    exact contDiff_pi.1 contDiff_id i

lemma contDiff_orb {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie) {u : E}
    (hu : SmoothVec Lie ρ u) (j : ℕ) : ContDiff ℝ ∞ (orb ρ Z u j) := by
  have h := (hu N Z hZ).comp (contDiff_mask (N := N) j)
  convert h using 1
  funext r
  simp only [orb, Function.comp_apply, prod_mask]

include hU1 hUm hρ hexp in
lemma orb_update {N : ℕ} (Z : Fin N → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie) (u : E) (j : ℕ)
    (hj : j < N) (r : Fin N → ℝ) (s : ℝ) :
    orb ρ Z u j (Function.update r ⟨j, hj⟩ s) = ρ (NormedSpace.exp (s • Z ⟨j, hj⟩)) (orb ρ Z u (j + 1) r) := by
  simp only [orb]
  have hlen : j < (List.ofFn fun i => NormedSpace.exp (Function.update r ⟨j, hj⟩ s i • Z i)).length := by
    simpa using hj
  rw [List.drop_eq_getElem_cons hlen, List.prod_cons]
  have hdrop : (List.ofFn fun i => NormedSpace.exp (Function.update r ⟨j, hj⟩ s i • Z i)).drop (j + 1) =
      (List.ofFn fun i => NormedSpace.exp (r i • Z i)).drop (j + 1) := by
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.getElem_drop, List.getElem_ofFn]
      rw [Function.update_apply, if_neg]
      intro h
      simp only [Fin.mk.injEq] at h
      omega
  rw [hdrop, List.getElem_ofFn, Function.update_apply, if_pos rfl,
    hρ _ (hexp _ (hZ _) _) _ (prod_drop_mem hU1 hUm hexp Z hZ r (j + 1))]
  rfl

lemma orb_last {k : ℕ} (Z : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) (u : E) (r : Fin (k + 1) → ℝ) :
    orb ρ Z u k r = ρ (NormedSpace.exp (r (Fin.last k) • Z (Fin.last k))) u := by
  simp only [orb]
  rw [List.ofFn_succ', List.concat_eq_append, List.drop_left' (by simp), List.prod_singleton]

include hU1 hUm hρ hexp in
theorem word_pds {k : ℕ} (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : l.length = k)
    (Z : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie)
    (hZl : ∀ (i : Fin (k + 1)) (h : i.val < k), Z i = l[i.val]'(by omega)) :
    ∀ d j, j + d = k → ∃ L : List (Fin (k + 1)), (∀ i ∈ L, j ≤ i.val ∧ i.val < k) ∧
      ∀ u, SmoothVec Lie ρ u → ∀ r : Fin (k + 1) → ℝ, (∀ i : Fin (k + 1), j ≤ i.val → i.val < k → r i = 0) →
        (l.drop j).foldr (dRep ρ) (orb ρ Z u k r) = pds L (orb ρ Z u j) r := by
  intro d
  induction d with
  | zero =>
    intro j hj
    refine ⟨[], by simp, ?_⟩
    intro u _ r _
    obtain rfl : j = k := by omega
    have h0 : l.drop j = [] := List.drop_eq_nil_of_le (by omega)
    rw [h0, List.foldr_nil, pds_nil]
  | succ d ih =>
    intro j hj
    obtain ⟨L', hL'1, hL'2⟩ := ih (j + 1) (by omega)
    have hjk : j < k := by omega
    refine ⟨⟨j, by omega⟩ :: L', ?_, ?_⟩
    · intro i hi
      rcases List.mem_cons.1 hi with h | h
      · subst h
        exact ⟨le_refl _, hjk⟩
      · have := hL'1 i h
        exact ⟨by omega, this.2⟩
    · intro u hu r hr
      have hjl : j < l.length := by omega
      rw [List.drop_eq_getElem_cons hjl, List.foldr_cons,
        hL'2 u hu r (fun i h1 h2 => hr i (by omega) h2), pds_cons]
      have hne : ∀ i ∈ L', i ≠ (⟨j, by omega⟩ : Fin (k + 1)) := by
        intro i hi h
        have := (hL'1 i hi).1
        rw [h] at this
        simp at this
      have hF : ContDiff ℝ ∞ (pds L' (orb ρ Z u j)) := contDiff_pds L' (contDiff_orb Z hZ hu j)
      have hdiff : DifferentiableAt ℝ (pds L' (orb ρ Z u j)) r := hF.differentiable (by simp) r
      rw [pd_eq_deriv _ r hdiff]
      have hZj : Z ⟨j, by omega⟩ = l[j] := hZl ⟨j, by omega⟩ hjk
      have hfun : (fun t : ℝ => pds L' (orb ρ Z u j) (r + t • Pi.single (⟨j, by omega⟩ : Fin (k + 1)) (1 : ℝ))) =
          fun t => ρ (NormedSpace.exp (t • Z ⟨j, by omega⟩)) (pds L' (orb ρ Z u (j + 1)) r) := by
        funext t
        have hup : r + t • Pi.single (⟨j, by omega⟩ : Fin (k + 1)) (1 : ℝ) = Function.update r ⟨j, by omega⟩ t := by
          funext i
          by_cases h : i = ⟨j, by omega⟩
          · subst h
            simp [hr ⟨j, by omega⟩ (le_refl j) hjk]
          · simp [h, Pi.single_apply, Function.update_apply]
        have h1 : pds L' (orb ρ Z u j) (Function.update r ⟨j, by omega⟩ t) =
            pds L' (fun r' => orb ρ Z u j (Function.update r' ⟨j, by omega⟩ t)) r := by
          rw [pds_update L' _ hne t (contDiff_orb Z hZ hu j)]
        have h2 : (fun r' => orb ρ Z u j (Function.update r' ⟨j, by omega⟩ t)) =
            fun r' => ((ρ (NormedSpace.exp (t • Z ⟨j, by omega⟩))).restrictScalars ℝ) (orb ρ Z u (j + 1) r') := by
          funext r'
          exact orb_update hU1 hUm hρ hexp Z hZ u j (by omega) r' t
        rw [hup, h1, h2, pds_clm L' _ (contDiff_orb Z hZ hu (j + 1))]
        rfl
      (rw [hfun, hZj]) <;> rfl

lemma orb_zero_split {k : ℕ} (Z : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) (u : E) (r : Fin (k + 1) → ℝ) :
    orb ρ Z u 0 r = ρ ((List.ofFn fun i : Fin k => NormedSpace.exp (r i.castSucc • Z i.castSucc)).prod *
      NormedSpace.exp (r (Fin.last k) • Z (Fin.last k))) u := by
  simp only [orb, List.drop_zero]
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]

include hU1 hUm hρ hexp in

lemma pd_last_orb {k : ℕ} (Z : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ i, Z i ∈ Lie) {u w : E}
    (hu : SmoothVec Lie ρ u) (hd : HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • Z (Fin.last k))) u) w 0) :
    pd (Fin.last k) (orb ρ Z u 0) = orb ρ Z w 0 := by
  funext r
  have hdiff : DifferentiableAt ℝ (orb ρ Z u 0) r :=
    (contDiff_orb Z hZ hu 0).differentiable (by simp) r
  rw [pd_eq_deriv _ r hdiff]
  have hP : (List.ofFn fun i : Fin k => NormedSpace.exp (r i.castSucc • Z i.castSucc)).prod ∈ U := by
    refine list_prod_mem hU1 hUm _ (fun a ha => ?_)
    simp only [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact hexp _ (hZ _) _
  have hE : ∀ s : ℝ, NormedSpace.exp (s • Z (Fin.last k)) ∈ U := fun s => hexp _ (hZ _) _
  have hfun : (fun t : ℝ => orb ρ Z u 0 (r + t • Pi.single (Fin.last k) 1)) =
      fun t => ((ρ (List.ofFn fun i : Fin k => NormedSpace.exp (r i.castSucc • Z i.castSucc)).prod).comp
        (ρ (NormedSpace.exp (r (Fin.last k) • Z (Fin.last k))))) (ρ (NormedSpace.exp (t • Z (Fin.last k))) u) := by
    funext t
    rw [orb_zero_split]
    have hc : ∀ i : Fin k, (r + t • Pi.single (Fin.last k) (1 : ℝ) : Fin (k + 1) → ℝ) i.castSucc = r i.castSucc := by
      intro i
      simp [Pi.single_apply, Fin.castSucc_ne_last]
    have hl : (r + t • Pi.single (Fin.last k) (1 : ℝ) : Fin (k + 1) → ℝ) (Fin.last k) = r (Fin.last k) + t := by simp
    simp only [hc, hl]
    rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl (Z (Fin.last k))).smul_left _).smul_right _),
      ← mul_assoc, hρ _ (hUm _ hP _ (hE _)) _ (hE _), hρ _ hP _ (hE _)]
    rfl
  rw [hfun]
  have hD : HasDerivAt (fun t : ℝ => ((ρ (List.ofFn fun i : Fin k => NormedSpace.exp (r i.castSucc • Z i.castSucc)).prod).comp
        (ρ (NormedSpace.exp (r (Fin.last k) • Z (Fin.last k))))) (ρ (NormedSpace.exp (t • Z (Fin.last k))) u))
      (((ρ (List.ofFn fun i : Fin k => NormedSpace.exp (r i.castSucc • Z i.castSucc)).prod).comp
        (ρ (NormedSpace.exp (r (Fin.last k) • Z (Fin.last k))))) w) 0 := ((((ρ (List.ofFn fun i : Fin k => NormedSpace.exp (r i.castSucc • Z i.castSucc)).prod).comp
        (ρ (NormedSpace.exp (r (Fin.last k) • Z (Fin.last k))))).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt
        (0 : ℝ) hd
  (rw [hD.deriv, orb_zero_split, hρ _ hP _ (hE _)]) <;> rfl

include hU1 hUm hρ hexp in

lemma word_eval (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ Y ∈ l, Y ∈ Lie)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Lie) :
    ∃ (Z : Fin (l.length + 1) → Matrix (Fin n) (Fin n) ℂ) (L : List (Fin (l.length + 1))), (∀ i, Z i ∈ Lie) ∧
      Z (Fin.last _) = X ∧ ∀ v, SmoothVec Lie ρ v → ∀ t : ℝ,
        l.foldr (dRep ρ) (ρ (NormedSpace.exp (t • X)) v) = pds L (orb ρ Z v 0) (t • Pi.single (Fin.last _) 1) := by
  let Z : Fin (l.length + 1) → Matrix (Fin n) (Fin n) ℂ := fun i => if h : i.val < l.length then l[i.val] else X
  have hZ : ∀ i, Z i ∈ Lie := by
    intro i
    simp only [Z]
    split_ifs with h
    · exact hl _ (by simp)
    · exact hX
  have hZl : ∀ (i : Fin (l.length + 1)) (h : i.val < l.length), Z i = l[i.val]'(by omega) := by
    intro i h
    simp only [Z, dif_pos h]
  obtain ⟨L, -, hL⟩ := word_pds hU1 hUm hρ hexp l rfl Z hZ hZl l.length 0 (by simp)
  refine ⟨Z, L, hZ, by simp [Z], ?_⟩
  intro v hv t
  have hr : ∀ i : Fin (l.length + 1), 0 ≤ i.val → i.val < l.length →
      (t • Pi.single (Fin.last l.length) (1 : ℝ)) i = 0 := by
    intro i _ h
    have : i ≠ Fin.last _ := by
      intro h'
      rw [h'] at h
      simp at h
    simp [Pi.single_apply, this]
  have := hL v hv _ hr
  rw [List.drop_zero] at this
  rw [← this, orb_last]
  simp [Z]

include hU1 hUm hρ hexp in

theorem word_deriv (hρ1 : ρ 1 = 1) (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ Y ∈ l, Y ∈ Lie)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Lie) {u w : E} (hu : SmoothVec Lie ρ u) (hw : SmoothVec Lie ρ w)
    (hd : HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) u) w 0) :
    HasDerivAt (fun t : ℝ => l.foldr (dRep ρ) (ρ (NormedSpace.exp (t • X)) u)) (l.foldr (dRep ρ) w) 0 := by
  obtain ⟨Z, L, hZ, hZX, hL⟩ := word_eval hU1 hUm hρ hexp l hl hX
  have hfun : (fun t : ℝ => l.foldr (dRep ρ) (ρ (NormedSpace.exp (t • X)) u)) =
      fun t => pds L (orb ρ Z u 0) (0 + t • Pi.single (Fin.last _) 1) := by
    funext t
    rw [hL u hu t, zero_add]
  rw [hfun]
  have hF : ContDiff ℝ ∞ (pds L (orb ρ Z u 0)) := contDiff_pds L (contDiff_orb Z hZ hu 0)
  have h1 := pd_hasDerivAt (Fin.last _) (0 : Fin (l.length + 1) → ℝ) (hF.differentiable (by simp) 0)
  convert h1 using 1
  have hd' : HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • Z (Fin.last _))) u) w 0 := by
    rw [hZX]
    exact hd
  rw [pd_pds _ L (contDiff_orb Z hZ hu 0), pd_last_orb hU1 hUm hρ hexp Z hZ hu hd']
  have := hL w hw 0
  rw [zero_smul, zero_smul, NormedSpace.exp_zero, hρ1, ContinuousLinearMap.one_apply] at this
  exact this

include hU1 hUm hρ hexp in

theorem word_lin (hρ1 : ρ 1 = 1) (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ Y ∈ l, Y ∈ Lie)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Lie) {a b : E} (ha : SmoothVec Lie ρ a) (hb : SmoothVec Lie ρ b)
    (c : ℝ) : l.foldr (dRep ρ) (a + c • b) = l.foldr (dRep ρ) a + c • l.foldr (dRep ρ) b := by
  obtain ⟨Z, L, hZ, -, hL⟩ := word_eval hU1 hUm hρ hexp l hl hX
  have key : ∀ v, SmoothVec Lie ρ v → l.foldr (dRep ρ) v = pds L (orb ρ Z v 0) 0 := by
    intro v hv
    have := hL v hv 0
    rw [zero_smul, zero_smul, NormedSpace.exp_zero, hρ1, ContinuousLinearMap.one_apply] at this
    exact this
  have hab : SmoothVec Lie ρ (a + c • b) := smoothVec_add ha (smoothVec_rsmul c hb)
  rw [key _ hab, key _ ha, key _ hb]
  have horb : orb ρ Z (a + c • b) 0 = fun r => orb ρ Z a 0 r + c • orb ρ Z b 0 r := by
    funext r
    simp only [orb, map_add, ContinuousLinearMap.map_smul_of_tower]
  rw [horb, pds_add L (contDiff_orb Z hZ ha 0) ((contDiff_orb Z hZ hb 0).const_smul c),
    pds_smul L c (contDiff_orb Z hZ hb 0)]

end Formalism.IndefR.Tow.OrbStPf

end
