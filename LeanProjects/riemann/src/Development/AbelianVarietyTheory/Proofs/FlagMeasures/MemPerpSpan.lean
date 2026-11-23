import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StdLat

open GlobalTheory.HL.Eichler

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_zero_l (y : Fin n → E) : hf L Hm 0 y = 0 := by simp [hf]

theorem hf_zero_r (y : Fin n → E) : hf L Hm y 0 = 0 := by simp [hf]

theorem hf_sum_l {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L Hm (a i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_l]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, ih]

theorem hf_sum_r {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ i ∈ s, a i) = ∑ i ∈ s, hf L Hm y (a i) := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_r]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, ih]

theorem mem_perp_span {ι : Type} (v : ι → Fin n → E) (x : Fin n → E) :
    x ∈ perp L Hm (Submodule.span E (Set.range v)) ↔ ∀ i, hf L Hm x (v i) = 0 := by
  constructor
  · intro h i
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i
    | zero => exact hf_zero_r L Hm x
    | add a b _ _ ha hb => rw [hf_add_r, ha, hb, add_zero]
    | smul c a _ ha => rw [hf_smul_r, ha, mul_zero]

theorem exists_mul_mem (s : Finset E) :
    ∃ c : F, c ≠ 0 ∧ c ∈ 𝒪[F] ∧ ∀ x ∈ s, algebraMap F E c * x ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have h1 : ∀ x : E, ∃ c : F, c ≠ 0 ∧ c ∈ 𝒪[F] ∧ algebraMap F E c * x ∈ L.O := by
    intro x
    have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (R := 𝒪[F]) (nonZeroDivisors 𝒪[F]) x hx
    refine ⟨((m : 𝒪[F]) : F), ?_, (m : 𝒪[F]).2, ?_⟩
    · have := nonZeroDivisors.ne_zero m.2
      exact fun h => this (Subtype.ext h)
    · rw [L.O_def]
      convert hm using 1
      rw [Submonoid.smul_def, Algebra.smul_def]
      rfl
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, Subring.one_mem _, by simp⟩
  | insert a s _ ih =>
    obtain ⟨c, hc, hc', h⟩ := ih
    obtain ⟨d, hd, hd', h'⟩ := h1 a
    refine ⟨c * d, mul_ne_zero hc hd, Subring.mul_mem _ hc' hd', fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [map_mul, mul_assoc]
      exact L.O.mul_mem ((UnramOrder.algebraMap_mem_iff L c).2 hc') h'
    · rw [map_mul, mul_comm (algebraMap F E c), mul_assoc]
      exact L.O.mul_mem ((UnramOrder.algebraMap_mem_iff L d).2 hd') (h x hx)

noncomputable def pr {r : ℕ} (e es : Fin r → Fin n → E) (x : Fin n → E) : Fin n → E :=
  x - ∑ j, hf L Hm x (es j) • e j - ∑ j, hf L Hm x (e j) • es j

noncomputable def lat {r : ℕ} (e es : Fin r → Fin n → E) (A : Submodule L.O (Fin n → E)) :
    Submodule L.O (Fin n → E) :=
  Submodule.span L.O (Set.range e) ⊔
    (A ⊓ (perp L Hm (Submodule.span E (Set.range es))).restrictScalars L.O) ⊔
    Submodule.span L.O (Set.range es)

section
variable {L Hm} {r : ℕ} {e es : Fin r → Fin n → E} (hH : IsHerm L Hm)
  (hee : ∀ i j, hf L Hm (e i) (e j) = 0) (hss : ∀ i j, hf L Hm (es i) (es j) = 0)
  (hes : ∀ i j, hf L Hm (e i) (es j) = if i = j then 1 else 0)
include hH hes

theorem hse (i j : Fin r) : hf L Hm (es i) (e j) = if i = j then 1 else 0 := by
  rw [← hf_cj L hH, hes]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

include hee in
theorem pr_e (x : Fin n → E) (j : Fin r) : hf L Hm (pr L Hm e es x) (e j) = 0 := by
  simp [pr, hf_sub_l, hf_sum_l, hf_smul_l, hee, hse hH hes]

omit hH in
include hss in
theorem pr_es (x : Fin n → E) (j : Fin r) : hf L Hm (pr L Hm e es x) (es j) = 0 := by
  simp [pr, hf_sub_l, hf_sum_l, hf_smul_l, hss, hes]

omit hH hes in
theorem pr_add (x y : Fin n → E) : pr L Hm e es (x + y) = pr L Hm e es x + pr L Hm e es y := by
  simp only [pr, hf_add_l, add_smul, Finset.sum_add_distrib]
  abel

omit hH hes in
theorem pr_smul (c : E) (x : Fin n → E) : pr L Hm e es (c • x) = c • pr L Hm e es x := by
  simp only [pr, hf_smul_l, mul_smul, smul_sub, Finset.smul_sum]

omit hH hes in
theorem hf_pr_r {x : Fin n → E} (h1 : ∀ j, hf L Hm x (e j) = 0) (h2 : ∀ j, hf L Hm x (es j) = 0)
    (y : Fin n → E) : hf L Hm x (pr L Hm e es y) = hf L Hm x y := by
  simp [pr, hf_sub_r, hf_sum_r, hf_smul_r, h1, h2]

include hee hss in
theorem hf_decomp (x y : Fin n → E) :
    hf L Hm x y = ∑ j, hf L Hm x (es j) * L.cj (hf L Hm y (e j)) +
      ∑ j, hf L Hm x (e j) * L.cj (hf L Hm y (es j)) +
      hf L Hm (pr L Hm e es x) (pr L Hm e es y) := by
  rw [hf_pr_r (pr_e hH hee hes x) (pr_es hss hes x)]
  simp only [pr, hf_sub_l, hf_sum_l, hf_smul_l, hf_cj L hH]
  ring

variable {A : Submodule L.O (Fin n → E)}

include hee hss in
theorem mem_lat (hAp : ∀ x ∈ A, ∀ j, hf L Hm x (e j) = 0) (x : Fin n → E) :
    x ∈ lat L Hm e es A ↔
      (∀ j, hf L Hm x (es j) ∈ L.O) ∧ (∀ j, hf L Hm x (e j) ∈ L.O) ∧ pr L Hm e es x ∈ A := by
  have hite : ∀ (p : Prop) [Decidable p], (if p then (1 : E) else 0) ∈ L.O := fun p _ => by
    split_ifs
    exacts [L.O.one_mem, L.O.zero_mem]
  constructor
  · let P : Submodule L.O (Fin n → E) :=
      { carrier := {x | (∀ j, hf L Hm x (es j) ∈ L.O) ∧ (∀ j, hf L Hm x (e j) ∈ L.O) ∧
          pr L Hm e es x ∈ A}
        zero_mem' := by
          refine ⟨fun j => ?_, fun j => ?_, ?_⟩
          · rw [hf_zero_l]; exact L.O.zero_mem
          · rw [hf_zero_l]; exact L.O.zero_mem
          · simp [pr, hf_zero_l]
        add_mem' := by
          rintro a b ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
          refine ⟨fun j => ?_, fun j => ?_, ?_⟩
          · rw [hf_add_l]; exact L.O.add_mem (h1 j) (k1 j)
          · rw [hf_add_l]; exact L.O.add_mem (h2 j) (k2 j)
          · rw [pr_add]; exact A.add_mem h3 k3
        smul_mem' := by
          rintro c a ⟨h1, h2, h3⟩
          have hc : c • a = (c : E) • a := rfl
          refine ⟨fun j => ?_, fun j => ?_, ?_⟩
          · rw [hc, hf_smul_l]; exact L.O.mul_mem c.2 (h1 j)
          · rw [hc, hf_smul_l]; exact L.O.mul_mem c.2 (h2 j)
          · rw [hc, pr_smul]; exact A.smul_mem c h3 }
    have : lat L Hm e es A ≤ P := by
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine ⟨fun j => ?_, fun j => ?_, ?_⟩
        · rw [hes]; exact hite _
        · rw [hee]; exact L.O.zero_mem
        · simp [pr, hes, hee]
      · rintro x ⟨hx, hx'⟩
        have hx2 := (mem_perp_span L Hm es x).1 hx'
        refine ⟨fun j => ?_, fun j => ?_, ?_⟩
        · rw [hx2]; exact L.O.zero_mem
        · rw [hAp x hx]; exact L.O.zero_mem
        · simpa [pr, hx2, hAp x hx] using hx
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine ⟨fun j => ?_, fun j => ?_, ?_⟩
        · rw [hss]; exact L.O.zero_mem
        · rw [hse hH hes]; exact hite _
        · simp [pr, hss, hse hH hes]
    exact fun h => this h
  · rintro ⟨h1, h2, h3⟩
    have hx : x = ∑ j, hf L Hm x (es j) • e j + pr L Hm e es x + ∑ j, hf L Hm x (e j) • es j := by
      simp only [pr]; abel
    rw [hx]
    refine Submodule.add_mem_sup (Submodule.add_mem_sup ?_ ⟨h3, ?_⟩) ?_
    · exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ (⟨_, h1 j⟩ : L.O) (Submodule.subset_span ⟨j, rfl⟩)
    · exact (mem_perp_span L Hm es _).2 (pr_es hss hes x)
    · exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ (⟨_, h2 j⟩ : L.O) (Submodule.subset_span ⟨j, rfl⟩)

variable (hXA : ∀ x ∈ Submodule.span E (Set.range e), x ∈ A)
  (hAp : ∀ x ∈ A, ∀ j, hf L Hm x (e j) = 0)
  (hd : ∀ y, (∀ j, hf L Hm y (e j) = 0) → ((∀ x ∈ A, hf L Hm x y ∈ L.O) ↔ y ∈ A))

omit hH hes in
include hXA hAp in
theorem pr_mem {x : Fin n → E} (hx : x ∈ A) : pr L Hm e es x ∈ A := by
  simp only [pr, hAp x hx, zero_smul, Finset.sum_const_zero, sub_zero]
  exact A.sub_mem hx (hXA _ (Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)))

include hee hss hXA hAp hd in
theorem pr_mem_of (y : Fin n → E)
    (h : ∀ x ∈ A, (∀ j, hf L Hm x (es j) = 0) → hf L Hm x y ∈ L.O) : pr L Hm e es y ∈ A := by
  refine (hd _ (pr_e hH hee hes y)).1 fun x hx => ?_
  rw [hf_decomp hH hee hss hes]
  simp only [pr_e hH hee hes, pr_es hss hes, map_zero, mul_zero, Finset.sum_const_zero, zero_add]
  rw [hf_pr_r (pr_e hH hee hes x) (pr_es hss hes x), hf_pr_r (pr_e hH hee hes x) (pr_es hss hes x)]
  exact h _ (pr_mem hXA hAp hx) (pr_es hss hes x)

include hee hss hXA hAp hd in
theorem lat_isSD
    (hfg : (A ⊓ (perp L Hm (Submodule.span E (Set.range es))).restrictScalars L.O).FG) :
    IsSD L Hm (lat L Hm e es A) := by
  have hm := mem_lat hH hee hss hes hAp
  have hcj : ∀ x : E, L.cj x ∈ L.O → x ∈ L.O := fun x hx => by
    simpa [L.cj_cj] using UnramOrder.cj_mem L hx
  have he : ∀ j, e j ∈ lat L Hm e es A := fun j =>
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩))
  have hs : ∀ j, es j ∈ lat L Hm e es A := fun j =>
    Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
  have h0 : ∀ x ∈ A, (∀ j, hf L Hm x (es j) = 0) → x ∈ lat L Hm e es A := fun x hx hx' =>
    Submodule.mem_sup_left (Submodule.mem_sup_right ⟨hx, (mem_perp_span L Hm es x).2 hx'⟩)
  refine ⟨⟨((Submodule.fg_span (Set.finite_range e)).sup hfg).sup
    (Submodule.fg_span (Set.finite_range es)), ?_⟩, fun y => ⟨fun h => ?_, fun hy x hx => ?_⟩⟩
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨s, hs'⟩ := hfg
    obtain ⟨c, hc, -, hcs⟩ := exists_mul_mem L (s.image fun x => hf L Hm x y)
    have h1 : pr L Hm e es (algebraMap F E c • y) ∈ A := by
      refine pr_mem_of hH hee hss hes hXA hAp hd _ fun x hx hx' => ?_
      have hx2 : x ∈ Submodule.span L.O (s : Set (Fin n → E)) := by
        rw [hs']; exact ⟨hx, (mem_perp_span L Hm es x).2 hx'⟩
      clear hx hx'
      induction hx2 using Submodule.span_induction with
      | mem x hx =>
        rw [hf_smul_r, AlgEquiv.commutes]
        exact hcs _ (Finset.mem_image_of_mem _ hx)
      | zero => rw [hf_zero_l]; exact L.O.zero_mem
      | add a b _ _ ha hb => rw [hf_add_l]; exact L.O.add_mem ha hb
      | smul d a _ ha =>
        have hc : d • a = (d : E) • a := rfl
        rw [hc, hf_smul_l]; exact L.O.mul_mem d.2 ha
    have h2 := h0 _ h1 (pr_es hss hes _)
    have hy : y = ∑ j, hf L Hm y (es j) • e j +
        algebraMap F E c⁻¹ • pr L Hm e es (algebraMap F E c • y) + ∑ j, hf L Hm y (e j) • es j := by
      rw [pr_smul, smul_smul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_smul]
      simp only [pr]; abel
    rw [hy]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (he j))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span h2)
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs j))
  · rw [hm]
    refine ⟨fun j => hcj _ ?_, fun j => hcj _ ?_,
      pr_mem_of hH hee hss hes hXA hAp hd _ fun x hx hx' => h x (h0 x hx hx')⟩
    · rw [hf_cj L hH]; exact h _ (hs j)
    · rw [hf_cj L hH]; exact h _ (he j)
  · rw [hm] at hx hy
    rw [hf_decomp hH hee hss hes]
    refine L.O.add_mem (L.O.add_mem ?_ ?_) ((hd _ (pr_e hH hee hes y)).2 hy.2.2 _ hx.2.2)
    · exact L.O.sum_mem fun j _ => L.O.mul_mem (hx.1 j) (UnramOrder.cj_mem L (hy.2.1 j))
    · exact L.O.sum_mem fun j _ => L.O.mul_mem (hx.2.1 j) (UnramOrder.cj_mem L (hy.1 j))

include hee hss hXA hAp in
theorem mem_iff_lat (x : Fin n → E) : x ∈ A ↔ ∃ y ∈ lat L Hm e es A,
    y ∈ perp L Hm (Submodule.span E (Set.range e)) ∧ y - x ∈ Submodule.span E (Set.range e) := by
  constructor
  · intro hx
    refine ⟨pr L Hm e es x, Submodule.mem_sup_left (Submodule.mem_sup_right ⟨pr_mem hXA hAp hx,
      (mem_perp_span L Hm es _).2 (pr_es hss hes x)⟩),
      (mem_perp_span L Hm e _).2 (pr_e hH hee hes x), ?_⟩
    simp only [pr, hAp x hx, zero_smul, Finset.sum_const_zero, sub_zero, sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  · rintro ⟨y, hy, hy', hyx⟩
    have h1 := ((mem_lat hH hee hss hes hAp y).1 hy).2.2
    rw [mem_perp_span] at hy'
    simp only [pr, hy', zero_smul, Finset.sum_const_zero, sub_zero] at h1
    have h2 : y ∈ A := by
      simpa using A.add_mem h1 (hXA (∑ j, hf L Hm y (es j) • e j) (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)))
    simpa using A.sub_mem h2 (hXA _ hyx)

end

theorem exists_coef {m : ℕ} {V : Type} [AddCommGroup V] [Module E V] (g : Fin m → V) (s : Set (Fin m))
    {x : V} (hx : x ∈ Submodule.span E (g '' s)) :
    ∃ c : Fin m → E, (∀ i, i ∉ s → c i = 0) ∧ x = ∑ i, c i • g i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (by rintro rfl; exact hj hi) _, ?_⟩
    simp [Pi.single_apply]
  | zero => exact ⟨0, by simp, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, rfl⟩ := ha
    obtain ⟨d, hd, rfl⟩ := hb
    exact ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul t a _ ha =>
    obtain ⟨c, hc, rfl⟩ := ha
    exact ⟨t • c, fun i hi => by simp [hc i hi], by simp [Finset.smul_sum, mul_smul]⟩

theorem image_lt {r : ℕ} {V : Type} (g : Fin (r + 1) → V) :
    g '' {i | (i : ℕ) < r} = Set.range fun j : Fin r => g j.castSucc := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, j.2, rfl⟩

theorem stdLat_spec : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ A, S.IsInner g gs A → IsSD L S.Hm (S.stdLat g gs A) ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ S.stdLat g gs A ∧ x ∈ S.spanTo g j) ↔ x ∈ Submodule.span L.O (g '' {i | (i : ℕ) < j})) ∧ ∀ x, x ∈ A ↔ ∃ y ∈ S.stdLat g gs A, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs hg A hA
  have hH := S.herm.1
  have key : (∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0) ∧
      (∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) ∧
      ∀ i j, hf L S.Hm (gs i) (gs j) = 0 := by
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun a j => by simp [S.gram, Fin.castSucc_ne_last], S.dual, S.iso⟩
    · exact ⟨fun a j => by simp [S.gram', Fin.castSucc_ne_last], S.dual', S.iso'⟩
  obtain ⟨hge, hgs, hss⟩ := key
  set e : Fin r → S.V := fun j => g j.castSucc with he
  have hX : S.spanTo g r = Submodule.span E (Set.range e) := by
    rw [Frames.spanTo, image_lt]
  have hl : S.stdLat g gs A = lat L S.Hm e gs A := rfl
  obtain ⟨hXA, hAp, hfg, hd, hz, z', hz', hzz⟩ := hA
  rw [hX] at hXA hAp hd
  simp only [mem_perp_span] at hAp hd
  have hee : ∀ i j, hf L S.Hm (e i) (e j) = 0 := fun i j => hge _ j
  have hes : ∀ i j, hf L S.Hm (e i) (gs j) = if i = j then 1 else 0 := fun i j => by
    simp [he, hgs]
  rw [hX, hl]
  refine ⟨lat_isSD hH hee hss hes hXA hAp hd hfg, fun j _ x => ⟨?_, fun hx => ⟨?_, ?_⟩⟩,
    mem_iff_lat hH hee hss hes hXA hAp⟩
  · rintro ⟨hx, hx'⟩
    obtain ⟨c, hc, rfl⟩ := exists_coef g _ hx'
    obtain ⟨h1, -, h3⟩ := (mem_lat hH hee hss hes hAp _).1 hx
    have h4 : ∀ j, hf L S.Hm (∑ i, c i • g i) (gs j) = c j.castSucc := fun j => by
      simp [hf_sum_l, hf_smul_l, hgs]
    have h5 : ∀ j, hf L S.Hm (∑ i, c i • g i) (e j) = 0 := fun j => by
      simp [hf_sum_l, hf_smul_l, he, hge]
    have h6 : pr L S.Hm e gs (∑ i, c i • g i) = c (Fin.last r) • g (Fin.last r) := by
      simp only [pr, h4, h5, zero_smul, Finset.sum_const_zero, sub_zero]
      rw [Fin.sum_univ_castSucc]
      simp [he]
    have h7 : ∀ i, c i ∈ L.O := fun i => by
      refine Fin.lastCases ?_ (fun i => h4 i ▸ h1 i) i
      have := (hd z' (hAp z' hz')).2 hz' _ h3
      rw [h6, Frames.h, hf_smul_l] at this
      rw [Frames.h] at hzz
      rwa [hzz, mul_one] at this
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : (i : ℕ) < j
    · exact Submodule.smul_mem _ (⟨_, h7 i⟩ : L.O) (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [hc i hi, zero_smul]; exact Submodule.zero_mem _
  · refine (Submodule.span_le.2 ?_ : _ ≤ lat L S.Hm e gs A) hx
    rintro _ ⟨i, -, rfl⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Submodule.mem_sup_left (Submodule.mem_sup_right ⟨hz, (mem_perp_span L _ gs _).2 fun j => ?_⟩)
      simp [hgs, (Fin.castSucc_ne_last j).symm]
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩))
  · exact Submodule.span_subset_span L.O E _ hx

end GlobalTheory.HL.StdLat
