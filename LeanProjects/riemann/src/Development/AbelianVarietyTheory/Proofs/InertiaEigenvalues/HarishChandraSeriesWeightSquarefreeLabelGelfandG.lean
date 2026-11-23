import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvari
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionHarishChandraInductionMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionCuspidalGreenDegreeEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

namespace ProductIntervalSplit
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace CompanionTheory.Member.UnipotentCardinalityCoefficients

variable {g : ℕ} [Fact g.Prime]

theorem uni_one {N : ℕ} : IsUniUp (1 : Mt g N) := by
  intro a b
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact Matrix.one_apply_ne (ne_of_gt h)
  · subst h
    exact Matrix.one_apply_eq a

theorem entN_one {N : ℕ} (i j : ℕ) (h : i < j) : entN (1 : Mt g N) i j = 0 := by
  unfold entN
  split_ifs with hij
  · apply Matrix.one_apply_ne
    intro he
    have := congrArg Fin.val he
    simp only at this
    omega
  · rfl

private theorem card_filter_Gn_eq_card_filter_Mt_of_unipotent {N : ℕ} (P : Mt g N → Prop) (hU : ∀ M, P M → IsUniUp M) :
    (Finset.univ.filter fun u : Gn g N => P (u : Mt g N)).card =
      (Finset.univ.filter fun M : Mt g N => P M).card := by
  apply Finset.card_bij (fun (u : Gn g N) _ => u.1)
  · intro u hu
    simpa using hu
  · intro u _ v _ h
    exact Units.ext h
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    have hdet : M.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular (fun i j hij => ((hU M hM) i j).1 hij)]
      exact Finset.prod_eq_one fun i _ => ((hU M hM) i i).2 rfl
    have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hdet]; exact isUnit_one)
    exact ⟨hu.unit, by simpa using hM, rfl⟩

private theorem card_filter_unipotent_eq_pow_card_free {N : ℕ} (Q : Fin N × Fin N → Prop) (P : Mt g N → Prop)
    (hP : ∀ M, P M ↔ IsUniUp M ∧ ∀ p : Fin N × Fin N, p.1 < p.2 → Q p → M p.1 p.2 = 0) :
    (Finset.univ.filter fun M : Mt g N => P M).card =
      g ^ (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ ¬ Q p).card := by
  set s := Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ ¬ Q p with hs
  have hmem : ∀ p, p ∈ s ↔ p.1 < p.2 ∧ ¬ Q p := fun p => by simp [s]
  let e : {M : Mt g N // P M} ≃ (s → ZMod g) :=
    { toFun := fun M p => M.1 p.1.1 p.1.2
      invFun := fun v => ⟨Matrix.of fun i j => if i = j then 1 else if h : (i, j) ∈ s then v ⟨(i, j), h⟩ else 0, by
        refine (hP _).2 ⟨fun a b => ⟨fun hab => ?_, fun hab => ?_⟩, fun p hp hq => ?_⟩
        · have h1 : a ≠ b := ne_of_gt hab
          have h2 : (a, b) ∉ s := by
            rw [hmem]
            intro h
            exact absurd (lt_trans h.1 hab) (lt_irrefl _)
          simp [Matrix.of_apply, h1, h2]
        · simp [Matrix.of_apply, hab]
        · have h1 : p.1 ≠ p.2 := ne_of_lt hp
          have h2 : (p.1, p.2) ∉ s := by
            rw [hmem]
            exact fun h => h.2 hq
          simp [Matrix.of_apply, h1, h2]⟩
      left_inv := fun M => by
        apply Subtype.ext
        ext i j
        obtain ⟨hU, hZ⟩ := (hP M.1).1 M.2
        by_cases hij : i = j
        · subst hij
          simp [Matrix.of_apply, (hU i i).2 rfl]
        · by_cases hin : (i, j) ∈ s
          · simp [Matrix.of_apply, hij, hin]
          · simp only [Matrix.of_apply, hij, hin, if_false, dif_neg, not_false_eq_true]
            rcases lt_or_gt_of_ne hij with hlt | hgt
            · have hq : Q (i, j) := by
                by_contra hq
                exact hin ((hmem _).2 ⟨hlt, hq⟩)
              exact (hZ (i, j) hlt hq).symm
            · exact ((hU i j).1 hgt).symm
      right_inv := fun v => by
        funext p
        have hp := (hmem p.1).1 p.2
        have h1 : p.1.1 ≠ p.1.2 := ne_of_lt hp.1
        simp [Matrix.of_apply, h1, p.2] }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, ZMod.card, Fintype.card_coe]

theorem card_uni {N : ℕ} (Q : Fin N × Fin N → Prop) (P : Mt g N → Prop)
    (hP : ∀ M, P M ↔ IsUniUp M ∧ ∀ p : Fin N × Fin N, p.1 < p.2 → Q p → M p.1 p.2 = 0) :
    (Finset.univ.filter fun u : Gn g N => P (u : Mt g N)).card =
      g ^ (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ ¬ Q p).card := by
  rw [card_filter_Gn_eq_card_filter_Mt_of_unipotent P (fun M hM => ((hP M).1 hM).1), card_filter_unipotent_eq_pow_card_free Q P hP]

theorem card_lt (N : ℕ) :
    (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2).card = N * (N - 1) / 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  have h : ∀ j : Fin N, (∑ i : Fin N, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    simp_rw [Fin.lt_def]
    rw [Fin.card_filter_val_lt]
    exact min_eq_right j.2.le
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

private theorem card_unipotent_upper_eq_pow' (N : ℕ) :
    (Finset.univ.filter fun u : Gn g N => IsUniUp (u : Mt g N)).card = g ^ (N * (N - 1) / 2) := by
  have h := card_uni (g := g) (N := N) (fun _ => False) IsUniUp (fun M => by simp)
  simp only [not_false_eq_true, and_true, card_lt] at h
  exact h

theorem eU_coeff_one (N : ℕ) (ψ : AddChar (ZMod g) ℂ) :
    (eU g N ψ).coeff 1 = ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ := by
  have hφ : (∑ i ∈ Finset.range (N - 1), entN (1 : Mt g N) i (i + 1)) = 0 :=
    Finset.sum_eq_zero fun i _ => entN_one i (i + 1) (Nat.lt_succ_self i)
  have h1 : (1 : Gn g N) ∈ Finset.univ.filter fun u : Gn g N => IsUniUp (u : Mt g N) := by
    simpa using (uni_one : IsUniUp (1 : Mt g N))
  unfold eU eDat
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq_of_mem' _ _ _ h1]
  simp [hφ, card_unipotent_upper_eq_pow']

theorem wh_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (fun _ : Gn g 0 => (1 : ℂ)) = 1 := by
  unfold wh tr
  rw [Finset.sum_eq_single (1 : Gn g 0)]
  · rw [eU_coeff_one]
    simp
  · intro b _ hb
    exact absurd (Units.ext (Subsingleton.elim _ _)) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem isClass_mul_right {G : Type} [Group G] {α : G → ℂ} (h : IsClass α) (c : ℂ) :
    IsClass fun x => α x * c := by
  intro x y
  show α (y * x * y⁻¹) * c = α x * c
  rw [h x y]

theorem isClass_mul_left {G : Type} [Group G] {α : G → ℂ} (h : IsClass α) (c : ℂ) :
    IsClass fun x => c * α x := by
  intro x y
  show c * α (y * x * y⁻¹) = c * α x
  rw [h x y]

theorem isChar_of_irr {G : Type} [Group G] {α : G → ℂ} (h : IsIrr α) : IsChar α := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem wh_mul_left (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (α : Gn g n → ℂ) (c : ℂ) :
    wh ψ (fun x => c * α x) = c * wh ψ α := by
  unfold wh tr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem wh_hcL (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (L : List (Pc g))
    (hL : ∀ p ∈ L, IsChar p.2 ∧ wh ψ p.2 = 1) : wh ψ (hcL L (degL L)) = 1 := by
  induction L with
  | nil =>
    rw [hcL_nil]
    exact wh_zero ψ
  | cons p L ih =>
    have hp := hL p (List.mem_cons.2 (Or.inl rfl))
    have hrest : ∀ q ∈ L, IsChar q.2 ∧ wh ψ q.2 = 1 := fun q hq => hL q (List.mem_cons.2 (Or.inr hq))
    have ihL := ih hrest
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    have hclassL : IsClass (hcL L (degL L)) :=
      GlobalTheory.CharDec.isClass_of_isChar (GlobalTheory.GLqPerm.isChar_hcL L fun q hq => (hrest q hq).1)
    have hclassp : IsClass p.2 := GlobalTheory.CharDec.isClass_of_isChar hp.1
    rw [hcL_cons]
    unfold hc
    rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ p.1 (degL L) (degL (p :: L)) hdeg _
      (fun y => isClass_mul_right hclassp _) (fun x => isClass_mul_left hclassL _)]
    simp only [wh_mul_left, ihL, mul_one]
    exact hp.2

theorem prod_Icc_ne (n : ℕ) : ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hlt : 1 < g ^ i := Nat.one_lt_pow (by omega) (by omega)
  intro h
  have h' : ((g ^ i : ℕ) : ℂ) = 1 := by
    push_cast
    linear_combination h
  norm_cast at h'
  omega

theorem card_Gn (n : ℕ) : (Fintype.card (Gn g n) : ℂ) =
    (g : ℂ) ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1) := by
  rw [GlobalTheory.GLq.HcDeg.card_GL_C, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

theorem list_prod_split (L : List (Pc g))
    (hL : ∀ p ∈ L, 0 < p.1 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)) :
    (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod =
      (L.map fun p => p.2 1).prod * (L.map fun p => (g : ℂ) ^ p.1 - 1).prod := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp := hL p (List.mem_cons.2 (Or.inl rfl))
    have ih' := ih fun q hq => hL q (List.mem_cons.2 (Or.inr hq))
    simp only [List.map_cons, List.prod_cons, ih']
    have hsplit : ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1) =
        (∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)) * ((g : ℂ) ^ p.1 - 1) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_succ_top (by omega : 1 ≤ p.1)]
    rw [hsplit, ← hp.2]
    ring

private theorem prod_pow_natDegree_sub_one_cast_eq (Q : List ((ZMod g)[X] × Pc g))
    (hQ : ∀ q ∈ Q, q.1.natDegree = q.2.1) :
    ((((Q.map Prod.fst).map fun P => (g : ℝ) ^ P.natDegree - 1).prod : ℝ) : ℂ) =
      ((Q.map Prod.snd).map fun p => (g : ℂ) ^ p.1 - 1).prod := by
  induction Q with
  | nil => simp
  | cons q Q ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [Complex.ofReal_mul, ih fun r hr => hQ r (List.mem_cons.2 (Or.inr hr)),
      hQ q (List.mem_cons.2 (Or.inl rfl))]
    push_cast
    ring

end CompanionTheory.Member.UnipotentCardinalityCoefficients

open CompanionTheory.Member.UnipotentCardinalityCoefficients in
theorem CompanionTheory.Member.harishChandraSeriesWeight_squarefree_label_unipotent : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → Squarefree f → wtC L (eU g n ψ) f = 1 / ((UniqueFactorizationMonoid.normalizedFactors f).map (fun P => (g : ℝ) ^ P.natDegree - 1)).prod := by
  intro g _ L hg hG ψ hψ n f hm hn h0 hs
  obtain ⟨Q, hQ, hfac, hdeg, hset⟩ := (GlobalTheory.GLq.Label.label_main g L hg hG n).2.2 f hm hn h0 hs
  subst hdeg
  set C := hcL (Q.map Prod.snd) (degL (Q.map Prod.snd)) with hC
  have hcusp : ∀ c ∈ Q.map Prod.snd,
      IsCusp c.2 ∧ c.2 1 = ∏ i ∈ Finset.Ico 1 c.1, ((g : ℂ) ^ i - 1) := by
    intro c hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
    exact ⟨(hQ q hq).1.2.1, (hQ q hq).2⟩
  have hwh : wh ψ C = 1 := wh_hcL ψ hψ _ fun c hc =>
    ⟨isChar_of_irr (hcusp c hc).1.2.1,
      GlobalTheory.GLq.wh_cusp_eq_one g ψ hψ c.1 c.2 (hcusp c hc).1 (hcusp c hc).2⟩
  have hser : eSerC L (degL (Q.map Prod.snd)) f = zOf C := by
    unfold eSerC
    rw [hset, finsum_mem_singleton]
  have hcoef : (eU g _ ψ * zOf C).coeff 1 = C 1 / (Fintype.card (Gn g (degL (Q.map Prod.snd))) : ℂ) * wh ψ C :=
    (GlobalTheory.GLq.trIdem (Gn g _) (eU g _ ψ) C).2.2
  have hdeg1 := GlobalTheory.GLq.HcDeg.hc_degree g (Q.map Prod.snd) _ rfl
  rw [list_prod_split _ fun c hc => ⟨(hcusp c hc).1.1, (hcusp c hc).2⟩] at hdeg1
  have hA : ((Q.map Prod.snd).map fun p => p.2 1).prod ≠ 0 := by
    refine List.prod_ne_zero ?_
    intro h0'
    obtain ⟨c, hc, hc0⟩ := List.mem_map.1 h0'
    rw [(hcusp c hc).2] at hc0
    exact GlobalTheory.GLq.green_deg_ne_zero (g := g) c.1 hc0
  have hI : ∏ i ∈ Finset.Icc 1 (degL (Q.map Prod.snd)), ((g : ℂ) ^ i - 1) ≠ 0 := prod_Icc_ne _
  have hBR := prod_pow_natDegree_sub_one_cast_eq Q fun q hq => (hQ q hq).1.1.2.2.2
  set B := ((Q.map Prod.snd).map fun p => (g : ℂ) ^ p.1 - 1).prod with hBdef
  have hB : B ≠ 0 := by
    intro h
    rw [h, mul_zero, mul_zero] at hdeg1
    exact mul_ne_zero hI hA hdeg1.symm
  have hC1 : C 1 = (∏ i ∈ Finset.Icc 1 (degL (Q.map Prod.snd)), ((g : ℂ) ^ i - 1)) / B := by
    rw [eq_div_iff hB]
    apply mul_right_cancel₀ hA
    linear_combination hdeg1
  unfold wtC
  rw [hser, hcoef, hwh, eU_coeff_one, card_Gn, hC1, ← hBR, ← hfac, Multiset.map_coe, Multiset.prod_coe]
  set R := ((Q.map Prod.fst).map fun P => (g : ℝ) ^ P.natDegree - 1).prod with hRdef
  have hR : R ≠ 0 := by
    intro h
    apply hB
    rw [← hBR, h, Complex.ofReal_zero]
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : g.Prime).ne_zero
  set k := degL (Q.map Prod.snd) * (degL (Q.map Prod.snd) - 1) / 2
  have key : (∏ i ∈ Finset.Icc 1 (degL (Q.map Prod.snd)), ((g : ℂ) ^ i - 1)) / (R : ℂ) /
      ((g : ℂ) ^ k * ∏ i ∈ Finset.Icc 1 (degL (Q.map Prod.snd)), ((g : ℂ) ^ i - 1)) * 1 =
        ((1 / ((g : ℝ) ^ k * R) : ℝ) : ℂ) := by
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
    have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg0
    push_cast
    field_simp
  have key2 : ((g : ℂ) ^ k)⁻¹ = ((((g : ℝ) ^ k)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [key, key2, Complex.ofReal_re, Complex.ofReal_re]
  field_simp

end

end ProductIntervalSplit
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
theorem _root_.GlobalTheory.Adopt.harishChandraSeriesWeight_squarefree_label_gelfandGraev : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → Squarefree f → wtC L (eU g n ψ) f = 1 / ((UniqueFactorizationMonoid.normalizedFactors f).map (fun P => (g : ℝ) ^ P.natDegree - 1)).prod := by
  exact ProductIntervalSplit.CompanionTheory.Member.harishChandraSeriesWeight_squarefree_label_unipotent

end
