import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MackeyFormulaHarishChandraRestrictionInductionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionTwoBlockCuspidalEqZeroStatement

noncomputable section

namespace GlobalTheory.GLq.ResCuspProd

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem toG_coe {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  unfold toG
  rw [dif_pos x.isUnit]
  exact Units.ext rfl

theorem br_zero_eq {a : ℕ} (M : Mt g a) : br 0 a M = M := by
  funext i j
  simp only [br, entN, zero_add, i.isLt, j.isLt, and_self, dif_pos]

theorem tl_self_eq {a : ℕ} (M : Mt g a) : tl a M = M := by
  funext i j
  simp only [tl, entN, i.isLt, j.isLt, and_self, dif_pos]

theorem inPar_zero' {n : ℕ} (M : Mt g n) : InPar 0 M := fun _ _ hj _ => absurd hj (Nat.not_lt_zero _)

theorem inPar_self' {a : ℕ} (M : Mt g a) : InPar a M := fun i _ _ hi => absurd i.isLt (not_lt.2 hi)

theorem isClass_conj {G : Type} [Group G] {χ : G → ℂ} (h : IsClass χ) (x y : G) : χ (y⁻¹ * x * y) = χ x := by
  have := h x y⁻¹
  rwa [inv_inv] at this

theorem mean_of_isClass {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsClass χ) (x : G) :
    (Fintype.card G : ℂ)⁻¹ * ∑ y : G, χ (y⁻¹ * x * y) = χ x := by
  simp only [isClass_conj h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, _, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

theorem isClass_hcT (a b : ℕ) (Φ : Gn g a → Gn g b → ℂ) (n : ℕ) : IsClass (hcT a b Φ n) := by
  intro x z
  unfold hcT
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft z⁻¹) _ _ (fun y => ?_)
  have : (z⁻¹ * y)⁻¹ * x * (z⁻¹ * y) = y⁻¹ * (z * x * z⁻¹) * y := by group
  simp only [Equiv.coe_mulLeft, this]

theorem isClass_hcL (L : List (Pc g)) (n : ℕ) : IsClass (hcL L n) := by
  cases L with
  | nil => intro x y; rfl
  | cons p L =>
    rw [hcL_cons]
    unfold hc
    exact isClass_hcT _ _ _ _

theorem res_left_zero (i n : ℕ) (hi : i = 0) (χ : Gn g n → ℂ) (y₁ : Gn g i) (y₂ : Gn g n) :
    res i n χ y₁ y₂ = χ y₂ := by
  subst hi
  unfold res
  have hy : ∀ x : Gn g n, (InPar 0 (x : Mt g n) ∧ tl 0 (x : Mt g n) = (y₁ : Mt g 0) ∧
      br 0 n (x : Mt g n) = (y₂ : Mt g n)) ↔ x = y₂ := by
    intro x
    rw [br_zero_eq, Units.val_inj]
    exact ⟨fun h => h.2.2, fun h => ⟨inPar_zero' _, Subsingleton.elim _ _, h⟩⟩
  simp only [hy, zero_mul, pow_zero, inv_one, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem res_right_zero (n b : ℕ) (hb : b = 0) (χ : Gn g n → ℂ) (y₁ : Gn g n) (y₂ : Gn g b) :
    res n b χ y₁ y₂ = χ y₁ := by
  subst hb
  unfold res
  have hy : ∀ x : Gn g n, (InPar n (x : Mt g n) ∧ tl n (x : Mt g n) = (y₁ : Mt g n) ∧
      br n 0 (x : Mt g n) = (y₂ : Mt g 0)) ↔ x = y₁ := by
    intro x
    rw [tl_self_eq, Units.val_inj]
    exact ⟨fun h => h.2.1, fun h => ⟨inPar_self' _, h, Subsingleton.elim _ _⟩⟩
  simp only [hy, mul_zero, pow_zero, inv_one, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem res_mul_const (a b : ℕ) {n : ℕ} (χ : Gn g n → ℂ) (c : ℂ) (y₁ : Gn g a) (y₂ : Gn g b) :
    res a b (fun x => χ x * c) y₁ y₂ = res a b χ y₁ y₂ * c := by
  unfold res
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem res_const_mul (a b : ℕ) {n : ℕ} (χ : Gn g n → ℂ) (c : ℂ) (y₁ : Gn g a) (y₂ : Gn g b) :
    res a b (fun x => c * χ x) y₁ y₂ = c * res a b χ y₁ y₂ := by
  simp_rw [mul_comm c]
  exact res_mul_const a b χ c y₁ y₂

theorem hcT_sum {ι : Type} (s : Finset ι) (a b : ℕ) (Φ : ι → Gn g a → Gn g b → ℂ) (n : ℕ) (x : Gn g n) :
    hcT a b (fun u v => ∑ j ∈ s, Φ j u v) n x = ∑ j ∈ s, hcT a b (Φ j) n x := by
  unfold hcT
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

theorem hcT_mul_const (a b : ℕ) (Φ : Gn g a → Gn g b → ℂ) (c : ℂ) (n : ℕ) (x : Gn g n) :
    hcT a b (fun u v => Φ u v * c) n x = hcT a b Φ n x * c := by
  unfold hcT
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

theorem hcT_zero (a b : ℕ) (n : ℕ) (x : Gn g n) : hcT a b (fun (_ : Gn g a) (_ : Gn g b) => (0 : ℂ)) n x = 0 := by
  unfold hcT
  simp

theorem hcT_left_zero (i a : ℕ) (hi : i = 0) (ψ : Gn g a → ℂ) (hψ : IsClass ψ) (x : Gn g a) :
    hcT i a (fun (_ : Gn g i) v => ψ v) a x = ψ x := by
  subst hi
  unfold hcT
  simp only [inPar_zero', if_true, br_zero_eq, toG_coe]
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ]
  exact mean_of_isClass hψ x

theorem sum_subsets_fin_succ {β : Type} [AddCommMonoid β] {n : ℕ} (f : Finset (Fin (n + 1)) → β) :
    ∑ S, f S = ∑ S : Finset (Fin n),
      (f (S.map (Fin.succEmb n)) + f (insert 0 (S.map (Fin.succEmb n)))) := by
  have hu : (Finset.univ : Finset (Fin (n + 1))) =
      insert 0 (Finset.univ.map (Fin.succEmb n)) := by
    ext x; cases x using Fin.cases <;> simp
  have h0 : (0 : Fin (n + 1)) ∉ Finset.univ.map (Fin.succEmb n) := by
    simp [Fin.succ_ne_zero]
  have hp : (Finset.univ.map (Fin.succEmb n)).powerset =
      (Finset.univ : Finset (Finset (Fin n))).map (Finset.mapEmbedding (Fin.succEmb n)).toEmbedding := by
    ext t; simp [Finset.subset_map_iff, eq_comm]
  rw [← Finset.powerset_univ, hu, Finset.sum_powerset_insert h0, hp,
    Finset.sum_map, Finset.sum_map, ← Finset.sum_add_distrib]
  rfl

theorem degL_sort_map (L : List (Pc g)) (J : Finset (Fin L.length)) :
    degL ((J.sort (· ≤ ·)).map L.get) = ∑ j ∈ J, (L.get j).1 := by
  unfold degL
  rw [List.map_map, ← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  rfl

theorem degL_eq_sum (L : List (Pc g)) : degL L = ∑ j : Fin L.length, (L.get j).1 := by
  unfold degL
  rw [← Fin.sum_univ_fun_getElem]
  simp

theorem sort_map_succ (p : Pc g) (L : List (Pc g)) (J : Finset (Fin L.length)) :
    ((J.map (Fin.succEmb L.length) : Finset (Fin (p :: L).length)).sort (· ≤ ·)).map (p :: L).get =
      (J.sort (· ≤ ·)).map L.get := by
  have h : (J.sort (· ≤ ·)).map (Fin.succEmb L.length) =
      ((J.map (Fin.succEmb L.length)).sort (· ≤ ·) : List (Fin (L.length + 1))) :=
    Finset.map_sort (Fin.succEmb L.length) J (· ≤ ·) (· ≤ ·) (fun a _ b _ => by simp)
  erw [← h]
  rw [List.map_map]
  congr 1

theorem sort_insert_map_succ (p : Pc g) (L : List (Pc g)) (J : Finset (Fin L.length)) :
    ((insert 0 (J.map (Fin.succEmb L.length)) : Finset (Fin (p :: L).length)).sort (· ≤ ·)).map (p :: L).get =
      p :: (J.sort (· ≤ ·)).map L.get := by
  rw [Finset.sort_insert (· ≤ ·) (fun b _ => Fin.zero_le b) (by simp [Fin.succ_ne_zero]), List.map_cons,
    sort_map_succ]
  rfl

theorem compl_map_succ {n : ℕ} (J : Finset (Fin n)) :
    (J.map (Fin.succEmb n))ᶜ = insert 0 (Jᶜ.map (Fin.succEmb n)) := by
  ext x; cases x using Fin.cases <;> simp [Fin.succ_ne_zero]

theorem compl_insert_map_succ {n : ℕ} (J : Finset (Fin n)) :
    (insert 0 (J.map (Fin.succEmb n)))ᶜ = Jᶜ.map (Fin.succEmb n) := by
  ext x; cases x using Fin.cases <;> simp [Fin.succ_ne_zero]

theorem collapse_mid {e a b : ℕ} (ρ : Gn g e → ℂ) (hρ : IsCusp ρ) (i c d : ℕ) (h0 : 0 < i) (he : i < e)
    (R : Gn g c → Gn g d → ℂ) (x : Gn g a) (y : Gn g b) :
    hcT i c (fun y₁ y₃ => hcT (e - i) d (fun y₂ y₄ => res i (e - i) ρ y₁ y₂ * R y₃ y₄) b y) a x = 0 := by
  simp only [GlobalTheory.T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero g e i ρ hρ h0 he, zero_mul, hcT_zero]

theorem collapse_left {e a b : ℕ} (i c ei d : ℕ) (hi : i = 0) (hca : c = a) (hei : ei = e) (ρ : Gn g e → ℂ)
    {ι : Type} (s : Finset ι) (F G : ι → (n : ℕ) → Gn g n → ℂ) (hF : ∀ j n, IsClass (F j n))
    (x : Gn g a) (y : Gn g b) :
    hcT i c (fun y₁ y₃ => hcT ei d (fun y₂ y₄ => res i ei ρ y₁ y₂ * ∑ j ∈ s, F j c y₃ * G j d y₄) b y) a x =
      ∑ j ∈ s, F j a x * hc e d ρ (G j d) b y := by
  subst i; subst c; subst ei
  simp only [res_left_zero 0 e rfl]
  have key : ∀ y₃ : Gn g a, hcT e d (fun y₂ y₄ => ρ y₂ * ∑ j ∈ s, F j a y₃ * G j d y₄) b y =
      ∑ j ∈ s, hc e d ρ (G j d) b y * F j a y₃ := by
    intro y₃
    have : (fun (y₂ : Gn g e) (y₄ : Gn g d) => ρ y₂ * ∑ j ∈ s, F j a y₃ * G j d y₄) =
        fun y₂ y₄ => ∑ j ∈ s, (ρ y₂ * G j d y₄) * F j a y₃ := by
      funext y₂ y₄
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hcT_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hcT_mul_const]; rfl
  simp only [key]
  refine (hcT_left_zero 0 a rfl (fun y₃ => ∑ j ∈ s, hc e d ρ (G j d) b y * F j a y₃) ?_ x).trans ?_
  · intro u v
    simp only [hF _ _ u v]
  · exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem collapse_right {e a b : ℕ} (c ei d : ℕ) (hei : ei = 0) (hd : d = b) (ρ : Gn g e → ℂ)
    {ι : Type} (s : Finset ι) (F G : ι → (n : ℕ) → Gn g n → ℂ) (hG : ∀ j n, IsClass (G j n))
    (x : Gn g a) (y : Gn g b) :
    hcT e c (fun y₁ y₃ => hcT ei d (fun y₂ y₄ => res e ei ρ y₁ y₂ * ∑ j ∈ s, F j c y₃ * G j d y₄) b y) a x =
      ∑ j ∈ s, hc e c ρ (F j c) a x * G j b y := by
  subst ei; subst d
  simp only [res_right_zero e 0 rfl]
  have key : ∀ (y₁ : Gn g e) (y₃ : Gn g c),
      hcT 0 b (fun (_ : Gn g 0) y₄ => ρ y₁ * ∑ j ∈ s, F j c y₃ * G j b y₄) b y =
        ∑ j ∈ s, (ρ y₁ * F j c y₃) * G j b y := by
    intro y₁ y₃
    refine (hcT_left_zero 0 b rfl (fun y₄ => ρ y₁ * ∑ j ∈ s, F j c y₃ * G j b y₄) ?_ y).trans ?_
    · intro u v
      simp only [hG _ _ u v]
    · simp only [Finset.mul_sum, mul_assoc]
  simp only [key]
  rw [hcT_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [hcT_mul_const]; rfl

theorem main : ∀ (g : ℕ) [Fact g.Prime] (L : List (Pc g)) (a b : ℕ), degL L = a + b → (∀ p ∈ L, IsCusp p.2) →
    ∀ x y, res a b (hcL L (a + b)) x y =
      ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ i ∈ I, (L.get i).1 = a),
        hcL ((I.sort (· ≤ ·)).map L.get) a x * hcL ((Iᶜ.sort (· ≤ ·)).map L.get) b y := by
  intro g _ L
  induction L with
  | nil =>
    intro a b hdeg _ x y
    have hab : a + b = 0 := by simpa [degL] using hdeg.symm
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    rw [hcL_nil, res_left_zero 0 (0 + 0) rfl (fun _ => (1 : ℂ)) x y]
    have h0 : ∀ l : List (Fin 0), l.map ([] : List (Pc g)).get = [] := by
      intro l
      cases l with
      | nil => rfl
      | cons i _ => exact i.elim0
    simp [h0, hcL_nil]
  | cons p L ih =>
    intro a b hdeg hcusp x y
    obtain ⟨e, ρ⟩ := p
    have hdeg' : e + degL L = a + b := by simpa [degL] using hdeg
    have hρ : IsCusp ρ := hcusp ⟨e, ρ⟩ List.mem_cons_self
    have hL : ∀ p ∈ L, IsCusp p.2 := fun p hp => hcusp p (List.mem_cons_of_mem _ hp)
    have hρc : IsClass ρ := isClass_of_isIrr hρ.2.1
    have he0 : 0 < e := hρ.1
    rw [hcL_cons]
    unfold hc
    rw [GlobalTheory.T.mackey_formula_harishChandra_restriction_induction g e (degL L) a b (a + b) hdeg'.symm rfl (fun u v => ρ u * hcL L (degL L) v)
      (fun v u w => by simp only [hρc u w]) (fun u v w => by simp only [isClass_hcL L (degL L) v w]) x y]
    simp only [res_const_mul, res_mul_const]
    set S := (Finset.range (e + 1)).filter (fun i => i ≤ a ∧ a - i ≤ degL L) with hS
    rw [← Finset.sum_filter_add_sum_filter_not S (fun i => i = 0),
      ← Finset.sum_filter_add_sum_filter_not (S.filter fun i => ¬ i = 0) (fun i => i = e)]
    rw [Finset.sum_eq_zero (s := (S.filter fun i => ¬ i = 0).filter fun i => ¬ i = e), add_zero]
    swap
    · intro i hi
      simp only [hS, Finset.mem_filter, Finset.mem_range] at hi
      exact collapse_mid ρ hρ i (a - i) (degL L - (a - i)) (by omega) (by omega) _ x y
    rw [Finset.filter_eq', Finset.filter_eq']
    rw [Finset.sum_filter]
    erw [sum_subsets_fin_succ]
    rw [Finset.sum_add_distrib]
    have hget : ∀ j : Fin L.length, (⟨e, ρ⟩ :: L).get (Fin.succEmb L.length j) = L.get j := fun j => rfl
    have hsum : ∀ J : Finset (Fin L.length), ∑ j ∈ J, (L.get j).1 ≤ degL L := fun J => by
      rw [degL_eq_sum L]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ J)
    have hcompl : ∀ J : Finset (Fin L.length), ∑ j ∈ Jᶜ, (L.get j).1 = degL L - ∑ j ∈ J, (L.get j).1 := fun J => by
      rw [degL_eq_sum L, ← Finset.sum_compl_add_sum J]
      omega
    congr 1
    · by_cases h0 : a ≤ degL L
      · rw [if_pos (by simp only [hS, Finset.mem_filter, Finset.mem_range]; omega), Finset.sum_singleton]
        have ih' := ih (a - 0) (degL L - (a - 0)) (by omega) hL
        rw [show a - 0 + (degL L - (a - 0)) = degL L by omega] at ih'
        simp only [ih']
        refine (collapse_left 0 (a - 0) (e - 0) (degL L - (a - 0)) rfl rfl rfl ρ
          (Finset.univ.filter fun I : Finset (Fin L.length) => ∑ i ∈ I, (L.get i).1 = a - 0)
          (fun (J : Finset (Fin L.length)) (n : ℕ) => hcL (List.map L.get (J.sort (· ≤ ·))) n)
          (fun (J : Finset (Fin L.length)) (n : ℕ) => hcL (List.map L.get (Jᶜ.sort (· ≤ ·))) n)
          (fun J n => isClass_hcL _ _) x y).trans ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun J _ => ?_
        simp only [Finset.sum_map, hget]
        by_cases hJ : ∑ j ∈ J, (L.get j).1 = a
        · rw [if_pos (by omega), if_pos hJ]
          erw [sort_map_succ, compl_map_succ, sort_insert_map_succ]
          rw [hcL_cons, degL_sort_map, hcompl, hJ]
          rfl
        · rw [if_neg (by omega), if_neg hJ]
      · rw [if_neg (by simp only [hS, Finset.mem_filter, Finset.mem_range]; omega), Finset.sum_empty]
        refine (Finset.sum_eq_zero fun J _ => ?_).symm
        simp only [Finset.sum_map, hget]
        rw [if_neg]
        have := hsum J
        omega
    · by_cases he : e ≤ a
      · rw [if_pos (by simp only [hS, Finset.mem_filter, Finset.mem_range]; omega), Finset.sum_singleton]
        have ih' := ih (a - e) (degL L - (a - e)) (by omega) hL
        rw [show a - e + (degL L - (a - e)) = degL L by omega] at ih'
        simp only [ih']
        refine (collapse_right (a - e) (e - e) (degL L - (a - e)) (Nat.sub_self e) (by omega) ρ
          (Finset.univ.filter fun I : Finset (Fin L.length) => ∑ i ∈ I, (L.get i).1 = a - e)
          (fun (J : Finset (Fin L.length)) (n : ℕ) => hcL (List.map L.get (J.sort (· ≤ ·))) n)
          (fun (J : Finset (Fin L.length)) (n : ℕ) => hcL (List.map L.get (Jᶜ.sort (· ≤ ·))) n)
          (fun J n => isClass_hcL _ _) x y).trans ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_insert (by simp [Fin.succ_ne_zero])]
        simp only [Finset.sum_map, hget]
        by_cases hJ : ∑ j ∈ J, (L.get j).1 = a - e
        · rw [if_pos hJ, if_pos (by
            show e + ∑ j ∈ J, (L.get j).1 = a
            omega)]
          erw [sort_insert_map_succ, compl_insert_map_succ, sort_map_succ]
          rw [hcL_cons, degL_sort_map, hJ]
        · rw [if_neg hJ, if_neg (by
            show ¬ e + ∑ j ∈ J, (L.get j).1 = a
            omega)]
      · rw [if_neg (by simp only [hS, Finset.mem_filter, Finset.mem_range]; omega), Finset.sum_empty]
        refine (Finset.sum_eq_zero fun J _ => ?_).symm
        rw [Finset.sum_insert (by simp [Fin.succ_ne_zero])]
        rw [if_neg]
        show ¬ e + _ = a
        omega

end GlobalTheory.GLq.ResCuspProd
