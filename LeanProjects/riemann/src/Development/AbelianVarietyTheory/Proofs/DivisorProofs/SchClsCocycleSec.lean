import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SchCls

theorem sum_neg_one_pow (p : ℕ) : ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) = if Even p then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i)]
  induction p with
  | zero => simp [Finset.sum_range_succ]
  | succ q ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd q with h | h
    · have h2 : Even (q + 1 + 1) := by rw [add_assoc]; exact h.add even_two
      simp [h, Nat.even_add_one, h2.neg_one_pow]
    · have h2 : Odd (q + 1 + 1) := by rw [add_assoc]; exact h.add_even even_two
      have h3 : Even (q + 1) := h.add_one
      simp [h3, h2.neg_one_pow, Nat.not_even_iff_odd.mpr h]

variable {R : Type} [CommRing R]

theorem face_sch {X U : Scheme.{0}} {p : ℕ} (x : Sx (sch.obj X) (p + 1) U) (i : Fin (p + 2)) : x.face i = x := rfl

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (z : Sec F U) :
    Sec.res g (Sec.res f z) = Sec.res (g ≫ f) z := by
  simp [Sec.res]

theorem map_id' {F : Shv R} {U : Scheme.{0}} (y : Sec F U) : Sec.map (𝟙 F) y = y := rfl

theorem map_units_smul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (u : ℤˣ) (y : Sec F U) :
    Sec.map φ (u • y) = u • Sec.map φ y := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem res_units_smul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (u : ℤˣ) (y : Sec F U) :
    Sec.res g (u • y) = u • Sec.res g y := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem ev_δ_sch {X : Scheme.{0}} {I : Cx R} {n k : ℤ} (hk : n + 1 = k)
    (α : Cochain ((chains R).obj (sch.obj X)) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
    (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + k = t) (x : Sx (sch.obj X) (p + 1) U) :
    ev (δ n k α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
      (if Even p then 0 else k.negOnePow • ev α p t (by omega) U x) := by
  rw [CupSpec.ev_δ_succ hk α U p s t hs ht x]
  simp only [face_sch]
  rw [← Finset.sum_smul, sum_neg_one_pow]
  split_ifs <;> simp

end GlobalTheory.EtC.SchCls

namespace GlobalTheory.EtC

open GlobalTheory.EtC.SchCls in

theorem sch_cls_cocycle_sec : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ), m + 1 = n → n + 1 = k → (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, (∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 n (by simp) U x = Sec.res x z) ∧ ∀ (p : ℕ) s h U x, ev α.1 (p + 1) s h U x = 0) ∧ ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n, Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 ∧ (CohomologyClass.mk α = 0 ↔ ∃ y : Sec (I.X m) X, Sec.map (I.d m n) y = ev α.1 0 n (by simp) X (𝟙 X)) := by
  intro R _ X I m n k hmn hnk
  refine ⟨fun z hz => ?_, fun α => ?_⟩
  · obtain ⟨a, ha⟩ := CupSpec.ev_exists (R := R) (E := sch.obj X) (I := I) (n := n)
      (fun p s h U x => if hp : p = 0 then
        Sec.map (I.XIsoOfEq (show n = s by omega)).hom (Sec.res (x : U ⟶ X) z) else 0)
      (by
        intro p s h V U g x
        by_cases hp : p = 0
        · subst hp
          simp only [dif_pos]
          erw [CupSpec.map_res, res_comp]
          rfl
        · simp only [dif_neg hp]
          exact map_zero _)
    have hc : δ n k a = 0 := by
      refine CupSpec.ev_ext _ _ fun p t ht U x => ?_
      erw [CupSpec.ev_zero]
      cases p with
      | zero =>
        have hkt : k = t := by omega
        subst hkt
        erw [CupSpec.ev_δ_zero hnk a U n k (by simp) ht x, ha]
        simp only [dif_pos, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, map_id']
        erw [← CupSpec.map_res, hz]
        exact map_zero _
      | succ p =>
        erw [ev_δ_sch hnk a U p (-((p + 1 : ℕ) : ℤ) + n) t (by omega) ht x, ha, ha]
        simp only [Nat.add_one_ne_zero, dif_neg, not_false_eq_true, map_zero, zero_add]
        split_ifs with he hp0
        · rfl
        · exact absurd (hp0 ▸ (⟨0, rfl⟩ : Even 0)) he
        · exact smul_zero _
    refine ⟨Cocycle.mk a k hnk hc, fun U x => ?_, fun p s h U x => ?_⟩
    · change ev a 0 n _ U x = _
      erw [ha]
      simp only [dif_pos, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, map_id']
    · change ev a (p + 1) s h U x = 0
      erw [ha]
      simp
  · have hδ := Cocycle.δ_eq_zero α k
    refine ⟨?_, ?_⟩
    · have h0 := CupSpec.ev_δ_zero hnk α.1 X n k (by simp) (by simp) (𝟙 X)
      erw [hδ, CupSpec.ev_zero] at h0
      exact h0.symm
    erw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α m hmn]
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨ev β 0 m (by simp) X (𝟙 X), ?_⟩
      erw [← hβ, CupSpec.ev_δ_zero hmn β X m n (by simp) (by simp)]
    · rintro ⟨y, hy⟩
      obtain ⟨b, hb⟩ := CupSpec.ev_exists (R := R) (E := sch.obj X) (I := I) (n := m)
        (fun p s h U x => if hp : p = 0 then
          Sec.map (I.XIsoOfEq (show m = s by omega)).hom (Sec.res (x : U ⟶ X) y)
          else if Even p then 0 else (-k.negOnePow) • ev α.1 (p + 1) s (by omega) U x)
        (by
          intro p s h V U g x
          by_cases hp : p = 0
          · subst hp
            simp only [dif_pos]
            erw [CupSpec.map_res, res_comp]
            rfl
          · simp only [dif_neg hp]
            split_ifs
            · exact map_zero _
            · erw [res_units_smul, CupSpec.ev_res]
              rfl)
      refine ⟨b, CupSpec.ev_ext _ _ fun p t ht U x => ?_⟩
      cases p with
      | zero =>
        have hnt : n = t := by omega
        subst hnt
        erw [CupSpec.ev_δ_zero hmn b U m n (by simp) ht x, hb]
        simp only [dif_pos, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, map_id']
        erw [← CupSpec.map_res, hy, CupSpec.ev_res]
        congr 1
      | succ p =>
        erw [ev_δ_sch hmn b U p (-((p + 1 : ℕ) : ℤ) + m) t (by omega) ht x, hb, hb]
        have hc := ev_δ_sch hnk α.1 U (p + 1) (-((p + 1 : ℕ) : ℤ) + m) t (by omega) (by omega) x
        erw [hδ, CupSpec.ev_zero] at hc
        rcases Nat.even_or_odd p with he | ho
        · have hne : ¬ Even (p + 1) := Nat.not_even_iff_odd.mpr he.add_one
          simp only [Nat.add_one_ne_zero, dif_neg, not_false_eq_true, hne, if_false, if_pos he,
            add_zero] at hc ⊢
          erw [map_units_smul, eq_neg_of_add_eq_zero_left hc.symm, smul_neg, smul_smul]
          simp [Int.units_mul_self]
        · have hne : ¬ Even p := Nat.not_even_iff_odd.mpr ho
          have hp0 : p ≠ 0 := fun h => hne (h ▸ (⟨0, rfl⟩ : Even 0))
          have hev : Even (p + 1) := ho.add_one
          simp only [Nat.add_one_ne_zero, dif_neg, not_false_eq_true, hev, if_true, hne, if_false,
            dif_neg hp0, map_zero, zero_add]
          have hkn : k.negOnePow = -n.negOnePow := by rw [← hnk, Int.negOnePow_succ]
          erw [hkn, neg_neg, smul_smul, Int.units_mul_self, one_smul]

end GlobalTheory.EtC
