import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicPropertiStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LerayInj

theorem peel (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ)
    (hH : ∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0)
    (N : ℤ) (hN : (n : ℤ) + 1 = N)
    (c : Cochain ((chains R).obj E) (res R F) N)
    (hc : ∀ (p q : ℤ) (hpq : p + N = q), p ≠ -N → c.v p q hpq = 0)
    (β₀ : Cochain ((chains R).obj E) (res R F) n) (h₀ : δ n N β₀ = c) :
    ∀ k : ℕ, k ≤ n → ∃ β : Cochain ((chains R).obj E) (res R F) n, δ n N β = c ∧
      ∀ (p q : ℤ) (hpq : p + n = q), -(k : ℤ) < p → β.v p q hpq = 0 := by
  obtain ⟨cl, -, hcl, hcl0, -⟩ := GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F
  obtain ⟨-, -, -, -, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨β₀, h₀, fun p q hpq hp => (hpos E p (by omega)).eq_of_src _ _⟩
  | succ k ih =>
    intro hk
    obtain ⟨β, hβ, hv⟩ := ih (by omega)
    have hqk : (((n - k : ℕ) : ℤ)) = (n : ℤ) - k := by omega
    let t : (free R).obj (E.obj (op ⦋k⦌)) ⟶ (res R F).X ((n - k : ℕ) : ℤ) :=
      (chainsXIso R E k).inv ≫ β.v (-(k : ℤ)) ((n - k : ℕ) : ℤ) (by omega)
    have ht : t ≫ (res R F).d ((n - k : ℕ) : ℤ) (((n - k : ℕ) : ℤ) + 1) = 0 := by
      have e := Cochain.congr_v hβ (-(k : ℤ)) (((n - k : ℕ) : ℤ) + 1) (by omega)
      rw [δ_v n N hN β (-(k : ℤ)) (((n - k : ℕ) : ℤ) + 1) (by omega) ((n - k : ℕ) : ℤ) (-(k : ℤ) + 1)
        (by omega) rfl, hc _ _ _ (by omega), hv (-(k : ℤ) + 1) (((n - k : ℕ) : ℤ) + 1) (by omega) (by omega),
        comp_zero, smul_zero, add_zero] at e
      simp only [t, Category.assoc, e, comp_zero]
    have h0 : cl _ _ t ht = cl _ _ 0 zero_comp :=
      (hH k (n - k) (by omega) (by omega) _).trans (hcl0 _ _).symm
    obtain ⟨y, hy⟩ := ((hcl _ _ _ _ _ _).1 h0)
    rw [zero_add] at hy
    let γ : Cochain ((chains R).obj E) (res R F) ((n : ℤ) - 1) :=
      Cochain.single (p := -(k : ℤ)) (q := ((n - k : ℕ) : ℤ) - 1) ((chainsXIso R E k).hom ≫ y) ((n : ℤ) - 1)
    refine ⟨β - δ ((n : ℤ) - 1) n γ, ?_, ?_⟩
    · rw [δ_sub, δ_δ, sub_zero, hβ]
    · intro p q hpq hp
      rw [Cochain.sub_v, Cochain.δ_single _ ((n : ℤ) - 1) n (by omega) (-(k : ℤ) - 1) ((n - k : ℕ) : ℤ) (by omega) (by omega),
        Cochain.add_v, Cochain.units_smul_v]
      by_cases hpk : p = -(k : ℤ)
      · subst hpk
        obtain rfl : q = ((n - k : ℕ) : ℤ) := by omega
        rw [Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), smul_zero, add_zero]
        have hb : β.v (-(k : ℤ)) ((n - k : ℕ) : ℤ) hpq = (chainsXIso R E k).hom ≫ t := by
          simp only [t, Iso.hom_inv_id_assoc]
        rw [hb, hy, Category.assoc, sub_self]
      · rw [hv p q hpq (by omega), Cochain.single_v_eq_zero _ _ _ _ _ hpk,
          Cochain.single_v_eq_zero _ _ _ _ _ (by omega), smul_zero, add_zero, sub_zero]

end GlobalTheory.EtC.LerayInj

namespace GlobalTheory.EtC

theorem leray_inj : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
    (∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0) →
    (∀ s : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, IsCls s 0 → s = 0) ∧
    ∀ s : (free R).obj (E.obj (op ⦋n + 1⦌)) ⟶ F, IsCls s 0 →
      ∃ t : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd t = s := by
  intro R _ F E n hH
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  constructor
  · rintro s ⟨z, hz0, hz⟩
    rw [CohomologyClass.mk_eq_zero_iff] at hz0
    obtain ⟨m, hm, β, hβ⟩ := hz0
    have e := Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) 0 (by simp)
    have h1 : β.v (-((0 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
    have h2 : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) 1 = 0 := (hpos E 1 (by norm_num)).eq_of_tgt _ _
    rw [δ_v m _ hm β _ 0 _ (-1) 1 (by omega) (by omega), h1, h2, zero_comp, zero_comp, smul_zero,
      add_zero] at e
    have e' : (↑z : Cochain ((chains R).obj E) (res R F) ((0 : ℕ) : ℤ)).v (-((0 : ℕ) : ℤ)) 0 (by simp) =
        (chainsXIso R E 0).hom ≫ s ≫ resι R F := by
      rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((0 : ℕ) : ℤ)) = z.1 from rfl, hz, Cochain.single_v]
    rw [e'] at e
    have e2 : s ≫ resι R F = 0 ≫ resι R F := by
      rw [zero_comp]
      exact (cancel_epi (chainsXIso R E 0).hom).1 (by rw [← e, comp_zero])
    exact (cancel_mono (resι R F)).1 e2
  · rintro s ⟨z, hz0, hz⟩
    rw [CohomologyClass.mk_eq_zero_iff] at hz0
    obtain ⟨m, hm, β₀, hβ₀⟩ := hz0
    obtain rfl : m = (n : ℤ) := by push_cast at hm; omega
    have hzv : ∀ (p q : ℤ) (hpq : p + ((n + 1 : ℕ) : ℤ) = q),
        (↑z : Cochain ((chains R).obj E) (res R F) ((n + 1 : ℕ) : ℤ)).v p q hpq =
          (Cochain.single (p := -((n + 1 : ℕ) : ℤ)) (q := 0)
            ((chainsXIso R E (n + 1)).hom ≫ s ≫ resι R F) ((n + 1 : ℕ) : ℤ)).v p q hpq := by
      intro p q hpq
      rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((n + 1 : ℕ) : ℤ)) = z.1 from rfl, hz]
    obtain ⟨β, hβ, hv⟩ := LerayInj.peel R F E n hH ((n + 1 : ℕ) : ℤ) (by push_cast; rfl) z
      (fun p q hpq hp => by rw [hzv, Cochain.single_v_eq_zero _ _ _ _ _ hp]) β₀ hβ₀ n le_rfl

    let b := β.v (-(n : ℤ)) 0 (by omega)
    have hb : b ≫ (res R F).d 0 1 = 0 := by
      have e := Cochain.congr_v hβ (-(n : ℤ)) 1 (by push_cast; omega)
      rw [δ_v (n : ℤ) _ (by push_cast; rfl) β (-(n : ℤ)) 1 _ 0 (-(n : ℤ) + 1) (by omega) rfl,
        hv (-(n : ℤ) + 1) 1 (by omega) (by omega), comp_zero, smul_zero, add_zero, hzv,
        Cochain.single_v_eq_zero _ _ _ _ _ (by omega)] at e
      exact e
    haveI : Mono (ShortComplex.mk _ _ w).f := hmono
    let t' : ((chains R).obj E).X (-(n : ℤ)) ⟶ F := hex.lift b hb
    have ht' : t' ≫ resι R F = b := hex.lift_f b hb

    have e := Cochain.congr_v hβ (-((n + 1 : ℕ) : ℤ)) 0 (by omega)
    have h1 : β.v (-((n + 1 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
    rw [δ_v (n : ℤ) _ (by push_cast; rfl) β _ 0 _ (-1) (-(n : ℤ)) (by omega) (by push_cast; omega), h1,
      zero_comp, zero_add, hzv, Cochain.single_v] at e
    rw [show β.v (-(n : ℤ)) 0 (by omega) = b from rfl, ← ht'] at e
    have hD : ((chainsN R).obj E).d (n + 1) n =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i) :=
      AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ _
    let D : (free R).obj (E.obj (op ⦋n + 1⦌)) ⟶ (free R).obj (E.obj (op ⦋n⦌)) :=
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i)
    have hd : ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
        (chainsXIso R E (n + 1)).hom ≫ D ≫ (chainsXIso R E n).inv :=
      (HomologicalComplex.extend_d_eq _ _ rfl rfl).trans
        (congrArg (fun D' => (chainsXIso R E (n + 1)).hom ≫ D' ≫ (chainsXIso R E n).inv) hD)
    rw [hd] at e
    have hs : s = (((n + 1 : ℕ) : ℤ).negOnePow : ℤ) • (D ≫ (chainsXIso R E n).inv ≫ t') := by
      apply (cancel_epi (chainsXIso R E (n + 1)).hom).1
      apply (cancel_mono (resι R F)).1
      rw [Category.assoc, ← e]
      simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
    refine ⟨(((n + 1 : ℕ) : ℤ).negOnePow : ℤ) • ((chainsXIso R E n).inv ≫ t'), ?_⟩
    rw [hs]
    simp only [D, cobd, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum,
      smul_smul, Category.assoc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]

end GlobalTheory.EtC
