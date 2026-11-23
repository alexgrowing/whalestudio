import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdTsumEqTsumIndicatorEnnreal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetProdMapProductEqProdProd

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.RSnmEul

open GlobalTheory.ZEul GlobalTheory.RSnmUnf

def padInt {m n : ℕ} (_h : m ≤ n) (v : Fin m → ℤ) : Fin n → ℤ :=
  fun i => if hi : (i : ℕ) < m then v ⟨i, hi⟩ else 0

theorem padInt_injective {m n : ℕ} (h : m ≤ n) : Function.Injective (padInt h) := by
  intro v w hvw
  funext j
  have := congrFun hvw ⟨j, lt_of_lt_of_le j.2 h⟩
  simpa [padInt, j.2] using this

theorem padInt_zero {m n : ℕ} (h : m ≤ n) : padInt h (0 : Fin m → ℤ) = 0 := by
  funext i; simp only [padInt, Pi.zero_apply]; split_ifs <;> rfl

theorem padInt_valid {m n : ℕ} (h : m ≤ n) {v : Fin m → ℤ} (hv : (∀ i, 0 ≤ v i) ∧ Antitone v) :
    (∀ i, 0 ≤ padInt h v i) ∧ Antitone (padInt h v) := by
  have hnn : ∀ i, 0 ≤ padInt h v i := by
    intro i; unfold padInt; split_ifs
    · exact hv.1 _
    · exact le_rfl
  refine ⟨hnn, fun a b hab => ?_⟩
  by_cases hb : (b : ℕ) < m
  · have ha : (a : ℕ) < m := lt_of_le_of_lt hab hb
    simp only [padInt, ha, hb, dite_true]
    exact hv.2 (show (⟨a, ha⟩ : Fin m) ≤ ⟨b, hb⟩ from hab)
  · have : padInt h v b = 0 := by simp [padInt, hb]
    rw [this]; exact hnn a

theorem toNat_padInt {m n : ℕ} (h : m ≤ n) (v : Fin m → ℤ) :
    (fun i => (padInt h v i).toNat) = padNat (n := n) (fun i => (v i).toNat) := by
  funext i; simp only [padInt, padNat]; split_ifs <;> simp

theorem sum_padNat {m n : ℕ} (h : m ≤ n) (l : Fin m → ℕ) : ∑ i, padNat (n := n) l i = ∑ i, l i := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro c hc
    have : ¬ (c : ℕ) < m := fun hcm => hc ⟨⟨c, hcm⟩, Fin.ext rfl⟩
    simp [padNat, this]
  · intro i; simp [padNat, i.2]

theorem norm_rsTermNM_le (q : ℕ) (hq : 0 < q) {m n : ℕ} (h : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ)
    (v : Fin m → ℤ) :
    ‖rsTermNM q α β x v‖ ≤ (sqTerm q α x (padInt h v) + sqTerm q β x v) / 2 := by
  by_cases hv : (∀ i, 0 ≤ v i) ∧ Antitone v
  · rw [rsTermNM, if_pos hv, sqTerm, if_pos (padInt_valid h hv), sqTerm, if_pos hv, toNat_padInt h v,
      sum_padNat h, norm_mul, norm_mul, Complex.norm_conj, norm_cpow_pow q hq]
    have hw : 0 ≤ (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [mul_nonneg (sq_nonneg (‖schurAt (padNat (n := n) fun i => (v i).toNat) α‖ -
      ‖schurAt (fun i => (v i).toNat) β‖)) hw]
  · rw [rsTermNM, if_neg hv, norm_zero]
    exact div_nonneg (add_nonneg (sqTerm_nonneg _ _ _ _) (sqTerm_nonneg _ _ _ _)) zero_le_two

theorem rsTermNM_zero (q : ℕ) {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ) : rsTermNM q α β x 0 = 1 := by
  have h : (fun _ : Fin m => (0 : ℕ)) = fun i => ((0 : Fin m → ℤ) i).toNat := by funext i; simp
  have hs : schurAt (padNat (n := n) fun i => ((0 : Fin m → ℤ) i).toNat) α = 1 := by
    rw [← h]
    have : (padNat (n := n) fun _ : Fin m => (0 : ℕ)) = fun _ => 0 := padNat_zero
    rw [this, schurAt, schur_zero]; simp
  have hs' : schurAt (fun i => ((0 : Fin m → ℤ) i).toNat) β = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  rw [rsTermNM, if_pos ⟨fun i => le_rfl, antitone_const⟩, hs, hs']
  simp

theorem rsTermNM_partVec (q : ℕ) {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ)
    (l : {l : Fin m → ℕ // Antitone l}) :
    rsTermNM q α β x (partVec l) =
      schurAt (padNat (n := n) l.1) α * conj (schurAt l.1 β) * ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, l.1 i) := by
  rw [rsTermNM, if_pos (partVec_valid l)]
  simp [partVec]

end GlobalTheory.RSnmEul

namespace GlobalTheory.RSnmEul

open GlobalTheory.ZEul GlobalTheory.RSnmUnf

theorem hasSum_rsTermNM_local (q : ℕ) {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (x : ℝ)
    (hs : Summable fun v : Fin m → ℤ => ‖rsTermNM q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v‖) :
    HasSum (fun v => rsTermNM q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v)
      (locL q (Finset.univ.val.map α) ((Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom))
        (x : ℂ)) := by
  set β' : Fin m → ℂˣ := fun j => Units.map (starRingEnd ℂ).toMonoidHom (β j) with hβ'
  have hconj : ∀ l : Fin m → ℕ, schurAt l (fun j => (β' j : ℂ)) = conj (schurAt l fun j => (β j : ℂ)) := by
    intro l
    rw [schurAt, schurAt, MvPolynomial.eval₂_comp_left, RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ))
      (Int.castRingHom ℂ)]
    rfl
  have hpad : ∀ l : Fin m → ℕ, padTo hmn l = padNat (n := n) l := fun l => rfl
  have hm : (Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom) = Finset.univ.val.map β' :=
    Multiset.map_map _ _ _
  rw [hm]
  have hs' : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β' j : ℂ))‖ *
        ‖(q : ℂ) ^ (-(x : ℂ))‖ ^ (∑ i, l.1 i) := by
    refine (hs.comp_injective partVec_injective).congr fun l => ?_
    simp only [Function.comp, rsTermNM_partVec, hpad, hconj, norm_mul, norm_pow, Complex.norm_conj]
  have hc := cauchy_locL hmn α β' q (x : ℂ) hs'
  rw [← (partVec_injective (n := m)).hasSum_iff]
  · convert hc using 1
    funext l
    simp only [Function.comp, rsTermNM_partVec, hpad, hconj]
  · intro v hv
    by_cases hval : (∀ j, 0 ≤ v j) ∧ Antitone v
    · exact absurd (mem_range_partVec hval) hv
    · rw [rsTermNM, if_neg hval]

theorem euler_rsTermNM : ∀ {I : Type} (q : I → ℕ) {n m : ℕ}, m ≤ n → ∀ (α : I → Fin n → ℂˣ) (β : I → Fin m → ℂˣ) (x : ℝ), 1 < x →
    (∀ i, 2 ≤ q i) → GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    ∃ P : ℂ, HasProd (fun i => GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i))
        ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P ∧
      HasSum (fun l : I →₀ (Fin m → ℤ) => l.prod fun i v =>
        GlobalTheory.RSnmUnf.rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v) P := by
  intro I q n m hmn α β x _ hq hα hβ
  set f : I → (Fin m → ℤ) → ℂ := fun i v => rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v
    with hfdef
  have hf0 : ∀ i, f i 0 = 1 := fun i => rsTermNM_zero _ _ _ _
  have hA := summable_sqTerm q (fun i j => (α i j : ℂ)) x hα
  have hB := summable_sqTerm q (fun i j => (β i j : ℂ)) x hβ
  have hinj : Function.Injective fun p : I × {v : Fin m → ℤ // v ≠ 0} =>
      ((p.1, ⟨padInt hmn p.2.1, fun h0 => p.2.2 (padInt_injective hmn (h0.trans (padInt_zero hmn).symm))⟩) :
        I × {v : Fin n → ℤ // v ≠ 0}) := by
    intro p p' hp
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hp
    exact Prod.ext hp.1 (Subtype.ext (padInt_injective hmn hp.2))
  have hA' := hA.comp_injective hinj
  have hsum : Summable fun p : I × {v : Fin m → ℤ // v ≠ 0} => ‖f p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => by
        simpa only [hfdef, Function.comp_apply] using norm_rsTermNM_le (q p.1) (by have := hq p.1; omega) hmn
          (fun j => (α p.1 j : ℂ)) (fun j => (β p.1 j : ℂ)) x p.2.1) ((hA'.add hB).div_const 2)
  obtain ⟨hN, hP, -⟩ := GlobalTheory.EulerSum.euler_product_intVec m f hf0 hsum
  have hloc : ∀ i, ∑' v, f i v = locL (q i) (Finset.univ.val.map (α i))
      ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) :=
    fun i => (hasSum_rsTermNM_local (q i) hmn (α i) (β i) x (GlobalTheory.EulerSum.summable_norm_local f hsum i)).tsum_eq
  refine ⟨∑' l : I →₀ (Fin m → ℤ), l.prod f, ?_, hN.of_norm.hasSum⟩
  simpa only [hloc] using hP

end GlobalTheory.RSnmEul
