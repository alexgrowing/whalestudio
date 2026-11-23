import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatRowMapEqRootExchangeOperatorTranslateStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat.DoubleStepProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]

theorem box_eq_pi (c : kˣ) : (box n c : Set (n → k)) = Set.univ.pi (fun _ => cball c) := by
  ext y; simp [mem_box, cball]

variable [MeasurableSpace k] [BorelSpace k]

theorem measurableSet_box (c : kˣ) : MeasurableSet (box n c : Set (n → k)) := by
  rw [box_eq_pi]; exact MeasurableSet.univ_pi fun _ => (isOpen_cball c).measurableSet

theorem vol_box_pos (ν : Measure k) [ν.IsAddHaarMeasure] (c : kˣ) :
    0 < ((Measure.pi fun _ : n => ν) (box n c : Set (n → k))).toReal := by
  have := secondCountable k
  rw [box_eq_pi, Measure.pi_pi]
  refine ENNReal.toReal_pos (Finset.prod_ne_zero_iff.2 fun i _ => ?_) (ENNReal.prod_ne_top fun i _ => ?_)
  · exact ((isOpen_cball c).measure_pos ν ⟨0, by simp [cball]⟩).ne'
  · exact (isCompact_cball c).measure_lt_top.ne

open Classical in
theorem integral_box (ν : Measure k) (c : kˣ) :
    ∫ u, (if u ∈ box n c then (1 : ℂ) else 0) ∂(Measure.pi fun _ : n => ν) =
      (((Measure.pi fun _ : n => ν) (box n c : Set (n → k))).toReal : ℂ) := by
  have e : (fun u : n → k => if u ∈ box n c then (1 : ℂ) else 0) = Set.indicator (box n c : Set (n → k)) fun _ => 1 := by
    funext u; simp [Set.indicator_apply]
  rw [e, integral_indicator_const _ (measurableSet_box c)]
  simp [Measure.real]

open Classical in

theorem hat_box {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (c : kˣ) :
    ∃ V : ℝ, 0 < V ∧ ∀ u, hat ψ ν (-1) (fun y : n → k => if y ∈ box n c⁻¹ then (1 : ℂ) else 0) u =
      (V : ℂ) * (if u ∈ box n c then 1 else 0) := by
  have := secondCountable k
  have hc0 : valuation k (c : k) ≠ 0 := (Valuation.ne_zero_iff _).2 c.ne_zero
  refine ⟨_, vol_box_pos (n := n) ν c⁻¹, fun u => ?_⟩
  by_cases hu : u ∈ box n c
  · rw [if_pos hu, mul_one, ← integral_box (n := n) ν c⁻¹]
    unfold hat
    congr 1
    funext y
    dsimp only
    by_cases hy : y ∈ box n c⁻¹
    · rw [if_pos hy, one_mul]
      have hm : (-1 : k) * (u ⬝ᵥ y) ∈ cball (1 : kˣ) := by
        show valuation k _ ≤ valuation k ((1 : kˣ) : k)
        rw [map_mul, Valuation.map_neg, map_one, one_mul, Units.val_one, map_one]
        refine Valuation.map_sum_le _ fun i _ => ?_
        rw [map_mul]
        calc valuation k (u i) * valuation k (y i) ≤ valuation k (c : k) * valuation k ((c⁻¹ : kˣ) : k) :=
              mul_le_mul' (hu i) (hy i)
          _ = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀ hc0]
      rw [hψ.eq_one hm]; simp
    · rw [if_neg hy, zero_mul]
  · rw [if_neg hu, mul_zero]
    obtain ⟨i, hi⟩ : ∃ i, valuation k (c : k) < valuation k (u i) := by
      by_contra hcon; push_neg at hcon; exact hu (mem_box.2 hcon)
    have hui : u i ≠ 0 := by rintro h0; simp [h0] at hi
    have hv0 : valuation k (u i) ≠ 0 := (Valuation.ne_zero_iff _).2 hui
    set x := u i * ((c⁻¹ : kˣ) : k) with hxdef
    have hx : ¬ valuation k x ≤ valuation k ((1 : kˣ) : k) := by
      intro hle
      rw [hxdef, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_one, map_one] at hle
      have : valuation k (u i) ≤ valuation k (c : k) := by
        have h2 := mul_le_mul' hle (le_refl (valuation k (c : k)))
        rwa [one_mul, mul_assoc, inv_mul_cancel₀ hc0, mul_one] at h2
      exact (not_le.2 hi) this
    obtain ⟨y, hy1, hy2⟩ : ∃ y, valuation k y ≤ valuation k x ∧ ψ y ≠ 1 := by
      by_contra hcon; push_neg at hcon; exact hx ((hψ x).1 hcon)
    set y₀ : n → k := Pi.single i (-(y / u i)) with hy₀def
    have hy₀ : y₀ ∈ box n c⁻¹ := by
      intro l
      by_cases hl : l = i
      · subst hl
        simp only [hy₀def, Pi.single_eq_same, map_neg, map_div₀]
        rw [Units.val_inv_eq_inv_val, map_inv₀]
        rw [hxdef, map_mul, Units.val_inv_eq_inv_val, map_inv₀] at hy1
        have h2 := mul_le_mul' hy1 (le_refl (valuation k (u l))⁻¹)
        rw [mul_comm (valuation k (u l)) _, mul_assoc, mul_inv_cancel₀ hv0, mul_one, ← div_eq_mul_inv] at h2
        rw [Valuation.map_neg, Valuation.map_div]; exact h2
      · simp [hy₀def, hl]
    have hχ : (-1 : k) * (u ⬝ᵥ y₀) = y := by
      rw [hy₀def, dotProduct_single]; field_simp
    set F : (n → k) → ℂ := fun y => (if y ∈ box n c⁻¹ then (1 : ℂ) else 0) * (ψ ((-1 : k) * (u ⬝ᵥ y)) : ℂ) with hF
    have hFt : ∀ z, F (y₀ + z) = (ψ y : ℂ) * F z := by
      intro z
      simp only [hF]
      rw [if_congr ((box n c⁻¹).add_mem_iff_right hy₀) rfl rfl, dotProduct_add, mul_add, AddChar.map_add_eq_mul,
        hχ, Circle.coe_mul]
      ring
    have hI := integral_add_left_eq_self (μ := Measure.pi fun _ : n => ν) F y₀
    simp_rw [hFt] at hI
    rw [integral_const_mul] at hI
    have hne : (ψ y : ℂ) ≠ 1 := fun h => hy2 (Circle.coe_inj.1 (by simpa using h))
    show ∫ z, F z ∂(Measure.pi fun _ : n => ν) = 0
    have h3 : ((ψ y : ℂ) - 1) * ∫ z, F z ∂(Measure.pi fun _ : n => ν) = 0 := by rw [sub_mul, hI]; ring
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h

end GlobalTheory.LocFlat.DoubleStepProof

noncomputable section
namespace GlobalTheory.LocFlat.DoubleStepProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rowE_inv' {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (u : n → k) :
    (rowE c p u)⁻¹ = rowE c p (-u) := by
  ext1
  change fromBlocks 1 0 (-(Matrix.of fun (l : Fin c) (s : n) => if l.val + 1 = p then u s else 0)) 1 =
    fromBlocks 1 0 (Matrix.of fun (l : Fin c) (s : n) => if l.val + 1 = p then (-u) s else 0) 1
  congr 1
  ext l s
  simp only [Matrix.neg_apply, Matrix.of_apply, Pi.neg_apply]
  split_ifs <;> simp

theorem det_rowE' {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (u : n → k) :
    Matrix.GeneralLinearGroup.det (rowE c p u) = 1 := by
  ext
  simp [rowE, lowU]

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem conj_rowE (j c : ℕ) (H : j + 1 + (c + 1) = s) (r : ℕ) (v : XIx (Fin κ) t (j + 1) → k) :
    ((typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1 + 1) (by omega))).conj.symm
      (rowE (c + 1 + 1) (r + 1) v)).val =
      (fromBlocks 1 0 (Matrix.of fun (l : Fin (c + 1 + 1)) x => if l.val = r then (((S.ϖ : k) ^ (r + 1))⁻¹ * v x) else 0) 1 :
        Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k).submatrix
        (stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1 + 1) (by omega))
        (stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1 + 1) (by omega)) := by
  set F := typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1 + 1) (by omega))
  have e : (F.bas⁻¹).val = fromBlocks 1 0 0 (diagonal fun i : Fin (c + 1 + 1) => ((S.ϖ : k) ^ (i.val + 1))⁻¹) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    change fromBlocks 1 0 0 (diagonal _) * _ = _
    simp [fromBlocks_multiply, diagonal_mul_diagonal]
  have e2 : F.bas.val = fromBlocks 1 0 0 (diagonal fun i : Fin (c + 1 + 1) => ((S.ϖ : k) ^ (i.val + 1))) := by
    change fromBlocks 1 0 0 (diagonal _) = _
    simp
  rw [LatFrame.conj, MulEquiv.symm_trans_apply, reGL_symm_val, MulAut.conj_symm_apply]
  congr 1
  rw [Units.val_mul, Units.val_mul, e, e2]
  change _ * fromBlocks 1 0 _ 1 * _ = _
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    diagonal_mul_diagonal]
  congr 1
  · ext l x
    rw [diagonal_mul]
    simp only [Matrix.of_apply]
    split_ifs with h1 h2 h2
    · rw [show l.val = r by omega]
    · omega
    · omega
    · simp
  · rw [← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _))

theorem rowE_mem_lev (hP : S.Pattern t) (j c : ℕ) (H : j + 1 + (c + 1) = s) (r : ℕ) (hc : c = 2 * r)
    (u : XIx (Fin κ) t (j + 1) → k) (hu : u ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1))) :
    rowE (c + 1 + 1) (r + 1) u ∈ ((S.T t).lev (j + 1) (c + 1 + 1) (by omega)).J := by
  have hr : r < S.ρ := by have := S.odd; omega
  set ord := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1 + 1) (by omega) with hord
  have hint : ∀ v ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1)),
      IntM (fromBlocks 1 0 (Matrix.of fun (l : Fin (c + 1 + 1)) x => if l.val = r then (((S.ϖ : k) ^ (r + 1))⁻¹ * v x) else 0) 1 :
        Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k) := by
    intro v hv
    refine intM_fromBlocks.2 ⟨intM_one, intM_zero, fun l x => ?_, intM_one⟩
    simp only [Matrix.of_apply]
    split_ifs
    · rw [Valuation.mem_integer_iff, map_mul, map_inv₀]
      have h0 : valuation k ((S.ϖ : k) ^ (r + 1)) ≠ 0 := (Valuation.ne_zero_iff _).2 (pow_ne_zero _ (Units.ne_zero _))
      have h1 := hv x
      rw [Units.val_pow_eq_pow_val] at h1
      calc (valuation k ((S.ϖ : k) ^ (r + 1)))⁻¹ * valuation k (v x) ≤
            (valuation k ((S.ϖ : k) ^ (r + 1)))⁻¹ * valuation k ((S.ϖ : k) ^ (r + 1)) := mul_le_mul' le_rfl h1
        _ = 1 := inv_mul_cancel₀ h0
    · exact zero_mem _
  change (typeFrame S.ϖ ord).conj.symm (rowE (c + 1 + 1) (r + 1) u) ∈ (S.P.iter t S.μ S.tame (j + 1)).J
  rw [hP (j + 1)]
  refine ⟨mem_KO.2 ⟨?_, ?_⟩, ?_⟩
  · rw [conj_rowE S t j c H r u]
    exact fun a b => hint u hu _ _
  · rw [← map_inv, rowE_inv', conj_rowE S t j c H r (-u)]
    exact fun a b => hint (-u) (neg_mem hu) _ _
  · intro a b hab
    rw [conj_rowE S t j c H r u]
    suffices h : (fromBlocks 1 0 (Matrix.of fun (l : Fin (c + 1 + 1)) x => if l.val = r then (((S.ϖ : k) ^ (r + 1))⁻¹ * u x) else 0) 1 :
        Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k) (ord a) (ord b) =
        (1 : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k) (ord a) (ord b) by
      have h1 : (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (j + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) t (j + 1)) k) a b =
          (1 : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k) (ord a) (ord b) := by
        simp only [Matrix.one_apply, ord.injective.eq_iff]
      rw [Matrix.submatrix_apply, h, ← h1, sub_self, map_zero]
      exact zero_lt_one
    rcases hA : ord a with A | A <;> rcases hB : ord b with B | B
    · simp [Matrix.one_apply]
    · simp
    · simp only [fromBlocks_apply₂₁, Matrix.of_apply]
      split_ifs with hAr
      · exfalso
        apply hab
        have ha : a = .inl (.inr ⟨A.val, by omega⟩) :=
          ord.injective (hA.trans (standardOrderExtendedBasis_apply_low_block (Fin κ) t (j + 1) (c + 1 + 1) _ A).symm)
        subst ha
        rcases B with (B | B) | B
        · have hb : b = .inl (.inl B) := ord.injective (hB.trans (stdOrd_eps (Fin κ) t (j + 1) (c + 1 + 1) _ B).symm)
          subst hb
          simp only [FreeIx, FreeTop]
          omega
        · have hb : b = .inl (.inr ⟨c + 1 + 1 + B.val, by omega⟩) :=
            ord.injective (hB.trans (stdOrd_f (Fin κ) t (j + 1) (c + 1 + 1) _ B).symm)
          subst hb
          simp only [FreeIx, FreeTop, Fin.lt_def]
          omega
        · have hb : b = .inr B := ord.injective (hB.trans (stdOrd_d (Fin κ) t (j + 1) (c + 1 + 1) _ B).symm)
          subst hb
          simp only [FreeIx]
      · simp
    · simp [Matrix.one_apply]

theorem Phi_mul_rowE (hP : S.Pattern t) (j c : ℕ) (H : j + 1 + (c + 1) = s) (r : ℕ) (hc : c = 2 * r)
    (u : XIx (Fin κ) t (j + 1) → k) (hu : u ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1))) :
    ∃ a : ℂ, ∀ y, (S.T t).Phi (j + 1) (c + 1) H (y * (rowE (c + 1 + 1) (r + 1) u).val) =
      a * (S.T t).Phi (j + 1) (c + 1) H y := by
  have hL : (S.T t).Laws := Chain.ofType_laws _ _ _ _ _
  have hm := rowE_mem_lev S t hP j c H r hc u hu
  have h1 := (hL.1 (j + 1) (c + 1) H).1 ⟨_, hm⟩
  refine ⟨((((S.T t).lev (j + 1) (c + 1 + 1) (by omega)).lam ⟨_, hm⟩ : ℂˣ) : ℂ), fun y => ?_⟩
  have h2 := congrFun h1 y
  simp only [om, det_rowE', map_one, inv_one, Units.val_one, nabs_one, Real.one_rpow, Complex.ofReal_one, one_mul,
    Matrix.one_mul, Pi.smul_apply, smul_eq_mul] at h2
  exact h2

end GlobalTheory.LocFlat.DoubleStepProof

open GlobalTheory.LocFlat.DoubleStepProof in
open Classical in

theorem GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.OneIndexAt t ν → GlobalTheory.LocFlat.PureCol S t ν → GlobalTheory.LocFlat.PureRow S t ν → GlobalTheory.LocFlat.DoubleStep S t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hP hOne hCol hRow j c H r hc
  haveI := hν.1
  obtain ⟨C₁, hC₁, hC1⟩ := hCol j (c + 1) (by omega) (r + 1) (by omega)
  obtain ⟨V, hV, hVe⟩ := hat_box (n := XIx (Fin κ) t (j + 1)) S.cond ν (S.ϖ ^ (r + 1))
  have hhat : ∀ (p : Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) k × Matrix (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) k)
      (u : XIx (Fin κ) t (j + 1) → k),
      hat S.ψ ν (-1) (fun y => flCol S.ψ ν (r + 1 + 1) ((S.T t).Phi j (c + 1 + 1) (by omega))
        (fromCols p.1 (Matrix.of fun r _ => y r))) u =
        (C₁ : ℂ) * (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 p.1 *
          ((V : ℂ) * (if u ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1)) then 1 else 0)) := by
    intro p u
    rw [← hVe u]
    unfold hat
    rw [← integral_const_mul]
    congr 1
    funext y
    dsimp only
    rw [hC1, toCols₁_fromCols]
    have ey : (fun a => (fromCols p.1 (Matrix.of fun r _ => y r) : Matrix _ _ k) a (Sum.inr ())) = y := by funext a; simp
    rw [ey]
    ring
  have hΦ₂ : (S.T t).Phi (j + 1) (c + 1) (by omega) ∈ SB _ := (Chain.ofType_regular _ _ _ _ _).1 (j + 1) (c + 1) (by omega)
  refine ⟨fun h hne => ?_, ?_⟩
  · obtain ⟨p, hp⟩ := Function.ne_iff.mp hne
    refine hOne (j + 1) (c + 1) (by omega) (r + 1) (by omega) (by omega) h (fun h0 => hp ?_)
    simp only [contr]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.zero_apply]
    rw [hhat p u]
    by_cases hu : u ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1))
    · have e1 : (fromRows p.2 (Matrix.of fun _ => u)) (Sum.inr ()) = u := by funext a; simp
      rw [GlobalTheory.T.flatRowMap_eq_rootExchangeOperator_translate k S.ψ ν S.cond.continuous hν.1 _ _ (c + 1) (r + 1) (by omega) (by omega) _
        (om_mem_SB _ 1 h hΦ₂) _, e1, toRows₁_fromRows]
      obtain ⟨a, ha⟩ := Phi_mul_rowE S t hP j c (by omega) r hc u hu
      have e2 : (fun z => om (S.μ (j + 1 + 1)) 1 h ((S.T t).Phi (j + 1) (c + 1) (by omega)) (z * (rowE (c + 1 + 1) (r + 1) u).val)) =
          fun z => a * om (S.μ (j + 1 + 1)) 1 h ((S.T t).Phi (j + 1) (c + 1) (by omega)) z := by
        funext z
        simp only [om]
        rw [show (h⁻¹ : GL _ k).val * (z * (rowE (c + 1 + 1) (r + 1) u).val) * (1 : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k).val =
          ((h⁻¹ : GL _ k).val * z * (1 : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k).val) * (rowE (c + 1 + 1) (r + 1) u).val by
          simp [Matrix.mul_assoc], ha]
        ring
      have e3 : opE S.ψ ν (r + 1) (fun z => a * om (S.μ (j + 1 + 1)) 1 h ((S.T t).Phi (j + 1) (c + 1) (by omega)) z) p.2 = 0 := by
        unfold opE
        simp_rw [mul_assoc]
        rw [integral_const_mul]
        have := congrFun h0 p.2
        unfold opE at this
        rw [this]; simp
      refine mul_eq_zero_of_left ?_ _
      rw [← e3]
      congr 1
    · rw [if_neg hu]; simp
  · obtain ⟨C₂, hC₂, hC2⟩ := hRow (j + 1) c H r hc
    have hW := vol_box_pos (n := XIx (Fin κ) t (j + 1)) ν (S.ϖ ^ (r + 1))
    set W := ((Measure.pi fun _ : XIx (Fin κ) t (j + 1) => ν) (box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1)) : Set (XIx (Fin κ) t (j + 1) → k))).toReal with hWdef
    refine ⟨C₁ * C₂ * V * W, by positivity, fun p => ?_⟩
    simp only [contr]
    refine (integral_congr_ae (μ := Measure.pi fun _ => ν)
      (g := fun u => ((C₁ : ℂ) * C₂ * V * (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 p.1 *
        (S.T t).entry S.ψ ν (j + 1) c H 1 1 p.2) * (if u ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1)) then 1 else 0))
      (Filter.Eventually.of_forall fun u => ?_)).trans ?_
    · dsimp only
      rw [hhat p u, hC2]
      have e1 : (fromRows p.2 (Matrix.of fun _ => u)) (Sum.inr ()) = u := by funext a; simp
      rw [e1, toRows₁_fromRows]
      split_ifs <;> ring
    · rw [integral_const_mul, integral_box]
      push_cast
      ring
