import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpOmOm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumEigenvectorTwoBlockParahoricStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntegralGLOfInParahoricDatumSupportMulBlockDiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumTorusIntegrandEqIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasureParahoricDatumSupportStatement

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section
namespace GlobalTheory.ChainStepCoef

theorem om_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (g g' : GL a k)
    (Φ : Matrix b a k → ℂ) : om μ (g * g') (1 : GL b k) Φ = om μ g 1 (om μ g' 1 Φ) := by
  funext x
  have p1 := (nabs_pos' (GeneralLinearGroup.det g)).le
  have p2 := (nabs_pos' (GeneralLinearGroup.det g')).le
  have hm : ∀ u v : kˣ, nabs k (u * v) = nabs k u * nabs k v := fun u v => by simp [nabs, map_mul]
  have h1 : nabs k 1 = 1 := by simp [nabs]
  simp only [om, map_mul, hm, Real.mul_rpow p1 p2, inv_one, Units.val_one, Matrix.one_mul, Units.val_mul,
    Matrix.mul_assoc, map_one, h1, Real.one_rpow]
  push_cast
  ring

theorem om_smul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (g : GL a k)
    (h : GL b k) (c : ℂ) (Φ : Matrix b a k → ℂ) :
    om μ g h (fun x => c * Φ x) = fun x => c * om μ g h Φ x := by
  funext x
  simp only [om]
  ring

theorem ip_smul_left {k : Type} [Field k] [MeasurableSpace k] (ν : Measure k) {m n : Type} [Fintype m] [Fintype n]
    (c : ℂ) (F G : Matrix m n k → ℂ) : ip ν (fun x => c * F x) G = c * ip ν F G := by
  unfold ip
  simp_rw [mul_assoc]
  exact integral_const_mul c _

theorem ip_smul_right {k : Type} [Field k] [MeasurableSpace k] (ν : Measure k) {m n : Type} [Fintype m] [Fintype n]
    (c : ℂ) (F G : Matrix m n k → ℂ) : ip ν F (fun x => c * G x) = starRingEnd ℂ c * ip ν F G := by
  unfold ip
  simp_rw [map_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem part1 (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν)
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ μ₀ : kˣ →* ℂˣ) (hξu : IsUnitaryChar ξ) (hξt : IsTame ξ) (hμu : IsUnram μ₀) (hμn : IsUnitaryChar μ₀) :
    IsBiType ξ (fun g : GL (A ⊕ D) k =>
      ip ν (om (μ₀ * ξ) g (1 : GL (A ⊕ E) k) (datum ξ)) (datum ξ : Matrix (A ⊕ E) (A ⊕ D) k → ℂ)) := by
  haveI := hν.1
  have hμ' : ∀ x, ‖((μ₀ * ξ) x : ℂ)‖ = 1 := fun x => by
    simp [MonoidHom.mul_apply, Units.val_mul, norm_mul, hξu x, hμn x]
  have hL1 := GlobalTheory.T.parahoricDatum_eigenvector_twoBlockParahoric k A D E ξ μ₀ hξt hμu
  intro j hj d hd g
  have hu : (ξ d : ℂ) * starRingEnd ℂ (ξ d) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hξu d]; simp
  refine ⟨?_, ?_⟩
  · have h1 := ip_om_om k _ _ ν (μ₀ * ξ) hμ' j 1 (om (μ₀ * ξ) g 1 (datum ξ : Matrix (A ⊕ E) (A ⊕ D) k → ℂ))
      (datum ξ)
    rw [← om_mul, hL1 j hj d hd, ip_smul_right] at h1
    simp only
    rw [← h1, ← mul_assoc, hu, one_mul]
  · simp only
    rw [om_mul, hL1 j hj d hd, om_smul, ip_smul_left]

theorem part2 (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] (ν : Measure k)
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ μ : kˣ →* ℂˣ) (x : GL A k) (y : GL D k) :
    ip ν (om μ (emb₂ k (Equiv.refl (A ⊕ D)) (x, y)) (1 : GL (A ⊕ E) k) (datum ξ))
      (datum ξ : Matrix (A ⊕ E) (A ⊕ D) k → ℂ) ≠ 0 → x ∈ KO k A := by
  intro h
  by_contra hx
  apply h
  unfold ip
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.zero_apply, om, inv_one, Units.val_one, Matrix.one_mul]
  by_cases h1 : InSupp z
  · have h2 : ¬ InSupp (z * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y) : Matrix (A ⊕ D) (A ⊕ D) k)) :=
      fun h2 => hx (GlobalTheory.T.mem_integralGL_of_inParahoricDatumSupport_mul_blockDiag k A D E z x y h1 h2)
    simp [datum, h2]
  · simp [datum, h1]

theorem det_mtor {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    GeneralLinearGroup.det (mtor ϖ e : GL (A ⊕ D) k) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, mtor, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val,
    Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
  induction (Finset.univ : Finset D) using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ (Units.ne_zero ϖ), ih]

theorem nabs_det_mtor {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (e : D → ℤ) :
    nabs k (GeneralLinearGroup.det (mtor ϖ e : GL (A ⊕ D) k)) = (resCard k : ℝ) ^ (-∑ i, e i) := by
  rw [mtor, nabs_det_torusElt hϖ, Fintype.sum_sum_type]
  simp

theorem part3 (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν)
    (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (r : ℕ)
    (D E : Type) [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ μ : kˣ →* ℂˣ) (hξu : IsUnitaryChar ξ) (e : D → ℤ) :
    ip ν (om μ (mtor ϖ e) (1 : GL (Fin r ⊕ E) k) (datum ξ)) (datum ξ : Matrix (Fin r ⊕ E) (Fin r ⊕ D) k → ℂ) =
      (μ ϖ : ℂ) ^ (∑ i, e i) * ((volAdd ν r * ((resCard k : ℝ) ^ (r * Fintype.card E))⁻¹ : ℝ) : ℂ) *
      (resCard k : ℂ) ^ (-((r + Fintype.card E : ℕ) : ℂ) / 2 * (sumAbs e : ℂ)) := by
  haveI := hν.1
  obtain ⟨hS, hV⟩ := GlobalTheory.T.measure_parahoricDatumSupport k ν hν r D E
  have q1 : 1 < Nat.card 𝓀[k] := Finite.one_lt_card
  have q0 : (0 : ℝ) < resCard k := by unfold resCard; exact_mod_cast (lt_trans one_pos q1)
  set Φ : Matrix (Fin r ⊕ E) (Fin r ⊕ D) k → ℂ := datum ξ with hΦ
  set m : GL (Fin r ⊕ D) k := mtor ϖ e with hm
  set f : D → ℤ := fun i => -max 0 (-e i) with hf
  set m' : GL (Fin r ⊕ D) k := mtor ϖ f with hm'
  set S := {x : Matrix (Fin r ⊕ E) (Fin r ⊕ D) k | InSupp x} with hSdef
  have h1 : nabs k 1 = 1 := by simp [nabs]
  have hA : ∀ x, om μ m 1 Φ x * starRingEnd ℂ (Φ x) =
      ((μ (GeneralLinearGroup.det m) : ℂ) * ((nabs k (GeneralLinearGroup.det m) ^
        ((Fintype.card (Fin r ⊕ E) : ℝ) / 2) : ℝ) : ℂ)) * (Φ (x * m.val) * starRingEnd ℂ (Φ x)) := by
    intro x
    simp only [om, inv_one, Units.val_one, Matrix.one_mul, map_one, h1, Real.one_rpow]
    push_cast
    ring
  have hB : ∀ x, Φ (x * m.val) * starRingEnd ℂ (Φ x) = S.indicator (fun _ => (1 : ℂ)) (x * m'.val) := by
    intro x
    exact GlobalTheory.T.parahoricDatum_torus_integrand_eq_indicator k ϖ hϖ (Fin r) D E ξ hξu e x
  have hC := integral_comp_mul_mul_volM ν m' (1 : GL (Fin r ⊕ E) k) (S.indicator (fun _ => (1 : ℂ)))
  simp only [Units.val_one, Matrix.one_mul, map_one, h1, Real.one_rpow, one_mul] at hC
  have hI : ∫ x, S.indicator (fun _ => (1 : ℂ)) x ∂(volM ν (Fin r ⊕ E) (Fin r ⊕ D)) =
      (volM ν (Fin r ⊕ E) (Fin r ⊕ D)).real S • (1 : ℂ) := by
    exact integral_indicator_const (μ := volM ν (Fin r ⊕ E) (Fin r ⊕ D)) (1 : ℂ) hS
  unfold ip
  simp_rw [hA, hB]
  rw [integral_const_mul, hC, hI, hV, nabs_det_mtor hϖ, nabs_det_mtor hϖ, det_mtor,
    map_zpow, Units.val_zpow_eq_zpow_val]
  have hsumZ : sumAbs e = ∑ i, e i - 2 * ∑ i, f i := by
    unfold sumAbs
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf]
    rcases le_total 0 (e i) with h | h
    · rw [abs_of_nonneg h, max_eq_left (by omega)]; ring
    · rw [abs_of_nonpos h, max_eq_right (by omega)]; ring
  have hsum : (sumAbs e : ℝ) = ∑ i, (e i : ℝ) - 2 * ∑ i, (f i : ℝ) := by
    rw [hsumZ]; push_cast; ring
  have key : ((resCard k : ℝ) ^ (-∑ i, e i)) ^ (((r + Fintype.card E : ℕ) : ℝ) / 2) *
      ((resCard k : ℝ) ^ (-∑ i, f i)) ^ (-((r + Fintype.card E : ℕ) : ℝ)) =
      (resCard k : ℝ) ^ ((-((r + Fintype.card E : ℕ) : ℝ) / 2) * (sumAbs e : ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul q0.le, ← Real.rpow_mul q0.le,
      ← Real.rpow_add q0, hsum]
    congr 1
    push_cast
    ring
  have hc : (resCard k : ℂ) ^ (-((r + Fintype.card E : ℕ) : ℂ) / 2 * (sumAbs e : ℂ)) =
      (((resCard k : ℝ) ^ ((-((r + Fintype.card E : ℕ) : ℝ) / 2) * (sumAbs e : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow q0.le]
    push_cast
    ring_nf
  rw [hc, ← key]
  simp only [Fintype.card_sum, Fintype.card_fin, Complex.real_smul, smul_eq_mul, mul_one]
  push_cast
  ring

theorem coef : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r t l : ℕ) (ξ μ₀' : kˣ →* ℂˣ), IsUnitaryChar ξ → IsTame ξ → IsUnram μ₀' → IsUnitaryChar μ₀' →
  let μ' : kˣ →* ℂˣ := μ₀' * ξ
  let Φ : Matrix (Fin r ⊕ Blocks (l + 1) t) (Fin r ⊕ Blocks l t) k → ℂ := datum ξ
  let c : GL (Fin r ⊕ Blocks l t) k → ℂ := fun g => ip ν (om μ' g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) Φ) Φ
  IsBiType ξ c ∧
  (∀ x y, c (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (x, y)) ≠ 0 → x ∈ KO k (Fin r)) ∧
  ∀ e : Blocks l t → ℤ, c (mtor ϖ e) = (μ' ϖ : ℂ) ^ (∑ i, e i) *
    ((volAdd ν r * ((resCard k : ℝ) ^ (r * ((l + 1) * t)))⁻¹ : ℝ) : ℂ) *
    (resCard k : ℂ) ^ (-((r + (l + 1) * t : ℕ) : ℂ) / 2 * (sumAbs e : ℂ)) := by
  intro k _ _ _ _ _ _ ν hν ϖ hϖ r t l ξ μ₀' hξu hξt hμu hμn μ' Φ c
  have hE : Fintype.card (Blocks (l + 1) t) = (l + 1) * t := by simp [Blocks]
  refine ⟨part1 k ν hν (Fin r) (Blocks l t) (Blocks (l + 1) t) ξ μ₀' hξu hξt hμu hμn,
    fun x y => part2 k ν (Fin r) (Blocks l t) (Blocks (l + 1) t) ξ (μ₀' * ξ) x y, fun e => ?_⟩
  have := part3 k ν hν ϖ hϖ r (Blocks l t) (Blocks (l + 1) t) ξ (μ₀' * ξ) hξu e
  rw [hE] at this
  exact this

end GlobalTheory.ChainStepCoef
