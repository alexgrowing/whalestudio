import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaPairDetTwist

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Tls2.Ming3.LawX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_inv (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by
  have h := nabs_mul' k x⁻¹ x
  rw [inv_mul_cancel, show nabs k 1 = 1 by simp [nabs]] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem inv_natPow_rpow_neg_half_even_eq_pow {A H : ℝ} (hA : 0 < A) (hH : 0 < H) (N r : ℝ) :
    A ^ (N / 2) * H ^ (-r / 2) * ((H⁻¹) ^ (-r) * A ^ (-N)) = A ^ (-N / 2) * H ^ (r / 2) := by
  rw [Real.inv_rpow hH.le, Real.rpow_neg hH.le, inv_inv]
  have e1 : A ^ (-N / 2) = A ^ (N / 2) * A ^ (-N) := by
    rw [← Real.rpow_add hA]; congr 1; ring
  have e2 : H ^ (r / 2) = H ^ (-r / 2) * H ^ r := by
    rw [← Real.rpow_add hH]; congr 1; ring
  rw [e1, e2]; ring

theorem rpow_product_eq_one {A D : ℝ} (hA : 0 < A) (hD : 0 < D) (r t : ℝ) :
    A ^ (-(r + t) / 2) * (A * D) ^ (r / 2) * (A ^ (t / 2) * D ^ (-r / 2)) = 1 := by
  have : A ^ (-(r + t) / 2) * (A * D) ^ (r / 2) * (A ^ (t / 2) * D ^ (-r / 2)) =
      A ^ (-(r + t) / 2 + r / 2 + t / 2) * D ^ (r / 2 + -r / 2) := by
    rw [Real.mul_rpow hA.le hD.le, Real.rpow_add hA, Real.rpow_add hA, Real.rpow_add hD]; ring
  rw [this, show -(r + t) / 2 + r / 2 + t / 2 = (0 : ℝ) by ring, show r / 2 + -r / 2 = (0 : ℝ) by ring]
  simp

variable [MeasurableSpace k] [BorelSpace k]

theorem integral_om (hcov : CovSt) (ν : Measure k) (hν : IsUnitVol ν) {r N : ℕ} (μ : kˣ →* ℂˣ)
    (g : GL (Fin r) k) (h : GL (Fin N) k) (Φ : Matrix (Fin N) (Fin r) k → ℂ) :
    ∫ x, om μ g h Φ x ∂volM ν (Fin N) (Fin r) =
      (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) *
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(N : ℝ) / 2) : ℝ) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det h) ^ ((r : ℝ) / 2) : ℝ) : ℂ) *
        ∫ x, Φ x ∂volM ν (Fin N) (Fin r) := by
  simp only [om]
  rw [integral_const_mul, hcov k ν hν N r h⁻¹ g Φ, map_inv, nabs_inv, Fintype.card_fin, Fintype.card_fin]
  have hR := inv_natPow_rpow_neg_half_even_eq_pow (nabs_pos' k (Matrix.GeneralLinearGroup.det g))
    (nabs_pos' k (Matrix.GeneralLinearGroup.det h)) (N : ℝ) (r : ℝ)
  have hR' := congrArg (fun x : ℝ => (x : ℂ)) hR
  set C : ℂ := (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ)
  set I := ∫ x, Φ x ∂volM ν (Fin N) (Fin r)
  simp only [Complex.ofReal_mul] at hR' ⊢
  linear_combination (C * I) * hR'

end PositivityTheory.Tls2.Ming3.LawX

namespace PositivityTheory.Tls2.Ming3

open PositivityTheory.Tls2.Ming3.LawX in
theorem law : BallSt → CovSt → LawSt := by
  intro hball hcov k _ _ _ _ _ _ ν hν r t μ V _ _ W _ _ σ π B hEq ev hG p w
  set a : GL (Fin r) k := leviProj k (two (stdSum (rfl : r + t = r + t))) p false with ha
  set d : GL (Fin t) k := leviProj k (two (stdSum (rfl : r + t = r + t))) p true with hd
  set e := GlobalTheory.GodementJacquet.eMat k r t with he
  refine ((hG _ _).1 ?_).symm
  obtain ⟨c₀, hc₀⟩ := (hG w (ev w)).2 rfl
  have hfe : ((p : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val * e * a.val = e := by
    rw [Matrix.mul_assoc, he, ha, ← GlobalTheory.GodementJacquet.parab_mul_eMat p, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  have hfc : Continuous fun y : Matrix (Fin (r + t)) (Fin r) k =>
      ((p : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val * y * a.val :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have he0 : e ∈ ballM c₀ e := fun i l => by simp
  have hU : (fun y : Matrix (Fin (r + t)) (Fin r) k =>
      ((p : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val * y * a.val) ⁻¹' ballM c₀ e ∈ nhds e := by
    refine hfc.continuousAt.preimage_mem_nhds ?_
    rw [hfe]
    exact ((hball k (r + t) r).1 c₀ e).1.mem_nhds he0
  obtain ⟨c, -, hc⟩ := (hball k (r + t) r).2.1 e _ hU
  refine ⟨c, fun Φ' hΦ' => ?_⟩
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : SB (Matrix (Fin (r + t)) (Fin r) k),
      Φ.1 = om μ a⁻¹ ((p : GL (Fin (r + t)) k)⁻¹) Φ'.1 :=
    ⟨⟨_, om_mem_SB μ _ _ Φ'.2⟩, rfl⟩
  have hΦΦ' : (Φ' : Matrix (Fin (r + t)) (Fin r) k → ℂ) = om μ a (p : GL (Fin (r + t)) k) Φ.1 := by
    show Φ'.1 = _
    rw [hΦdef, ← om_mul, mul_inv_cancel, mul_inv_cancel, om_one]
  have hsupp : ∀ x, Φ.1 x ≠ 0 → x ∈ ballM c₀ e := by
    intro x hx
    rw [hΦdef] at hx
    simp only [om, inv_inv] at hx
    have hy := hΦ' _ (right_ne_zero_of_mul hx)
    have h2 := hc hy
    simp only [Set.mem_preimage] at h2
    have h3 : ((p : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val *
        ((p : GL (Fin (r + t)) k).val * x * (a⁻¹ : GL (Fin r) k).val) * a.val = x := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
        Units.inv_mul, Matrix.mul_one]
    rwa [h3] at h2
  have h1 := hEq a (p : GL (Fin (r + t)) k) Φ Φ' hΦΦ' w
  rw [h1, hc₀ Φ hsupp, map_smul, smul_smul]
  congr 1
  show _ = (∫ x, Φ'.1 x ∂volM ν (Fin (r + t)) (Fin r)) * _
  rw [show Φ'.1 = om μ a (p : GL (Fin (r + t)) k) Φ.1 from hΦΦ', integral_om hcov ν hν μ a _ Φ.1]
  have hl : leviProj k (two (stdSum (rfl : r + t = r + t))) p = leviTwo k (Fin r) (Fin t) (a, d) := by
    funext x
    cases x <;> rfl
  have hdet : Matrix.GeneralLinearGroup.det (p : GL (Fin (r + t)) k) =
      Matrix.GeneralLinearGroup.det a * Matrix.GeneralLinearGroup.det d := by
    rw [det_parab, Fintype.prod_bool, mul_comm]
  have e1 : (absPow k ((t : ℂ) / 2) (Matrix.GeneralLinearGroup.det a) : ℂ) =
      ((nabs k (Matrix.GeneralLinearGroup.det a) ^ ((t : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((t : ℂ) / 2) = (((t : ℝ) / 2 : ℝ) : ℂ) by simp]
    exact val_absPow_ofReal k _ _
  have e2 : (absPow k (-(r : ℂ) / 2) (Matrix.GeneralLinearGroup.det d) : ℂ) =
      ((nabs k (Matrix.GeneralLinearGroup.det d) ^ (-(r : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show (-(r : ℂ) / 2) = ((-(r : ℝ) / 2 : ℝ) : ℂ) by simp]
    exact val_absPow_ofReal k _ _
  have hR := rpow_product_eq_one (nabs_pos' k (Matrix.GeneralLinearGroup.det a))
    (nabs_pos' k (Matrix.GeneralLinearGroup.det d)) (r : ℝ) (t : ℝ)
  have hR' := congrArg (fun x : ℝ => (x : ℂ)) hR
  simp only [Complex.ofReal_mul, Complex.ofReal_one] at hR'
  have hn : (μ (Matrix.GeneralLinearGroup.det a) : ℂ) ≠ 0 := Units.ne_zero _
  have hn2 : (μ (Matrix.GeneralLinearGroup.det d) : ℂ) ≠ 0 := Units.ne_zero _
  rw [hl, deltaHalf_two]
  simp only [Units.val_mul, e1, e2, hdet, map_mul, nabs_mul', Fintype.card_fin, Nat.cast_add,
    Units.val_inv_eq_inv_val, mul_inv]
  have hinv := mul_inv_cancel₀ hn
  have hinv2 := mul_inv_cancel₀ hn2
  generalize (μ (Matrix.GeneralLinearGroup.det a) : ℂ) = a' at *
  generalize (μ (Matrix.GeneralLinearGroup.det d) : ℂ) = d' at *
  generalize ∫ x, Φ.1 x ∂volM ν (Fin (r + t)) (Fin r) = I at *
  set x1 : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det a) ^ (-((r : ℝ) + (t : ℝ)) / 2) : ℝ) : ℂ)
  set x2 : ℂ := (((nabs k (Matrix.GeneralLinearGroup.det a) * nabs k (Matrix.GeneralLinearGroup.det d)) ^
    ((r : ℝ) / 2) : ℝ) : ℂ)
  set x3 : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det a) ^ ((t : ℝ) / 2) : ℝ) : ℂ)
  set x4 : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det d) ^ (-(r : ℝ) / 2) : ℝ) : ℂ)
  linear_combination (-I) * hR' + (-I * x1 * x2 * x3 * x4 * d' * d'⁻¹) * hinv + (-I * x1 * x2 * x3 * x4) * hinv2
end PositivityTheory.Tls2.Ming3
