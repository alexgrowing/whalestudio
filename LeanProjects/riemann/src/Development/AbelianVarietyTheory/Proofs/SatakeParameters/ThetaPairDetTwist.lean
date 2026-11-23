import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSchwartzBumpNearIdentityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormNormSqLeReMulReStatement

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published ValuativeRel GlobalTheory.RootEx
open scoped TensorProduct Topology

namespace GlobalTheory.GodementJacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

local notation "e₀" => stdSum (rfl : _ + _ = _ + _)

section Mat

variable {α β : Type} [Fintype α]

theorem val_inl (j : Fin r) : ((stdSum (rfl : r + t = r + t) (Sum.inl j) : Fin (r + t)) : ℕ) = j := by simp

theorem mul_eMat (X : Matrix α (Fin (r + t)) k) (i : α) (j : Fin r) :
    (X * eMat k r t) i j = X i (stdSum (rfl : r + t = r + t) (Sum.inl j)) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (stdSum (rfl : r + t = r + t) (Sum.inl j))]
  · simp [eMat]
  · intro l _ hl
    have : (l : ℕ) ≠ j := fun h => hl (Fin.ext (by simp [h]))
    simp [eMat, this]
  · simp

theorem eMat_mul_inl (Y : Matrix (Fin r) β k) (i : Fin r) (j : β) :
    (eMat k r t * Y) (stdSum (rfl : r + t = r + t) (Sum.inl i)) j = Y i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [eMat]
  · intro l _ hl
    have : (i : ℕ) ≠ l := fun h => hl (Fin.ext h.symm)
    simp [eMat, this]
  · simp

theorem eMat_mul_inr (Y : Matrix (Fin r) β k) (i : Fin t) (j : β) :
    (eMat k r t * Y) (stdSum (rfl : r + t = r + t) (Sum.inr i)) j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  have : r + (i : ℕ) ≠ l := by omega
  simp [eMat, this]

open MeasureTheory ValuativeRel in
open scoped TensorProduct Topology in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] in

theorem _root_.GlobalTheory.GodementJacquet.parab_mul_eMat
    (p : _root_.GlobalTheory.SmGL.parab k
      (_root_.GlobalTheory.SmGL.two (_root_.GlobalTheory.SmGL.stdSum (rfl : r + t = r + t)))) :
    (p : GL (Fin (r + t)) k).val * _root_.GlobalTheory.GodementJacquet.eMat k r t =
      _root_.GlobalTheory.GodementJacquet.eMat k r t * (_root_.GlobalTheory.SmGL.leviProj k
        (_root_.GlobalTheory.SmGL.two (_root_.GlobalTheory.SmGL.stdSum (rfl : r + t = r + t))) p false :
          GL (Fin r) k).val := by
  have hE : ∀ (i : Fin (r + t)) (j : Fin r),
      _root_.GlobalTheory.GodementJacquet.eMat k r t i j = if i = Fin.castAdd t j then 1 else 0 := by
    intro i j
    simp [_root_.GlobalTheory.GodementJacquet.eMat, Fin.ext_iff]
  have hlow : ∀ (i : Fin t) (j : Fin r),
      (p : GL (Fin (r + t)) k).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
    intro i j
    have := (_root_.GlobalTheory.SmGL.mem_parab_two k).1 p.2 i j
    simpa [_root_.GlobalTheory.SmGL.stdSum] using this
  have hL : ∀ (i j : Fin r), (_root_.GlobalTheory.SmGL.leviProj k
      (_root_.GlobalTheory.SmGL.two (_root_.GlobalTheory.SmGL.stdSum (rfl : r + t = r + t))) p false :
        GL (Fin r) k).val i j = (p : GL (Fin (r + t)) k).val (Fin.castAdd t i) (Fin.castAdd t j) := by
    intro i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply]
    rfl
  ext i j
  simp only [Matrix.mul_apply, hE, hL, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [eq_comm]
  · rw [hlow]
    refine (Finset.sum_eq_zero fun x _ => ?_).symm
    rw [if_neg]
    simp only [Fin.ext_iff, Fin.coe_natAdd, Fin.coe_castAdd]
    omega

end Mat

section Coef

variable {σ : Representation ℂ (GL (Fin r) k) V} {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem fix_inv {g : GL (Fin r) k} {v : V} (h : σ g v = v) : σ g⁻¹ v = v := by
  conv_lhs => rw [← h]
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem continuous_coef (hσ : IsSmooth σ) (v w : V) : Continuous (coef σ Bf v w) := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun g₀ => ?_)
  have hc : Continuous fun g : GL (Fin r) k => g * g₀⁻¹ := continuous_mul_right _
  have h1 : {g : GL (Fin r) k | σ g v = v} ∈ 𝓝 ((fun g : GL (Fin r) k => g * g₀⁻¹) g₀) :=
    (hσ v).mem_nhds (by simp)
  filter_upwards [hc.continuousAt.preimage_mem_nhds h1] with g hg
  have hg' : σ (g * g₀⁻¹) v = v := hg
  have h2 : g⁻¹ = g₀⁻¹ * (g * g₀⁻¹)⁻¹ := by group
  simp only [coef]
  rw [h2, map_mul, Module.End.mul_apply, fix_inv hg']

theorem norm_coef_le (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w) (v w : V) (g : GL (Fin r) k) :
    ‖coef σ Bf v w g‖ ≤ √((Bf v v).re * (Bf w w).re) := by
  have h := GlobalTheory.T.hermitian_norm_sq_le_re_mul_re_of_posDef V Bf hs hp (σ g⁻¹ v) w
  rw [hu] at h
  exact Real.le_sqrt_of_sq_le h

end Coef

section Law

theorem rpow_identity {a d g h : ℝ} (ha : 0 < a) (hd : 0 < d) (hg : 0 < g) (hh : 0 < h) (r t : ℝ) :
    (a * g) ^ ((r + t) / 2) * (a * d * h) ^ (-r / 2) =
      a ^ (t / 2) * d ^ (-r / 2) * (g ^ ((r + t) / 2) * h ^ (-r / 2)) := by
  rw [Real.mul_rpow ha.le hg.le, Real.mul_rpow (mul_pos ha hd).le hh.le, Real.mul_rpow ha.le hd.le]
  have : a ^ ((r + t) / 2) * a ^ (-r / 2) = a ^ (t / 2) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  rw [← this]
  ring

theorem om_parab (μ : kˣ →* ℂˣ) (p : parab k (two (stdSum (rfl : r + t = r + t))))
    (g : GL (Fin r) k) (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ) :
    om μ ((leviProj k (two (stdSum (rfl : r + t = r + t))) p false : GL (Fin r) k) * g)
        ((p : GL (Fin (r + t)) k) * h) Φ (eMat k r t) =
      (deltaHalf k (Two (Fin r) (Fin t)) (leviProj k (two (stdSum (rfl : r + t = r + t))) p) : ℂ) *
        ((μ (Matrix.GeneralLinearGroup.det
          (leviProj k (two (stdSum (rfl : r + t = r + t))) p true : GL (Fin t) k)))⁻¹ : ℂˣ) *
        om μ g h Φ (eMat k r t) := by
  set a : GL (Fin r) k := leviProj k (two (stdSum (rfl : r + t = r + t))) p false with ha
  set d : GL (Fin t) k := leviProj k (two (stdSum (rfl : r + t = r + t))) p true with hd
  have hl : leviProj k (two (stdSum (rfl : r + t = r + t))) p = leviTwo k (Fin r) (Fin t) (a, d) := by
    funext x
    cases x <;> rfl
  have hdet : Matrix.GeneralLinearGroup.det (p : GL (Fin (r + t)) k) =
      Matrix.GeneralLinearGroup.det a * Matrix.GeneralLinearGroup.det d := by
    rw [det_parab, Fintype.prod_bool, mul_comm]
  have hx : (((p : GL (Fin (r + t)) k) * h)⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * (a * g).val =
      (h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * g.val := by
    have h1 := parab_mul_eMat p
    have h2 : ((p : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * a.val = eMat k r t := by
      rw [Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have h3 : ((p : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val * (eMat k r t * a.val * g.val) =
        eMat k r t * g.val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2]
    rw [mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (eMat k r t),
      h3, Matrix.mul_assoc]
  have hR := rpow_identity (nabs_pos' k (Matrix.GeneralLinearGroup.det a))
    (nabs_pos' k (Matrix.GeneralLinearGroup.det d)) (nabs_pos' k (Matrix.GeneralLinearGroup.det g))
    (nabs_pos' k (Matrix.GeneralLinearGroup.det h)) (r : ℝ) (t : ℝ)
  have hR' := congrArg (fun x : ℝ => (x : ℂ)) hR
  simp only [Complex.ofReal_mul] at hR'
  have hn : (μ (Matrix.GeneralLinearGroup.det a) : ℂ) ≠ 0 := Units.ne_zero _
  have hn2 : (μ (Matrix.GeneralLinearGroup.det d) : ℂ) ≠ 0 := Units.ne_zero _
  have hn3 : (μ (Matrix.GeneralLinearGroup.det h) : ℂ) ≠ 0 := Units.ne_zero _
  rw [hl, deltaHalf_two]
  simp only [om]
  rw [hx]
  have e1 : (absPow k ((t : ℂ) / 2) (Matrix.GeneralLinearGroup.det a) : ℂ) =
      ((nabs k (Matrix.GeneralLinearGroup.det a) ^ ((t : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((t : ℂ) / 2) = (((t : ℝ) / 2 : ℝ) : ℂ) by simp]
    exact val_absPow_ofReal k _ _
  have e2 : (absPow k (-(r : ℂ) / 2) (Matrix.GeneralLinearGroup.det d) : ℂ) =
      ((nabs k (Matrix.GeneralLinearGroup.det d) ^ (-(r : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show (-(r : ℂ) / 2) = ((-(r : ℝ) / 2 : ℝ) : ℂ) by simp]
    exact val_absPow_ofReal k _ _
  simp only [map_mul, hdet, nabs_mul', Units.val_mul, e1, e2, Fintype.card_fin, Nat.cast_add,
    Units.val_inv_eq_inv_val, mul_inv]
  have hinv := mul_inv_cancel₀ hn
  generalize (μ (Matrix.GeneralLinearGroup.det a) : ℂ) = a' at *
  generalize (μ (Matrix.GeneralLinearGroup.det d) : ℂ) = d' at *
  generalize (μ (Matrix.GeneralLinearGroup.det h) : ℂ) = h' at *
  generalize (μ (Matrix.GeneralLinearGroup.det g) : ℂ) = g' at *
  generalize Φ ((h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * g.val) = y at *
  generalize ((((nabs k (Matrix.GeneralLinearGroup.det a) * nabs k (Matrix.GeneralLinearGroup.det g)) ^ (((r : ℝ) + (t : ℝ)) / 2)) : ℝ) : ℂ) = x1 at *
  generalize ((((nabs k (Matrix.GeneralLinearGroup.det a) * nabs k (Matrix.GeneralLinearGroup.det d) *
            nabs k (Matrix.GeneralLinearGroup.det h)) ^ (-(r : ℝ) / 2)) : ℝ) : ℂ) = x2 at *
  linear_combination (g' * d'⁻¹ * h'⁻¹ * y * x1 * x2) * hinv + (g' * d'⁻¹ * h'⁻¹ * y) * hR'

end Law

section Int

variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem integrable_mul_coef (hσ : IsSmooth σ) (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
    (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
    {f : GL (Fin r) k → ℂ} (hf : Integrable f m) (v w : V) :
    Integrable (fun g => f g * coef σ Bf v w g) m :=
  hf.mul_bdd (c := √((Bf v v).re * (Bf w w).re)) (continuous_coef hσ v w).aestronglyMeasurable
    (ae_of_all _ (norm_coef_le hs hp hu v w))

variable (hσ : IsSmooth σ) (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
    (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
include hσ hs hp hu

theorem gjInt_add_left {Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ} {h : GL (Fin (r + t)) k}
    (hf : Integrable (fun g => om μ g h Φ (eMat k r t)) m) (v v' w : V) :
    gjInt m μ σ Bf Φ h (v + v') w = gjInt m μ σ Bf Φ h v w + gjInt m μ σ Bf Φ h v' w := by
  simp only [gjInt]
  rw [← integral_add (integrable_mul_coef hσ hs hp hu hf _ _) (integrable_mul_coef hσ hs hp hu hf _ _)]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp [coef, mul_add]

theorem gjInt_add_right {Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ} {h : GL (Fin (r + t)) k}
    (hf : Integrable (fun g => om μ g h Φ (eMat k r t)) m) (v w w' : V) :
    gjInt m μ σ Bf Φ h v (w + w') = gjInt m μ σ Bf Φ h v w + gjInt m μ σ Bf Φ h v w' := by
  simp only [gjInt]
  rw [← integral_add (integrable_mul_coef hσ hs hp hu hf _ _) (integrable_mul_coef hσ hs hp hu hf _ _)]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp [coef, mul_add]

theorem gjInt_add_fun {Φ Ψ : Matrix (Fin (r + t)) (Fin r) k → ℂ} {h : GL (Fin (r + t)) k}
    (hf : Integrable (fun g => om μ g h Φ (eMat k r t)) m)
    (hg : Integrable (fun g => om μ g h Ψ (eMat k r t)) m) (v w : V) :
    gjInt m μ σ Bf (Φ + Ψ) h v w = gjInt m μ σ Bf Φ h v w + gjInt m μ σ Bf Ψ h v w := by
  simp only [gjInt]
  rw [← integral_add (integrable_mul_coef hσ hs hp hu hf _ _) (integrable_mul_coef hσ hs hp hu hg _ _)]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [om, Pi.add_apply]
  ring

omit hσ hs hp hu [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)] in
theorem gjInt_smul_left (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ) (h : GL (Fin (r + t)) k) (c : ℂ) (v w : V) :
    gjInt m μ σ Bf Φ h (c • v) w = c * gjInt m μ σ Bf Φ h v w := by
  simp only [gjInt]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [coef, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

omit hσ hs hp hu [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)] in
theorem gjInt_smul_right (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ) (h : GL (Fin (r + t)) k) (c : ℂ) (v w : V) :
    gjInt m μ σ Bf Φ h v (c • w) = starRingEnd ℂ c * gjInt m μ σ Bf Φ h v w := by
  simp only [gjInt]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [coef, LinearMap.map_smulₛₗ, smul_eq_mul]
  ring

omit hσ hs hp hu [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)] in
theorem gjInt_smul_fun (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ) (h : GL (Fin (r + t)) k) (c : ℂ) (v w : V) :
    gjInt m μ σ Bf (c • Φ) h v w = c * gjInt m μ σ Bf Φ h v w := by
  simp only [gjInt]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [om, Pi.smul_apply, smul_eq_mul]
  ring

omit hσ hs hp hu [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)] in

theorem gjInt_translate (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ) (h h₀ : GL (Fin (r + t)) k) (v w : V) :
    gjInt m μ σ Bf (om μ 1 h₀ Φ) h v w = gjInt m μ σ Bf Φ (h * h₀) v w := by
  simp only [gjInt]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  have := om_mul μ g 1 h h₀ Φ
  rw [mul_one] at this
  simp only [this]

end Int

section Family

variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem gjInt_shift [m.IsMulRightInvariant] (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
    (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ) (h : GL (Fin (r + t)) k) (g₀ : GL (Fin r) k) (v w : V) :
    gjInt m μ σ Bf (om μ g₀ 1 Φ) h v w = gjInt m μ σ Bf Φ h v (σ g₀⁻¹ w) := by
  simp only [gjInt]
  rw [← integral_mul_right_eq_self (μ := m)
    (fun x => om μ x h Φ (eMat k r t) * coef σ Bf v (σ g₀⁻¹ w) x) g₀]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  have h1 := om_mul μ g g₀ h 1 Φ
  rw [mul_one] at h1
  simp only [h1, coef]
  rw [mul_inv_rev, map_mul, Module.End.mul_apply, hu]

theorem gjInt_law [m.IsMulLeftInvariant] (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ)
    (p : parab k (two (stdSum (rfl : r + t = r + t)))) (h : GL (Fin (r + t)) k) (v w : V) :
    gjInt m μ σ Bf Φ ((p : GL (Fin (r + t)) k) * h) v w =
      (deltaHalf k (Two (Fin r) (Fin t)) (leviProj k (two (stdSum (rfl : r + t = r + t))) p) : ℂ) *
        ((μ (Matrix.GeneralLinearGroup.det
          (leviProj k (two (stdSum (rfl : r + t = r + t))) p true : GL (Fin t) k)))⁻¹ : ℂˣ) *
        gjInt m μ σ Bf Φ h
          (σ (leviProj k (two (stdSum (rfl : r + t = r + t))) p false : GL (Fin r) k)⁻¹ v) w := by
  simp only [gjInt]
  rw [← integral_mul_left_eq_self (μ := m)
    (fun x => om μ x ((p : GL (Fin (r + t)) k) * h) Φ (eMat k r t) * coef σ Bf v w x)
    (leviProj k (two (stdSum (rfl : r + t = r + t))) p false : GL (Fin r) k), ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  have h1 := om_parab μ p g h Φ
  simp only [coef]
  rw [mul_inv_rev, map_mul, Module.End.mul_apply]
  refine (congrArg (· * _) h1).trans ?_
  ring

omit [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)] in
theorem rid_leviRep (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V)
    (g : Levi k (Two (Fin r) (Fin t))) (x : V ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ V (leviRep t μ σ g x) =
      (μ (Matrix.GeneralLinearGroup.det (g true : GL (Fin t) k)) : ℂ) •
        σ (g false : GL (Fin r) k) (TensorProduct.rid ℂ V x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul v z =>
    show TensorProduct.rid ℂ V (extTensor σ (detRep (Fin t) μ) ((leviTwo k (Fin r) (Fin t)).symm g) (v ⊗ₜ z)) = _
    rw [extTensor_tmul]
    simp [leviTwo, detRep, smul_smul]

variable [m.IsMulLeftInvariant] (hσ : IsSmooth σ) (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
    (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
    (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
      Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
      Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)

def rawF (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) (h : GL (Fin (r + t)) k) (w : V) :
    Module.Dual ℂ (V ⊗[ℂ] ℂ) :=
  ({ toFun := fun v => gjInt m μ σ Bf Φ.1 h v w
     map_add' := fun v v' => gjInt_add_left hσ hs hp hu (hI h Φ.1 Φ.2) v v' w
     map_smul' := fun c v => gjInt_smul_left _ _ c v w } : V →ₗ[ℂ] ℂ) ∘ₗ
    (TensorProduct.rid ℂ V).toLinearMap

theorem rawF_apply (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) (h : GL (Fin (r + t)) k) (w : V)
    (x : V ⊗[ℂ] ℂ) :
    rawF hσ hs hp hu hI Φ h w x = gjInt m μ σ Bf Φ.1 h (TensorProduct.rid ℂ V x) w := rfl

theorem rawF_law (Φ : SB (Matrix (Fin (r + t)) (Fin r) k))
    (p : parab k (two (stdSum (rfl : r + t = r + t)))) (h : GL (Fin (r + t)) k) (w : V) :
    rawF hσ hs hp hu hI Φ ((p : GL (Fin (r + t)) k) * h) w =
      (deltaHalf k (Two (Fin r) (Fin t)) (leviProj k (two (stdSum (rfl : r + t = r + t))) p) : ℂ) •
        (leviRep t μ σ).dual (leviProj k (two (stdSum (rfl : r + t = r + t))) p)
          (rawF hσ hs hp hu hI Φ h w) := by
  refine LinearMap.ext fun x => ?_
  show rawF hσ hs hp hu hI Φ ((p : GL (Fin (r + t)) k) * h) w x =
    (deltaHalf k (Two (Fin r) (Fin t)) (leviProj k (two (stdSum (rfl : r + t = r + t))) p) : ℂ) *
      rawF hσ hs hp hu hI Φ h w
        (leviRep t μ σ (leviProj k (two (stdSum (rfl : r + t = r + t))) p)⁻¹ x)
  rw [rawF_apply, rawF_apply, rid_leviRep, gjInt_law, gjInt_smul_left]
  simp only [Pi.inv_apply, map_inv, Units.val_inv_eq_inv_val]
  ring

theorem rawF_translate (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) (h h₀ : GL (Fin (r + t)) k) (w : V)
    (h₁ : om μ 1 h₀ Φ.1 = Φ.1) :
    rawF hσ hs hp hu hI Φ (h * h₀) w = rawF hσ hs hp hu hI Φ h w := by
  refine LinearMap.ext fun x => ?_
  rw [rawF_apply, rawF_apply, ← gjInt_translate, h₁]

omit [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)] in
theorem eventually_stab (hμ : IsSmoothChar μ) (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) :
    ∀ᶠ h₀ : GL (Fin (r + t)) k in 𝓝 1, om μ 1 h₀ Φ.1 = Φ.1 := by
  have h := (om_isSmoothRepresentation k (Fin r) (Fin (r + t)) μ hμ).2.2.2.2 Φ.1 Φ.2
  have hc : Continuous fun h₀ : GL (Fin (r + t)) k => ((1 : GL (Fin r) k), h₀) :=
    continuous_const.prodMk continuous_id
  exact (h.preimage hc).mem_nhds (om_one μ Φ.1)

theorem rawF_mem (hμ : IsSmoothChar μ) (Φ : SB (Matrix (Fin (r + t)) (Fin r) k))
    (h : GL (Fin (r + t)) k) (w : V) :
    rawF hσ hs hp hu hI Φ h w ∈ smoothPart (leviRep t μ σ).dual := by
  refine mem_smoothPart_of_nhds ?_
  have hc : Continuous fun g : Levi k (Two (Fin r) (Fin t)) =>
      h⁻¹ * leviEmb k (two (stdSum (rfl : r + t = r + t))) g * h :=
    (continuous_const.mul (continuous_leviEmb k _)).mul continuous_const
  have h1 : ∀ᶠ g : Levi k (Two (Fin r) (Fin t)) in 𝓝 1,
      om μ 1 (h⁻¹ * leviEmb k (two (stdSum (rfl : r + t = r + t))) g * h) Φ.1 = Φ.1 :=
    (hc.tendsto' 1 1 (by simp)).eventually (eventually_stab hμ Φ)
  have h2 : ∀ᶠ g : Levi k (Two (Fin r) (Fin t)) in 𝓝 1, deltaHalf k (Two (Fin r) (Fin t)) g = 1 :=
    (isSmoothChar_deltaHalf k).mem_nhds (one_mem _)
  filter_upwards [h1, h2] with g hg hd
  have law := rawF_law hσ hs hp hu hI Φ ⟨_, leviEmb_mem_parab k _ g⟩ h w
  rw [leviProj_leviEmb, hd, Units.val_one, one_smul] at law
  have tr := rawF_translate hσ hs hp hu hI Φ h _ w hg
  rw [show h * (h⁻¹ * leviEmb k (two (stdSum (rfl : r + t = r + t))) g * h) =
    leviEmb k (two (stdSum (rfl : r + t = r + t))) g * h by group] at tr
  exact law.symm.trans tr

def famF (hμ : IsSmoothChar μ) (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) (w : V) :
    IndSp (two (stdSum (rfl : r + t = r + t))) (contra (leviRep t μ σ)) :=
  ⟨⟨fun h => ⟨rawF hσ hs hp hu hI Φ h w, rawF_mem hσ hs hp hu hI hμ Φ h w⟩,
    fun p g => Subtype.ext (rawF_law hσ hs hp hu hI Φ p g w)⟩,
    mem_smoothPart_of_nhds (by
      filter_upwards [eventually_stab hμ Φ] with g hg
      refine Subtype.ext (funext fun x => Subtype.ext ?_)
      exact rawF_translate hσ hs hp hu hI Φ x g w hg)⟩

theorem famF_apply (hμ : IsSmoothChar μ) (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) (w : V)
    (h : GL (Fin (r + t)) k) (x : V ⊗[ℂ] ℂ) :
    ((famF hσ hs hp hu hI hμ Φ w).1.1 h).1 x =
      gjInt m μ σ Bf Φ.1 h (TensorProduct.rid ℂ V x) w := rfl

omit [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  [m.IsMulLeftInvariant] in
theorem indExt {F₁ F₂ : IndSp (two (stdSum (rfl : r + t = r + t))) (contra (leviRep t μ σ))}
    (H : ∀ h x, (F₁.1.1 h).1 x = (F₂.1.1 h).1 x) : F₁ = F₂ :=
  Subtype.ext (Subtype.ext (funext fun h => Subtype.ext (LinearMap.ext (H h))))

theorem famF_add_fun (hμ : IsSmoothChar μ) (Φ Ψ : SB (Matrix (Fin (r + t)) (Fin r) k)) (w : V) :
    famF hσ hs hp hu hI hμ (Φ + Ψ) w = famF hσ hs hp hu hI hμ Φ w + famF hσ hs hp hu hI hμ Ψ w :=
  indExt fun h x => gjInt_add_fun hσ hs hp hu (hI h Φ.1 Φ.2) (hI h Ψ.1 Ψ.2) _ w

theorem famF_smul_fun (hμ : IsSmoothChar μ) (c : ℂ) (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) (w : V) :
    famF hσ hs hp hu hI hμ (c • Φ) w = c • famF hσ hs hp hu hI hμ Φ w :=
  indExt fun h x => gjInt_smul_fun _ h c _ w

theorem famF_add_right (hμ : IsSmoothChar μ) (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) (w w' : V) :
    famF hσ hs hp hu hI hμ Φ (w + w') = famF hσ hs hp hu hI hμ Φ w + famF hσ hs hp hu hI hμ Φ w' :=
  indExt fun h x => gjInt_add_right hσ hs hp hu (hI h Φ.1 Φ.2) _ w w'

theorem famF_smul_right (hμ : IsSmoothChar μ) (c : ℂ) (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) (w : V) :
    famF hσ hs hp hu hI hμ Φ (c • w) = starRingEnd ℂ c • famF hσ hs hp hu hI hμ Φ w :=
  indExt fun h x => gjInt_smul_right _ h c _ w

theorem famF_translate (hμ : IsSmoothChar μ) (Φ Φ' : SB (Matrix (Fin (r + t)) (Fin r) k))
    (h₀ : GL (Fin (r + t)) k) (hΦ : Φ'.1 = om μ 1 h₀ Φ.1) (w : V) :
    parInd (two (stdSum (rfl : r + t = r + t))) (contra (leviRep t μ σ)) h₀
      (famF hσ hs hp hu hI hμ Φ w) = famF hσ hs hp hu hI hμ Φ' w :=
  indExt fun h x => by
    show gjInt m μ σ Bf Φ.1 (h * h₀) _ w = gjInt m μ σ Bf Φ'.1 h _ w
    rw [hΦ, gjInt_translate]

theorem famF_shift [m.IsMulRightInvariant] (hμ : IsSmoothChar μ)
    (Φ Φ' : SB (Matrix (Fin (r + t)) (Fin r) k)) (g₀ : GL (Fin r) k)
    (hΦ : Φ'.1 = om μ g₀ 1 Φ.1) (w : V) :
    famF hσ hs hp hu hI hμ Φ' w = famF hσ hs hp hu hI hμ Φ (σ g₀⁻¹ w) :=
  indExt fun h x => by
    show gjInt m μ σ Bf Φ'.1 h _ w = gjInt m μ σ Bf Φ.1 h _ _
    rw [hΦ, gjInt_shift hu]

end Family

section Abstract

variable {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem form_injective (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (a b : V) (h : ∀ w, Bf a w = Bf b w) :
    a = b := by
  by_contra hab
  have h1 := hp (a - b) (sub_ne_zero.2 hab)
  have h2 : Bf (a - b) (a - b) = 0 := by
    rw [Bf.map_sub a b, LinearMap.sub_apply, h, sub_self]
  rw [h2] at h1
  simp at h1

theorem abstract_pairing {S A X : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup X] [Module ℂ X] (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (P : A →ₗ[ℂ] X →ₗ[ℂ] ℂ) (F : S → V → A)
    (h1 : ∀ Φ Φ' w, F (Φ + Φ') w = F Φ w + F Φ' w) (h2 : ∀ (c : ℂ) Φ w, F (c • Φ) w = c • F Φ w)
    (h3 : ∀ Φ w w', F Φ (w + w') = F Φ w + F Φ w')
    (h4 : ∀ (c : ℂ) Φ w, F Φ (c • w) = starRingEnd ℂ c • F Φ w)
    (hR : ∀ Φ f (L : V →ₗ⋆[ℂ] ℂ), (∀ w, L w = P (F Φ w) f) → ∃ u, ∀ w, L w = Bf u w) :
    ∃ B : S →ₗ[ℂ] X →ₗ[ℂ] V, ∀ Φ f w, Bf (B Φ f) w = P (F Φ w) f := by
  have hL : ∀ Φ f, ∃ u : V, ∀ w, P (F Φ w) f = Bf u w := fun Φ f =>
    hR Φ f { toFun := fun w => P (F Φ w) f
             map_add' := fun w w' => by simp [h3]
             map_smul' := fun c w => by simp [h4] } fun _ => rfl
  choose u hu' using hL
  have huniq := form_injective hp
  refine ⟨LinearMap.mk₂ ℂ u
      (fun Φ Φ' f => huniq _ _ fun w => ?_) (fun c Φ f => huniq _ _ fun w => ?_)
      (fun Φ f f' => huniq _ _ fun w => ?_) (fun c Φ f => huniq _ _ fun w => ?_),
    fun Φ f w => (hu' Φ f w).symm⟩
  · simp [← hu', h1]
  · simp [← hu', h2]
  · simp [← hu']
  · simp [← hu']

theorem abstract_equiv {H A X : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [AddCommGroup A] [Module ℂ A] [AddCommGroup X] [Module ℂ X]
    (I : Representation ℂ H A) (π : Representation ℂ H X) (Ψ : I.Equiv (contra π)) :
    ∃ P : A →ₗ[ℂ] X →ₗ[ℂ] ℂ, (∀ h a f, P (I h a) (π h f) = P a f) ∧
      ∀ a, (∀ f, P a f = 0) → a = 0 := by
  refine ⟨(smoothPart π.dual).subtype ∘ₗ Ψ.toLinearEquiv.toLinearMap, fun h a f => ?_, fun a h => ?_⟩
  · have e1 : Ψ.toLinearEquiv (I h a) = contra π h (Ψ.toLinearEquiv a) :=
      LinearMap.congr_fun (Ψ.isIntertwining' h) a
    show (Ψ.toLinearEquiv (I h a)).1 _ = (Ψ.toLinearEquiv a).1 f
    rw [e1]
    show (Ψ.toLinearEquiv a).1 (π h⁻¹ _) = _
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · have : Ψ.toLinearEquiv a = 0 := Subtype.ext (LinearMap.ext h)
    exact (LinearEquiv.map_eq_zero_iff _).1 this

end Abstract

section Pairing

variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
  [m.IsMulLeftInvariant] [m.IsMulRightInvariant] (hσ : IsSmooth σ)
  (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
  (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
  (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
    Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
    Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)

omit [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)] in

theorem exists_stab (hμ : IsSmoothChar μ) (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) :
    ∃ S : Subgroup (GL (Fin r) k), IsOpen (S : Set (GL (Fin r) k)) ∧ ∀ s ∈ S, om μ s 1 Φ.1 = Φ.1 := by
  have h := (om_isSmoothRepresentation k (Fin r) (Fin (r + t)) μ hμ).2.2.2.2 Φ.1 Φ.2
  have hc : Continuous fun g : GL (Fin r) k => (g, (1 : GL (Fin (r + t)) k)) :=
    continuous_id.prodMk continuous_const
  refine ⟨{ carrier := {g | om μ g 1 Φ.1 = Φ.1}
            one_mem' := om_one μ Φ.1
            mul_mem' := fun {x y} hx hy => ?_
            inv_mem' := fun {x} hx => ?_ }, h.preimage hc, fun s hs => hs⟩
  · have := om_mul μ x y (1 : GL (Fin (r + t)) k) 1 Φ.1
    rw [mul_one] at this
    show om μ (x * y) 1 Φ.1 = Φ.1
    rw [this, show om μ y 1 Φ.1 = Φ.1 from hy]
    exact hx
  · have := om_mul μ x⁻¹ x (1 : GL (Fin (r + t)) k) 1 Φ.1
    rw [mul_one, inv_mul_cancel, om_one, show om μ x 1 Φ.1 = Φ.1 from hx] at this
    exact this.symm

theorem exists_pairing (hμ : IsSmoothChar μ) (hadm : IsAdmissible σ)
    (P : IndSp (two (stdSum (rfl : r + t = r + t))) (contra (leviRep t μ σ)) →ₗ[ℂ]
      IndSp (two (stdSum (rfl : r + t = r + t))) (leviRep t μ σ) →ₗ[ℂ] ℂ)
    (hP : ∀ (h : GL (Fin (r + t)) k) a f,
      P (parInd (two (stdSum (rfl : r + t = r + t))) (contra (leviRep t μ σ)) h a)
        (parInd (two (stdSum (rfl : r + t = r + t))) (leviRep t μ σ) h f) = P a f)
    (hQ : ∀ a, (∀ f, P a f = 0) → a = 0)
    (Φ₀ : SB (Matrix (Fin (r + t)) (Fin r) k)) (w₀ : V)
    (hne : famF hσ hs hp hu hI hμ Φ₀ w₀ ≠ 0) :
    ThetaPair μ σ (prod₂ σ (detRep (Fin t) μ)) := by
  obtain ⟨B, hB⟩ := abstract_pairing hp P (famF hσ hs hp hu hI hμ)
    (famF_add_fun hσ hs hp hu hI hμ) (fun c Φ w => famF_smul_fun hσ hs hp hu hI hμ c Φ w)
    (famF_add_right hσ hs hp hu hI hμ) (fun c Φ w => famF_smul_right hσ hs hp hu hI hμ c Φ w)
    (fun Φ f L hL => by
      obtain ⟨S, hSo, hS⟩ := exists_stab (t := t) hμ Φ
      refine GlobalTheory.T.unitary_admissible_matrix_coefficient k r V σ Bf hadm hs hp hu L S hSo fun s hsS w => ?_
      have := famF_shift hσ hs hp hu hI hμ Φ Φ s⁻¹ (hS _ (inv_mem hsS)).symm w
      rw [inv_inv] at this
      rw [hL, hL, ← this])
  refine ⟨B, fun h0 => hne (hQ _ fun f => ?_), fun g h Φ Φ' hΦ' f => form_injective hp _ _ fun w => ?_⟩
  · rw [← hB, h0]
    simp
  · have hw : Bf (σ g (B Φ f)) w = Bf (B Φ f) (σ g⁻¹ w) := by
      rw [← hu g (B Φ f) (σ g⁻¹ w), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    let Φ₁ : SB (Matrix (Fin (r + t)) (Fin r) k) := ⟨om μ g 1 Φ.1, om_mem_SB μ g 1 Φ.2⟩
    have h1 : Φ'.1 = om μ 1 h Φ₁.1 := by
      have := om_mul μ 1 g h 1 Φ.1
      rw [one_mul, mul_one] at this
      exact hΦ'.trans this
    have e1 : Bf (B Φ' (parInd (two (stdSum (rfl : r + t = r + t))) (leviRep t μ σ) h f)) w =
        P (famF hσ hs hp hu hI hμ Φ' w) (parInd (two (stdSum (rfl : r + t = r + t))) (leviRep t μ σ) h f) :=
      hB Φ' _ w
    have e2 : Bf (B Φ f) (σ g⁻¹ w) = P (famF hσ hs hp hu hI hμ Φ (σ g⁻¹ w)) f := hB Φ f _
    have e3 := famF_shift hσ hs hp hu hI hμ Φ Φ₁ g rfl w
    have e4 := famF_translate hσ hs hp hu hI hμ Φ₁ Φ' h h1 w
    refine e1.trans (Eq.trans ?_ (hw.trans e2).symm)
    exact (congrArg (fun a => P a (parInd (two (stdSum (rfl : r + t = r + t))) (leviRep t μ σ) h f)) e4).symm.trans
      ((hP h _ f).trans (congrArg (fun a => P a f) e3))

end Pairing

section NonVanishing

variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
  [m.IsMulLeftInvariant] [m.IsOpenPosMeasure] (hσ : IsSmooth σ)
  (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
  (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
  (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
    Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
    Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)

theorem exists_famF_ne_zero (hμ : IsSmoothChar μ) {v : V} (hv : v ≠ 0) :
    ∃ Φ : SB (Matrix (Fin (r + t)) (Fin r) k), famF hσ hs hp hu hI hμ Φ v ≠ 0 := by
  set S : Set (GL (Fin r) k) := {g | σ g v = v ∧ μ (Matrix.GeneralLinearGroup.det g) = 1 ∧
    nabs k (Matrix.GeneralLinearGroup.det g) = 1} with hSdef
  have hS1 : S ∈ 𝓝 (1 : GL (Fin r) k) := by
    filter_upwards [(hσ v).mem_nhds (by simp), eventually_det_trivial (Fin r) hμ] with g h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨Φ, hΦ, hΦ1, h01, hΦS⟩ := GlobalTheory.T.exists_schwartz_bump_near_identity k r t (interior S) isOpen_interior
    (mem_interior_iff_mem_nhds.2 hS1)
  refine ⟨⟨Φ, hΦ⟩, fun h0 => ?_⟩
  have hcont : Continuous fun g : GL (Fin r) k => Φ (eMat k r t * g.val) :=
    (hΦ.1.comp_continuous (continuous_const.matrix_mul Units.continuous_val)).continuous
  set φ : GL (Fin r) k → ℝ := fun g => (Φ (eMat k r t * g.val)).re with hφ
  have hom : ∀ g : GL (Fin r) k, om μ g 1 Φ (eMat k r t) = (φ g : ℂ) := by
    intro g
    have hm : ((1 : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * g.val = eMat k r t * g.val := by
      simp
    simp only [om, hm]
    by_cases hg : Φ (eMat k r t * g.val) = 0
    · simp [hφ, hg]
    · obtain ⟨-, h2, h3⟩ := interior_subset (hΦS g hg)
      have h4 : Φ (eMat k r t * g.val) = 1 := (h01 _).resolve_left hg
      simp [hφ, h2, h3, h4, nabs_one]
  have hint : Integrable φ m := by
    have := (hI 1 Φ hΦ).re
    refine this.congr (ae_of_all _ fun g => ?_)
    simp [hom g]
  have hnn : 0 ≤ φ := fun g => by
    rcases h01 (eMat k r t * g.val) with h | h <;> simp [hφ, h]
  have hpos : 0 < ∫ g, φ g ∂m := by
    refine (integral_pos_iff_support_of_nonneg hnn hint).2 ?_
    have hc : Continuous φ := Complex.continuous_re.comp hcont
    refine hc.isOpen_support.measure_pos m ⟨1, ?_⟩
    have : eMat k r t * (1 : GL (Fin r) k).val = eMat k r t := by simp
    simp [hφ, this, hΦ1]
  have hval : gjInt m μ σ Bf Φ 1 v v = ((∫ g, φ g ∂m : ℝ) : ℂ) * Bf v v := by
    rw [← integral_complex_ofReal, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    show om μ g 1 Φ (eMat k r t) * coef σ Bf v v g = (φ g : ℂ) * Bf v v
    rw [hom g]
    by_cases hg : Φ (eMat k r t * g.val) = 0
    · simp [hφ, hg]
    · obtain ⟨h1, -, -⟩ := interior_subset (hΦS g hg)
      simp only [coef]
      rw [fix_inv h1]
  have hz : gjInt m μ σ Bf Φ 1 v v = 0 := by
    have h1 := famF_apply hσ hs hp hu hI hμ ⟨Φ, hΦ⟩ v 1 (v ⊗ₜ (1 : ℂ))
    rw [h0] at h1
    simpa using h1.symm
  rw [hval] at hz
  rcases mul_eq_zero.1 hz with h | h
  · exact hpos.ne' (by exact_mod_cast h)
  · have := hp v hv
    simp [h] at this

end NonVanishing

end GlobalTheory.GodementJacquet

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published in

theorem GlobalTheory.GodementJacquet.thetaPair_prod_det : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V), r < t → IsSmoothChar μ → IsUnitaryChar μ → IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → ThetaPair μ σ (prod₂ σ (detRep (Fin t) μ)) := by
  intro hBZ k _ _ _ _ r t μ V _ _ σ hrt hμ hμu hσ hirr huni
  obtain ⟨hadmAll, -, -, hIC⟩ := hBZ k
  have hadm := hadmAll (Fin r) V σ hσ hirr
  obtain ⟨Bf, hs, hp, hu⟩ := huni
  have hV : ∃ v : V, v ≠ 0 := by
    by_contra hc
    push_neg at hc
    haveI : IsSimpleOrder (Subrepresentation σ) := hirr
    refine bot_ne_top (α := Subrepresentation σ) (Subrepresentation.toSubmodule_injective ?_)
    ext x
    rw [hc x]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  obtain ⟨v, hv⟩ := hV
  borelize k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨i1, i2, i3, -, -, -, i7, i8⟩ := volGL_haar k (Fin r) (MeasureTheory.Measure.addHaar : MeasureTheory.Measure k)
  have hI := fun h Φ hΦ => GlobalTheory.T.theta_integral_integrable k (MeasureTheory.Measure.addHaar : MeasureTheory.Measure k) r t μ hrt.le hμ hμu h Φ hΦ
  have hρ : IsSmooth (GlobalTheory.GodementJacquet.leviRep t μ σ) :=
    isSmooth_comp (isSmooth_extTensor hσ ((isSmooth_ofChar_iff _).2 hμ.detChar)) _
      ((continuous_apply false).prodMk (continuous_apply true))
  obtain ⟨Ψ⟩ := hIC.nonempty_equiv (GlobalTheory.SmGL.two (stdSum (rfl : r + t = r + t))) hρ
  obtain ⟨P, hP, hQ⟩ := GlobalTheory.GodementJacquet.abstract_equiv _ _ Ψ
  obtain ⟨Φ₀, hne⟩ := GlobalTheory.GodementJacquet.exists_famF_ne_zero hσ hs hp hu hI hμ hv
  exact GlobalTheory.GodementJacquet.exists_pairing hσ hs hp hu hI hμ hadm P hP hQ Φ₀ v hne
