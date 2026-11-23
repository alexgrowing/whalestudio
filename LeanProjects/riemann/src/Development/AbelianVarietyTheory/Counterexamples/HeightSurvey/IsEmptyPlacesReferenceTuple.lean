import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedMY
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilUnr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.MeasTuple

theorem one_sub_pos {q : ℝ} (hq : 1 < q) {i : ℕ} (hi : 1 ≤ i) : 0 < 1 - q ^ (-(i : ℤ)) := by
  have : q ^ (-(i : ℤ)) < 1 := zpow_lt_one_of_neg₀ hq (by omega)
  linarith

theorem prod_pos' {q : ℝ} (hq : 1 < q) (n : ℕ) : 0 < ∏ i ∈ Finset.Icc 1 n, (1 - q ^ (-(i : ℤ))) :=
  Finset.prod_pos fun _ hi => one_sub_pos hq (Finset.mem_Icc.1 hi).1

theorem parIdx_pos {q : ℝ} (hq : 1 < q) (r s : ℕ) : 0 < parIdx q r s := by
  unfold parIdx
  have := prod_pos' hq (r + s); have := prod_pos' hq r; have := prod_pos' hq s
  have : 0 < q := by linarith
  positivity

theorem parIdx_zero {q : ℝ} (hq : 1 < q) (r : ℕ) : parIdx q r 0 = 1 := by
  unfold parIdx
  have := (prod_pos' hq r).ne'
  simp only [mul_zero, pow_zero, add_zero, one_mul]
  rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from rfl, Finset.prod_empty, mul_one, div_self this]

variable {D : D7}

theorem isEmpty_places_reference_tuple (Z : DivX D) : IsEmpty (Z.QPl D.what₂.mu0) := by
  refine ⟨fun v => ?_⟩
  obtain ⟨p, hp, -⟩ := Z.qv_char _ (Or.inl rfl) v
  rw [Z.degreeZero_partial_set_empty] at hp
  simp at hp

def setMY (X : ThetaX D) (Z : DivX D) : ThetaX D :=
  { X with
    mY := fun μ j => ∏ v : Z.QPl μ, parIdx (Z.qv μ v) D.R.r (j * D.R.t)
    mY_pos := fun μ j => Finset.prod_pos fun v _ => parIdx_pos (by exact_mod_cast Z.qv_gt μ v) _ _
    adelicDataRowMeasureScale_trivialTuple := fun j => by
      haveI := isEmpty_places_reference_tuple Z
      exact Fintype.prod_empty _
    mY_zero := fun μ => Finset.prod_eq_one fun v _ => by
      rw [zero_mul]; exact parIdx_zero (by exact_mod_cast Z.qv_gt μ v) _ }

theorem myTied_setMY (X : ThetaX D) (Z : DivX D) : ThetaDivisorCompatibility (setMY X Z) Z := fun _ _ _ => rfl

def thetaDivisorRestriction {X : ThetaX D} (T : ThetaTied D X) (Z : DivX D) : ThetaTied D (setMY X Z) :=
  { T with }

def rep (Z : DivX D) (n : ℕ) : DivX D :=
  { Z with
    QPl := fun μ => Fin n × Z.QPl μ
    finQ := fun _ => inferInstance
    qv := fun μ v => Z.qv μ v.2
    qv_gt := fun μ v => Z.qv_gt μ v.2
    qv_char := fun μ h v => Z.qv_char μ h v.2
    nu := fun μ v => Z.nu μ v.2
    nu_ne := fun μ v => Z.nu_ne μ v.2
    nu_abs := fun μ v => Z.nu_abs μ v.2
    ZQ := fun μ v => Z.ZQ μ v.2
    quotientLocalValueFirst := fun μ v => Z.quotientLocalValueFirst μ v.2
    typeDim := fun μ v => Z.typeDim μ v.2 }

theorem mY_rep (X : ThetaX D) (Z : DivX D) (n : ℕ) (μ : D.what₂.Tup) (j : ℕ) :
    (setMY X (rep Z n)).mY μ j = (setMY X Z).mY μ j ^ n := by
  change ∏ v : Fin n × Z.QPl μ, parIdx (Z.qv μ v.2) D.R.r (j * D.R.t) =
    (∏ v : Z.QPl μ, parIdx (Z.qv μ v) D.R.r (j * D.R.t)) ^ n
  rw [Fintype.prod_prod_type]
  simp

theorem trivial_factor (X : ThetaX D) (Z : DivX D) :
    ThetaDivisorCompatibility (setMY X (rep Z 0)) (rep Z 0) ∧ (rep Z 0).Qp = Z.Qp ∧ ∀ μ j, (setMY X (rep Z 0)).mY μ j = 1 :=
  ⟨myTied_setMY _ _, rfl, fun μ j => by rw [mY_rep, pow_zero]⟩

open IsDedekindDomain NumberField in

def PlacesTied {X : ThetaX D} (T : ThetaTied D X) (Z : DivX D) : Prop :=
  ∀ μ, ∃ e : Z.QPl μ ↪ HeightOneSpectrum (𝓞 D.host.F), (∀ v, Z.qv μ v = Ideal.absNorm (e v).asIdeal) ∧
    ∀ S, UnramOutside D (T.eChr (X.chrOf μ 1 * (X.chrOf D.what₂.mu0 1)⁻¹)) S ↔ ∀ v, e v ∈ S

end GlobalTheory.MeasTuple

end
