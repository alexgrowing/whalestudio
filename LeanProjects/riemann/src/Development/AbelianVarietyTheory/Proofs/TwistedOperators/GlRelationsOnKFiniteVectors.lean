import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandTraceConjInvertibleScalarMatrixStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryTracePowerCyclicWordsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FreeAlgebraLiftMonoidSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoefficientDerivativeFormulaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedRepConjMaxCompactIntertwinesStatement

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory.GKLie

theorem epow_intertwine {A : Type} [Ring A] {n : ℕ} (E E' : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, R * E a b = E' a b * R) : ∀ k a b, R * epow E k a b = epow E' k a b * R := by
  intro k
  induction k with
  | zero =>
    intro a b
    simp only [Formalism.REAL.epow]
    split_ifs <;> simp
  | succ k ih =>
    intro a b
    simp only [Formalism.REAL.epow, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc, ih, mul_assoc, h, ← mul_assoc]

theorem etr_intertwine {A : Type} [Ring A] {n : ℕ} (E E' : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, R * E a b = E' a b * R) (k : ℕ) : R * etr E k = etr E' k * R := by
  simp only [etr, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => epow_intertwine E E' R h k a a

theorem single_mul_single' {n : ℕ} (a b c d : Fin n) :
    (single a b (1 : ℂ)) * single c d 1 = if b = c then single a d 1 else 0 := by
  split_ifs with h
  · subst h; rw [single_mul_single_same, one_mul]
  · exact single_mul_single_of_ne _ _ _ _ h _

theorem conj_single {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    P * single a b 1 * P⁻¹ = ∑ c, ∑ d, (P c a * P⁻¹ b d) • single c d (1 : ℂ) := by
  ext i j
  simp [mul_apply, single_apply, Matrix.sum_apply, ite_and, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]

end GlobalTheory.GKLie

namespace GlobalTheory.GKLie

section Main

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem gAct_conj_glRel (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    GlRel (fun a b => gAct hρ hV (P * single a b 1 * P⁻¹)) := by
  have hPi : P⁻¹ * P = 1 := nonsing_inv_mul P ((isUnit_iff_isUnit_det P).1 hP)
  have hcb : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, P * X * P⁻¹ * (P * Y * P⁻¹) = P * (X * Y) * P⁻¹ := by
    intro X Y
    simp only [mul_assoc]
    rw [← mul_assoc P⁻¹ P, hPi, one_mul]
  intro a b c d
  simp only []
  rw [← gAct_bracket, hcb, hcb, ← sub_mul, ← mul_sub, single_mul_single', single_mul_single']
  split_ifs <;> simp [mul_sub, sub_mul]

theorem gAct_conj_sum (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (P : Matrix (Fin n) (Fin n) ℂ) :
    (fun a b => gAct hρ hV (P * single a b 1 * P⁻¹)) =
      fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • gAct hρ hV (single c d 1) := by
  funext a b
  rw [conj_single]
  simp only [map_sum, map_smul]

theorem gAct_conj_etr (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (k : ℕ) :
    etr (fun a b => gAct hρ hV (P * single a b 1 * P⁻¹)) k = etr (fun a b => gAct hρ hV (single a b 1)) k := by
  rw [gAct_conj_sum]
  exact GlobalTheory.T.gelfandTrace_conj_invertible_scalarMatrix (fun a b => gAct hρ hV (single a b 1)) P hP k

theorem dsigCW_eq (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (l : List (Fin n × Fin n)) (v : kFinVec ε ρ) :
    PI.DSInfCharCap.dsigCW ε ρ (l.map PI.DSInfCharCap.unitM) v =
      (((l.map fun ab : Fin n × Fin n => gAct hρ hV (single ab.1 ab.2 1)).prod v : kFinVec ε ρ) : H) := by
  induction l with
  | nil => simp [PI.DSInfCharCap.dsigCW]
  | cons x l ih =>
    rw [List.map_cons, PI.DSInfCharCap.dsigCW.eq_2, ih, List.map_cons, List.prod_cons, Module.End.mul_apply,
      gAct_coe]
    rfl

theorem actU_eq (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : kFinVec ε ρ) :
    actU ε ρ p (v : H) = ((FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => gAct hρ hV (single ab.1 ab.2 1)) p v :
      kFinVec ε ρ) : H) := by
  rw [GlobalTheory.T.freeAlgebra_lift_monoid_sum]
  unfold PI.DSInfCharCap.actU
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dsigCW_eq hρ hV]

end Main

end GlobalTheory.GKLie

namespace GlobalTheory.GKLie

section KPart

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kset_facts {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) :
    κᴴ * κ = 1 ∧ κ⁻¹ = κᴴ ∧ κ * Jm ε = Jm ε * κ ∧ κᴴ * Jm ε = Jm ε * κᴴ := by
  obtain ⟨hu, hc⟩ := hκ
  have h1 : κᴴ * κ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff'] at hu
    simpa [Matrix.star_eq_conjTranspose] using hu
  refine ⟨h1, Matrix.inv_eq_left_inv h1, hc, ?_⟩
  have := congrArg conjTranspose hc
  simpa [conjTranspose_mul, Jm_conjTranspose] using this.symm

theorem theta_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    PI.DSInfCharCap.thetaJ ε (κ * Y * κ⁻¹) = κ * PI.DSInfCharCap.thetaJ ε Y * κ⁻¹ := by
  obtain ⟨_, hinv, hc, hc'⟩ := kset_facts hκ
  rw [hinv]
  simp only [PI.DSInfCharCap.thetaJ, conjTranspose_mul, conjTranspose_conjTranspose, mul_neg, neg_mul, mul_assoc]
  rw [hc', ← mul_assoc (Jm ε) κ, ← hc, mul_assoc]

theorem cre_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cre ε (κ * Y * κ⁻¹) = κ * cre ε Y * κ⁻¹ := by
  unfold cre
  rw [theta_kconj hκ]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]

theorem cim_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cim ε (κ * Y * κ⁻¹) = κ * cim ε Y * κ⁻¹ := by
  unfold cim
  rw [theta_kconj hκ]
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm]

def kRes (hV : IsGKSub ε ρ (kFinVec ε ρ)) (κ : Matrix (Fin n) (Fin n) ℂ) (hκ : κ ∈ Kset ε) :
    Module.End ℂ (kFinVec ε ρ) :=
  (ρ κ : H →ₗ[ℂ] H).restrict (fun x hx => hV.kStable κ hκ x hx)

theorem kRes_coe (hV : IsGKSub ε ρ (kFinVec ε ρ)) (κ : Matrix (Fin n) (Fin n) ℂ) (hκ : κ ∈ Kset ε)
    (v : kFinVec ε ρ) : ((kRes hV κ hκ v : kFinVec ε ρ) : H) = ρ κ v := rfl

theorem gAct_kconj (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    kRes hV κ hκ * gAct hρ hV Y = gAct hρ hV (κ * Y * κ⁻¹) * kRes hV κ hκ := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, kRes_coe, gAct_coe, gAct_coe, kRes_coe, dsigC_eq, dsigC_eq,
    cre_kconj hκ, cim_kconj hκ,
    GlobalTheory.T.derivedRep_conj_maxCompact_intertwines n ε H ρ hρ κ hκ _ (cre_mem Y) v (hV.smooth v v.2),
    GlobalTheory.T.derivedRep_conj_maxCompact_intertwines n ε H ρ hρ κ hκ _ (cim_mem Y) v (hV.smooth v v.2), map_add, map_smul]

theorem etr_kequiv (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (k : ℕ) (v w : kFinVec ε ρ) (hw : (w : H) = ρ κ v) :
    ((etr (fun a b => gAct hρ hV (single a b 1)) k w : kFinVec ε ρ) : H) =
      ρ κ ((etr (fun a b => gAct hρ hV (single a b 1)) k v : kFinVec ε ρ) : H) := by
  have hw' : w = kRes hV κ hκ v := Subtype.ext (by rw [hw, kRes_coe])
  have hU : IsUnit κ := (isUnit_iff_isUnit_det κ).2 (isUnit_det_of_left_inverse (kset_facts hκ).1)
  have hint := etr_intertwine (fun a b => gAct hρ hV (single a b 1))
    (fun a b => gAct hρ hV (κ * single a b 1 * κ⁻¹)) (kRes hV κ hκ) (fun a b => gAct_kconj hρ hV hκ _) k
  rw [gAct_conj_etr hρ hV κ hU k] at hint
  rw [hw', ← kRes_coe hV κ hκ, ← Module.End.mul_apply, ← Module.End.mul_apply, hint]

theorem eword_coef (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ)) (w' : H) :
    ∀ (l : List (Fin n × Fin n)) (u : kFinVec ε ρ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Eword ε l (fun x => ⟪w', ρ x u⟫_ℂ) g =
        ⟪w', ρ g (((l.map fun ab : Fin n × Fin n => gAct hρ hV (single ab.1 ab.2 1)).prod u : kFinVec ε ρ) : H)⟫_ℂ := by
  intro l
  induction l with
  | nil => intro u g _; simp [Formalism.REAL.Eword]
  | cons p l ih =>
    intro u g hg
    rw [Formalism.REAL.Eword.eq_2]
    beta_reduce
    rw [GlobalTheory.T.matrix_coefficient_derivative_formula n ε H ρ hρ _ (hV.smooth _ ((l.map fun ab : Fin n × Fin n =>
      gAct hρ hV (single ab.1 ab.2 1)).prod u).2) w' _ (fun g' hg' => ih u g' hg') p.1 p.2 g hg]
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, gAct_coe]

theorem gelf_coef (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ)) (w' : H) (m : ℕ)
    (v : kFinVec ε ρ) :
    GlobalTheory.Dec.gelf ε m (fun x => ⟪w', ρ x v⟫_ℂ) 1 =
      ⟪w', ((etr (fun a b => gAct hρ hV (single a b 1)) (m + 1) v : kFinVec ε ρ) : H)⟫_ℂ := by
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [Formalism.REAL.inUJ]
  unfold GlobalTheory.Dec.gelf
  rw [GlobalTheory.T.elementary_trace_power_cyclic_words]
  simp only [eword_coef hρ hV w' _ v 1 h1, hρ.1, ContinuousLinearMap.one_apply, LinearMap.sum_apply,
    Submodule.coe_sum, inner_sum]

theorem etr_infChar (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ)) (χ : Fin n → ℂ)
    (hχ : HasInfChar ε χ ρ) (k : ℕ) (v : kFinVec ε ρ) :
    etr (fun a b => gAct hρ hV (single a b 1)) (k + 1) v = gelfVal χ (k + 1) • v := by
  set T := etr (fun a b => gAct hρ hV (single a b 1)) (k + 1) with hT
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [Formalism.REAL.inUJ]
  have key : ∀ w' : kFinVec ε ρ, ⟪(w' : H), (T v : H)⟫_ℂ = gelfVal χ (k + 1) * ⟪(w' : H), (v : H)⟫_ℂ := by
    intro w'
    have := (hχ v w' v.2 w'.2).2 k 1 h1
    rw [gelf_coef hρ hV] at this
    simpa [hρ.1] using this
  set z : kFinVec ε ρ := T v - gelfVal χ (k + 1) • v with hz
  have hzH : (z : H) = (T v : H) - gelfVal χ (k + 1) • (v : H) := by
    rw [hz, Submodule.coe_sub, Submodule.coe_smul]
  have hzz : ⟪(z : H), (z : H)⟫_ℂ = 0 := by
    conv_lhs => arg 3; rw [hzH]
    rw [inner_sub_right, inner_smul_right, key z, sub_self]
  have h0 : (z : H) = 0 := inner_self_eq_zero.1 hzz
  exact sub_eq_zero.1 (Subtype.ext h0)

end KPart

theorem kFin_glModule : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → IsGKSub ε ρ (kFinVec ε ρ) → ∃ A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (kFinVec ε ρ), (∀ X ∈ lieSet ε, ∀ v, ((A X v : kFinVec ε ρ) : H) = dRep ρ X v) ∧ (∀ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P → GlRel (fun a b => A (P * Matrix.single a b 1 * P⁻¹)) ∧ ∀ k : ℕ, etr (fun a b => A (P * Matrix.single a b 1 * P⁻¹)) k = etr (fun a b => A (Matrix.single a b 1)) k) ∧ (∀ (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : kFinVec ε ρ), actU ε ρ p (v : H) = ((FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => A (Matrix.single ab.1 ab.2 1)) p v : kFinVec ε ρ) : H)) ∧ (∀ κ ∈ Kset ε, ∀ (k : ℕ) (v w : kFinVec ε ρ), (w : H) = ρ κ v → ((etr (fun a b => A (Matrix.single a b 1)) k w : kFinVec ε ρ) : H) = ρ κ ((etr (fun a b => A (Matrix.single a b 1)) k v : kFinVec ε ρ) : H)) ∧ ∀ χ : Fin n → ℂ, HasInfChar ε χ ρ → ∀ (k : ℕ) v, etr (fun a b => A (Matrix.single a b 1)) (k + 1) v = gelfVal χ (k + 1) • v := by
  intro n ε H _ _ _ ρ hadm hV
  have hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ := hadm.1
  exact ⟨gAct hρ hV, fun X hX v => gAct_of_mem hρ hV hX v,
    fun P hP => ⟨gAct_conj_glRel hρ hV P hP, gAct_conj_etr hρ hV P hP⟩, fun p v => actU_eq hρ hV p v,
    fun κ hκ k v w hw => etr_kequiv hρ hV hκ k v w hw, fun χ hχ k v => etr_infChar hρ hV χ hχ k v⟩

end GlobalTheory.GKLie
