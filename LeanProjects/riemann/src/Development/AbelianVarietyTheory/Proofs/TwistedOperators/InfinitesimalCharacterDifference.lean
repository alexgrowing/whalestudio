import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightFunctionalCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfandStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlRelationsOnKFiniteVectorsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedModuleNontrivialStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommonKernelCommutingNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalInvariantSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairChangeOfBasisStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairInFirstFlagSpaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairSplitTorusStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableSubspaceExponentFunctionalStatement
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

noncomputable section

namespace GlobalTheory.IndCap

theorem epow_eq_pow' {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (m : ℕ) (a b : Fin n) :
    epow E m a b = (Matrix.of E ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp [epow, pow_succ, Matrix.mul_apply, ih]

theorem etr_succ_eq_gelfA' {B : Type} [Ring B] [Algebra ℂ B] {n : ℕ} (E : Fin n → Fin n → B) (k : ℕ) :
    etr E (k + 1) = GlobalTheory.SmoothForms.gelfA E k := by
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]; simp [etr, epow_eq_pow']

theorem commute_epow' {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (z : B)
    (hz : ∀ a b, Commute z (E a b)) (m : ℕ) (a b : Fin n) : Commute z (epow E m a b) := by
  induction m generalizing a b with
  | zero => simp only [epow]; split_ifs <;> simp
  | succ m ih => simp only [epow]; exact Commute.sum_right _ _ _ fun c _ => (ih a c).mul_right (hz c b)

theorem commute_etr' {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (z : B)
    (hz : ∀ a b, Commute z (E a b)) (m : ℕ) : Commute z (etr E m) :=
  Commute.sum_right _ _ _ fun a _ => commute_epow' E z hz m a a

theorem lift_etr' {n : ℕ} {B : Type} [Ring B] [Algebra ℂ B] (φ : Fin n × Fin n → B) (m : ℕ) :
    FreeAlgebra.lift ℂ φ (etr (Egl n) m) = etr (fun a b => φ (a, b)) m := by
  have key : ∀ a b, FreeAlgebra.lift ℂ φ (epow (Egl n) m a b) = epow (fun a b => φ (a, b)) m a b := by
    induction m with
    | zero => intro a b; simp only [epow]; split_ifs <;> simp
    | succ m ih => intro a b; simp [epow, map_sum, map_mul, ih, Egl]
  simp [etr, map_sum, key]

section Restr
variable {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (V : Submodule ℂ M)
  (E : Fin n → Fin n → Module.End ℂ M) (hE : ∀ a b, ∀ v ∈ V, E a b v ∈ V)

theorem epow_restrict' (m : ℕ) (a b : Fin n) (v : V) :
    ((epow (fun a b => (E a b).restrict (hE a b)) m a b v : V) : M) = epow E m a b v := by
  induction m generalizing a b v with
  | zero => simp only [epow]; split_ifs <;> simp
  | succ m ih =>
    simp only [epow, LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, ih]
    rfl

theorem glRel_restrict' (h : GlRel E) : GlRel (fun a b => (E a b).restrict (hE a b)) := by
  intro a b c d
  ext v
  have := congrArg (fun F => F (v : M)) (h a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, LinearMap.restrict_apply]
  rw [this]
  split_ifs <;> simp
end Restr

theorem infChar_sub_eq_of_line : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a), I.j ⟨0, h⟩ = 1 → ∀ χ : Fin n → ℂ, (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) → ∃ i j, i ≠ j ∧ χ i - χ j = I.s ⟨0, h⟩ := by
  intro hLC n ε I h hj χ hnil
  obtain ⟨hInd, -⟩ := hLC
  obtain ⟨hadm, -, hgk, -⟩ := hInd n ε I
  obtain ⟨A, hA1, hA2, hA3, hA4, -⟩ := GlobalTheory.T.gl_relations_on_k_finite_vectors n ε I.H I.ρ hadm hgk
  set E0 : Fin n → Fin n → Module.End ℂ (kFinVec ε I.ρ) := fun a b => A (Matrix.single a b 1) with hE0
  have hGl0 : GlRel E0 := by simpa using (hA2 1 isUnit_one).1
  set T : ℕ → Module.End ℂ (kFinVec ε I.ρ) := fun k => etr E0 (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1)) with hT
  have hcommE : ∀ k a b, Commute (etr E0 (k + 1)) (E0 a b) := fun k a b => by
    rw [etr_succ_eq_gelfA']; exact (GlobalTheory.SmoothForms.commute_gelfA _ n E0 hGl0 k a b).symm
  have hcommTE : ∀ k a b, Commute (T k) (E0 a b) := fun k a b =>
    (hcommE k a b).sub_left (Algebra.commute_algebraMap_left _ _)
  have hTcomm : ∀ k l, Commute (T k) (T l) := fun k l =>
    ((commute_etr' E0 _ (hcommTE k) (l + 1))).sub_right (Algebra.commute_algebraMap_right _ _)
  have hnilT : ∀ k (v : kFinVec ε I.ρ), ∃ N : ℕ, (T k ^ N) v = 0 := fun k v => by
    obtain ⟨N, hN⟩ := hnil k v v.2
    refine ⟨N, ?_⟩
    rw [hA3] at hN
    have e : FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => A (Matrix.single ab.1 ab.2 1))
        ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) = T k ^ N := by
      rw [map_pow, map_sub, AlgHom.commutes, lift_etr']
    rw [e] at hN
    exact Subtype.ext (by simpa using hN)
  have hTK : ∀ κ ∈ Kset ε, ∀ (k : ℕ) (v w : kFinVec ε I.ρ), (w : I.H) = I.ρ κ v →
      ((T k w : kFinVec ε I.ρ) : I.H) = I.ρ κ (T k v : I.H) := fun κ hκ k v w hw => by
    have := hA4 κ hκ (k + 1) v w hw
    simp only [hT, LinearMap.sub_apply, Submodule.coe_sub, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, Submodule.coe_smul, this, hw, map_sub, map_smul]
  haveI : Nontrivial I.H := GlobalTheory.T.induced_module_nontrivial n ε I
  obtain ⟨S, hSfd, hS0, hST⟩ := GlobalTheory.T.finite_dimensional_invariant_subspace n ε I.H I.ρ hadm T hTK
  obtain ⟨v₀, -, hv₀, hv₀T⟩ := GlobalTheory.T.common_kernel_commuting_nilpotent _ T S hSfd hS0 hST hTcomm (fun k v _ => hnilT k v)
  set Y : Submodule ℂ (kFinVec ε I.ρ) := ⨅ k : ℕ, LinearMap.ker (T k) with hY
  have memY : ∀ w, w ∈ Y ↔ ∀ k, T k w = 0 := fun w => by simp [hY, Submodule.mem_iInf]
  have hYE : ∀ a b, ∀ w ∈ Y, E0 a b w ∈ Y := fun a b w hw => (memY _).2 fun k => by
    rw [← Module.End.mul_apply, (hcommTE k a b).eq, Module.End.mul_apply, (memY w).1 hw k, map_zero]
  have hYA : ∀ Z : Matrix (Fin n) (Fin n) ℂ, ∀ w ∈ Y, A Z w ∈ Y := fun Z w hw => by
    rw [Matrix.matrix_eq_sum_single Z]
    simp only [map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    rw [show Matrix.single a b (Z a b) = Z a b • Matrix.single a b 1 by simp [Matrix.smul_single], map_smul,
      LinearMap.smul_apply]
    exact Y.smul_mem _ (hYE a b w hw)

  have hv₀Y : v₀ ∈ Y := (memY v₀).2 hv₀T
  set Y' : Submodule ℂ I.H := Y.map (kFinVec ε I.ρ).subtype with hY'
  have hY'le : Y' ≤ kFinVec ε I.ρ := Submodule.map_subtype_le _ _
  have hY'0 : Y' ≠ ⊥ := by
    intro e
    have : ((v₀ : kFinVec ε I.ρ) : I.H) ∈ Y' := Submodule.mem_map_of_mem hv₀Y
    rw [e, Submodule.mem_bot] at this
    exact hv₀ (Subtype.ext this)
  have hY'K : IsKStableOn ε I.ρ Y' := by
    rintro g hg _ ⟨w, hw, rfl⟩
    have hm : I.ρ g (w : I.H) ∈ kFinVec ε I.ρ := isKStableOn_kFinVec ε I.ρ g hg _ w.2
    refine ⟨⟨_, hm⟩, (memY _).2 fun k => Subtype.ext ?_, rfl⟩
    rw [hTK g hg k w ⟨_, hm⟩ rfl, (memY w).1 hw k]
    simp

  have hW1 : Module.finrank ℂ (I.W ⟨1, Nat.succ_lt_succ h⟩) = 1 := by
    have := I.flag.2.2.1 ⟨0, h⟩
    have hz : Module.finrank ℂ (I.W (⟨0, h⟩ : Fin I.a).castSucc) = 0 := Submodule.finrank_eq_zero.2 I.flag.1
    rw [hz, hj] at this
    exact this.trans (zero_add 1)
  obtain ⟨e, he1, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.1 hW1.ge)
  have hiso : star e ⬝ᵥ (Jm ε *ᵥ e) = 0 := by
    have hl : e ∈ I.W (Fin.last I.a) := I.flag.2.1 (Fin.le_last _) he1
    exact I.flag.2.2.2 e hl e hl
  obtain ⟨P, p, q, c, hPu, hpq, hPe, hPe', hG⟩ := GlobalTheory.T.hyperbolic_pair_change_of_basis n ε e he0 hiso
  have hPe1 : P *ᵥ Pi.single p 1 ∈ I.W ⟨1, Nat.succ_lt_succ h⟩ := hPe ▸ he1
  have hPe'' : P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) := by rw [hPe]; exact hPe'
  obtain ⟨hOffp, hOffq⟩ := GlobalTheory.T.hyperbolic_pair_in_first_flag_space n ε I.a I.j I.W h I.flag hj P p q c hPu hpq hPe1 hPe'' hG
  obtain ⟨hH₀, hsplit, hTc, hTcc⟩ := GlobalTheory.T.hyperbolic_pair_split_torus n ε I.a I.j I.W h I.flag hj P p q c hPu hpq hPe1 hPe'' hG
  set H₀ := P * diagonal (Pi.single p 1 - Pi.single q 1) * P⁻¹ with hH₀def
  set Tc := P * diagonal (Pi.single p Complex.I + Pi.single q Complex.I) * P⁻¹ with hTcdef
  obtain ⟨ℓ, γ, ⟨y, hyY, hy⟩, hℓN, hℓH, hℓT⟩ := GlobalTheory.T.k_stable_subspace_exponent_functional hInd n ε I h hj H₀ Tc hH₀ hTc hsplit hTcc Y' hY'le hY'0 hY'K

  set E' : Fin n → Fin n → Module.End ℂ Y := fun a b => (A (P * Matrix.single a b 1 * P⁻¹)).restrict
    (fun w hw => hYA _ w hw) with hE'
  have hGl' : GlRel E' := glRel_restrict' Y _ _ (hA2 P hPu).1
  have hetr' : ∀ (k : ℕ) (v : Y), etr E' (k + 1) v = gelfVal χ (k + 1) • v := fun k v => by
    apply Subtype.ext
    have e1 : ((etr E' (k + 1) v : Y) : kFinVec ε I.ρ) = etr (fun a b => A (P * Matrix.single a b 1 * P⁻¹)) (k + 1) v := by
      simp only [etr, LinearMap.sum_apply, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun a _ => epow_restrict' Y _ _ (k + 1) a a v
    rw [e1, (hA2 P hPu).2]
    have := (memY v).1 v.2 k
    simp only [hT, LinearMap.sub_apply, sub_eq_zero, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply] at this
    rw [this]; rfl
  have hqdet := GlobalTheory.T.qdet_apply_eq_prod_of_gelfVal Y n E' χ hGl' hetr'
  set ℓ' : Y →ₗ[ℂ] ℂ := ℓ ∘ₗ (kFinVec ε I.ρ).subtype ∘ₗ Y.subtype with hℓ'
  have hℓ'0 : ℓ' ≠ 0 := by
    obtain ⟨w, hw, rfl⟩ := hyY
    intro e0
    exact hy (by simpa [hℓ'] using LinearMap.congr_fun e0 ⟨w, hw⟩)

  have hE'v : ∀ a b (v : Y), ℓ' (E' a b v) =
      ℓ ((A (P * Matrix.single a b 1 * P⁻¹) (v : kFinVec ε I.ρ) : kFinVec ε I.ρ) : I.H) := fun a b v => rfl
  have hℓ'v : ∀ v : Y, ℓ' v = ℓ ((v : kFinVec ε I.ρ) : I.H) := fun v => rfl
  have hsplitA : ∀ (X X' : Matrix (Fin n) (Fin n) ℂ) (u v : ℂ) (w : Y), X ∈ lieSet ε → X' ∈ lieSet ε →
      ℓ ((A (u • X + v • X') (w : kFinVec ε I.ρ) : kFinVec ε I.ρ) : I.H) =
        u * ℓ (dRep I.ρ X ((w : kFinVec ε I.ρ) : I.H)) + v * ℓ (dRep I.ρ X' ((w : kFinVec ε I.ρ) : I.H)) := by
    intro X X' u v w hX hX'
    rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, map_add, map_smul, map_smul, hA1 X hX, hA1 X' hX',
      smul_eq_mul, smul_eq_mul]
  have hoffp : ∀ b, b ≠ p → ∀ v : Y, ℓ' (E' p b v) = 0 := fun b hb v => by
    obtain ⟨X, X', hX, hX', hXN, hX'N, he⟩ := hOffp b hb
    rw [hE'v, he, show X + Complex.I • X' = (1 : ℂ) • X + Complex.I • X' by rw [one_smul], hsplitA X X' _ _ v hX hX',
      hℓN X hX hXN _ (v : kFinVec ε I.ρ).2, hℓN X' hX' hX'N _ (v : kFinVec ε I.ρ).2]
    simp
  have hoffq : ∀ b, b ≠ q → ∀ v : Y, ℓ' (E' b q v) = 0 := fun b hb v => by
    obtain ⟨X, X', hX, hX', hXN, hX'N, he⟩ := hOffq b hb
    rw [hE'v, he, show X + Complex.I • X' = (1 : ℂ) • X + Complex.I • X' by rw [one_smul], hsplitA X X' _ _ v hX hX',
      hℓN X hX hXN _ (v : kFinVec ε I.ρ).2, hℓN X' hX' hX'N _ (v : kFinVec ε I.ρ).2]
    simp
  have hdiag : ∀ (u v : ℂ) (r : Fin n), (∀ i, diagonal (Pi.single r (1 : ℂ)) i i =
      u * (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) i + v * (Pi.single p Complex.I + Pi.single q Complex.I : Fin n → ℂ) i) →
      P * Matrix.single r r 1 * P⁻¹ = u • H₀ + v • Tc := by
    intro u v r hr
    have e : Matrix.single r r (1 : ℂ) = u • diagonal (Pi.single p 1 - Pi.single q 1) +
        v • diagonal (Pi.single p Complex.I + Pi.single q Complex.I) := by
      ext i k
      by_cases hik : i = k
      · subst hik
        have := hr i
        simp only [diagonal_apply_eq] at this
        simp only [Matrix.add_apply, Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul]
        rw [← this, Matrix.single_apply, Pi.single_apply]
        by_cases h' : r = i <;> simp [h', eq_comm]
      · have hn : ¬ (r = i ∧ r = k) := fun hh => hik (hh.1 ▸ hh.2)
        simp only [Matrix.add_apply, Matrix.smul_apply, diagonal_apply_ne _ hik, smul_zero, add_zero]
        rw [Matrix.single_apply, if_neg hn]
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
  have hDp : P * Matrix.single p p 1 * P⁻¹ = (1 / 2 : ℂ) • H₀ + (-(Complex.I / 2)) • Tc := hdiag _ _ p fun i => by
    by_cases hi : i = p
    · subst hi; simp [Pi.single_apply, hpq.symm]; ring_nf; rw [Complex.I_sq]; ring
    · by_cases hi' : i = q
      · subst hi'; simp [Pi.single_apply, hi]; ring_nf; rw [Complex.I_sq]; ring
      · simp [Pi.single_apply, hi, hi']
  have hDq : P * Matrix.single q q 1 * P⁻¹ = (-(1 / 2) : ℂ) • H₀ + (-(Complex.I / 2)) • Tc := hdiag _ _ q fun i => by
    by_cases hi : i = p
    · subst hi; simp [Pi.single_apply, hpq]; ring_nf; rw [Complex.I_sq]; ring
    · by_cases hi' : i = q
      · subst hi'; simp [Pi.single_apply, hi]; ring_nf; rw [Complex.I_sq]; ring
      · simp [Pi.single_apply, hi, hi']
  set α : ℂ := (1 / 2 : ℂ) * (I.s ⟨0, h⟩ + n - 1) + (-(Complex.I / 2)) * γ with hα
  set β : ℂ := (-(1 / 2) : ℂ) * (I.s ⟨0, h⟩ + n - 1) + (-(Complex.I / 2)) * γ with hβ
  have hdp : ∀ v : Y, ℓ' (E' p p v) = α * ℓ' v := fun v => by
    rw [hE'v, hDp, hsplitA _ _ _ _ v hH₀ hTc, hℓH _ (v : kFinVec ε I.ρ).2, hℓT _ (v : kFinVec ε I.ρ).2, hℓ'v, hα]
    ring
  have hdq : ∀ v : Y, ℓ' (E' q q v) = β * ℓ' v := fun v => by
    rw [hE'v, hDq, hsplitA _ _ _ _ v hH₀ hTc, hℓH _ (v : kFinVec ε I.ρ).2, hℓT _ (v : kFinVec ε I.ρ).2, hℓ'v, hβ]
    ring
  obtain ⟨i, k, hik, hi, hk⟩ := GlobalTheory.T.highest_weight_functional_character Y n E' χ hGl' hqdet p q hpq ℓ' α β hℓ'0 hoffp hoffq hdp hdq
  exact ⟨i, k, hik, by rw [hi, hk, hα, hβ]; ring⟩

end GlobalTheory.IndCap

end
