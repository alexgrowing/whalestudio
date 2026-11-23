import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmAtComplZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.VolSqMulIndex
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExistsUnifFv

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.VolStabSW
  PI.VolStabSW.SdUniqW PI.VolStabSW.LatFactsW
open scoped TensorProduct

section Oev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem oev_add {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x + y ∈ OEv (E := E) v := Submodule.add_mem _ hx hy

theorem oev_zero : (0 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := Submodule.zero_mem _

theorem oev_neg {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : -x ∈ OEv (E := E) v :=
  Submodule.neg_mem _ hx

theorem oev_smul {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : s • x ∈ OEv (E := E) v :=
  Submodule.smul_mem _ (⟨s, hs⟩ : v.adicCompletionIntegers F) hx

theorem sdc_sc_mul (x : Fv F v) (c : Fv F v ⊗[F] E) : sc (E := E) v x * c = x • c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul y e => simp [sc, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add p q hp hq => rw [mul_add, hp, hq, smul_add]

theorem dV_int : dV v ∈ v.adicCompletionIntegers F := by
  unfold dV
  split_ifs with h
  · obtain ⟨x, _, he⟩ := h.choose_spec.2.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← he]
    rw [show algebraMap F (Fv F v) ((x : 𝓞 F) : F) = (((x : 𝓞 F) : F) : v.adicCompletion F) from rfl,
      v.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one x
  · exact one_mem _

theorem dV_ne_zero : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem psiV_zero (ψ : AddChar (AF F) ℂ) : psiV F ψ v 0 = 1 := by
  have hs : singleV F v (0 : Fv F v) = 0 := by
    have h := SdUniqW.singleV_add v (0 : Fv F v) 0
    rw [add_zero] at h
    simpa using h
  rw [psiV, hs]
  convert AddChar.map_zero_eq_one ψ
  rfl

theorem unif_ne_zero {ϖ : Fv F v} (h : IsUnif v ϖ) : ϖ ≠ 0 := by
  intro h0
  rw [IsUnif, h0, map_zero] at h
  exact WithZero.coe_ne_zero h.symm

theorem unif_int {ϖ : Fv F v} (h : IsUnif v ϖ) : ϖ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, h]
  exact le_of_lt (by decide)

end Oev

section HermO

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

def HO (a : ℕ) : AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ i j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v}
  add_mem' := fun {_ _} hx hy i j => oev_add v (hx i j) (hy i j)
  zero_mem' := fun _ _ => oev_zero v
  neg_mem' := fun {_} hx i j => oev_neg v (hx i j)

theorem mem_HO {a : ℕ} (S : HermR (Fv F v) σ a) :
    S ∈ HO σ v a ↔ ∀ i j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v :=
  Iff.rfl

theorem smul_mem_HO {a : ℕ} {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {S : HermR (Fv F v) σ a} (hS : S ∈ HO σ v a) : s • S ∈ HO σ v a := by
  rw [mem_HO] at hS ⊢
  intro i j
  rw [coe_hermSMul, Matrix.smul_apply]
  exact oev_smul v hs (hS i j)

theorem hermitianDivisible_eq_smul {a : ℕ} {ϖ : Fv F v} (hϖ : ϖ ≠ 0) :
    HermP v σ a ϖ = (smulSub ϖ (HO σ v a) : Set (HermR (Fv F v) σ a)) := by
  ext S
  rw [SetLike.mem_coe, mem_smulSub]
  simp only [HermP, PO, Set.mem_ofPred_eq]
  constructor
  · intro hS
    refine ⟨ϖ⁻¹ • S, ?_, ?_⟩
    · rw [mem_HO]
      intro i j
      obtain ⟨c, hc, he⟩ := hS i j
      rw [coe_hermSMul, Matrix.smul_apply, he, sdc_sc_mul, smul_smul, inv_mul_cancel₀ hϖ, one_smul]
      exact hc
    · rw [smul_smul, mul_inv_cancel₀ hϖ, one_smul]
  · rintro ⟨p, hp, rfl⟩ i j
    refine ⟨(p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, hp i j, ?_⟩
    rw [coe_hermSMul, Matrix.smul_apply, sdc_sc_mul]

theorem pairHerm_smul_left {a : ℕ} (s : Fv F v) (S T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a (s • S) T = s * pairHerm (Fv F v) σ a S T := by
  simp only [pairHerm, coe_hermSMul, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul,
    smul_eq_mul]
  ring

theorem pairHerm_zero_right {a : ℕ} (S : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a S 0 = 0 := by
  simp [pairHerm]

end HermO

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def TopH (a : ℕ) : Prop :=
  IsCompact (HO σ v a : Set (HermR (Fv F v) σ a)) ∧ IsOpen (HO σ v a : Set (HermR (Fv F v) σ a))

def DualH (a : ℕ) : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v →
    {T : HermR (Fv F v) σ a | ∀ S ∈ HO σ v a,
      dV v * pairHerm (Fv F v) σ a S T ∈ v.adicCompletionIntegers F} =
      (smulSub (dV v)⁻¹ (HO σ v a) : Set (HermR (Fv F v) σ a))

def IdxHO (a : ℕ) : Prop :=
  UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ((HO σ v a).relIndex (smulSub (dV v)⁻¹ (HO σ v a)) : ℝ) = absV v (dV v) ^ (-((a : ℝ) ^ 2)) ∧
    ((smulSub ϖ (HO σ v a)).relIndex (HO σ v a) : ℝ) = qv v ^ (a ^ 2)

theorem sdVolH_of_top (a : ℕ) (hC : CondV σ J ψ v) (hT : TopH σ v a) (hD : DualH σ J ψ v a)
    (hI : IdxHO σ v a) : SdVolH σ J ψ v a := by
  intro hS hU hν ϖ hϖ
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hϖ0 := unif_ne_zero v hϖ
  have hd0 := dV_ne_zero v
  have hνsd : SdHerm F E σ (Fv F v) (psiV F ψ v) a (dT σ ψ v a) := by
    simp only [dT, dif_pos hν]
    exact hν.choose_spec
  have := hνsd.1
  set ν := dT σ ψ v a with hνdef
  set L := HO σ v a with hLdef
  set L' := smulSub (dV v)⁻¹ L with hL'def
  obtain ⟨hLc, hLo⟩ := hT
  have hL'c : IsCompact (L' : Set (HermR (Fv F v) σ a)) := isCompact_smulSub _ L hLc
  have hL'o : IsOpen (L' : Set (HermR (Fv F v) σ a)) := isOpen_smulSub _ (inv_ne_zero hd0) L hLo
  have hχ : ∀ x t y : HermR (Fv F v) σ a, psiV F ψ v (pairHerm (Fv F v) σ a (t + x) y) =
      psiV F ψ v (pairHerm (Fv F v) σ a t y) * psiV F ψ v (pairHerm (Fv F v) σ a x y) := by
    intro x t y
    rw [pairHerm_add, psiV_add]
  have h0 : ∀ y : HermR (Fv F v) σ a, psiV F ψ v (pairHerm (Fv F v) σ a y 0) = 1 := by
    intro y
    rw [pairHerm_zero_right, psiV_zero]
  have hA : ann (fun S T => psiV F ψ v (pairHerm (Fv F v) σ a S T)) (L : Set (HermR (Fv F v) σ a)) =
      L' := by
    rw [Sd.ann_eq_cond v (psiV F ψ v) (dV v) (pairHerm (Fv F v) σ a) _ (hC hS)]
    · exact hD hS hU
    · intro s hs x hx
      exact ⟨s • x, smul_mem_HO σ v hs hx, fun y => pairHerm_smul_left σ v s x y⟩
  have hle : L ≤ L' := by
    intro S hS'
    rw [hL'def, mem_smulSub]
    refine ⟨dV v • S, smul_mem_HO σ v (dV_int v) hS', ?_⟩
    rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
  obtain ⟨hN1, hN2⟩ := hI hU ϖ hϖ
  have hNz : L.relIndex L' ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hN1
    have := Real.rpow_pos_of_pos (absV_dV_pos v) (-((a : ℝ) ^ 2))
    linarith
  have key := Sd.vol_sq_mul_index hνsd hχ h0 L L' hLc hLo hL'c hL'o hA hle hNz
  rw [hN1] at key
  have hp := absV_dV_pos v
  have hvolL : ν.real (L : Set (HermR (Fv F v) σ a)) = absV v (dV v) ^ ((a : ℝ) ^ 2 / 2) := by
    have e1 : absV v (dV v) ^ (-((a : ℝ) ^ 2)) = (absV v (dV v) ^ ((a : ℝ) ^ 2))⁻¹ :=
      Real.rpow_neg hp.le _
    have e2 : (absV v (dV v) ^ ((a : ℝ) ^ 2 / 2)) ^ 2 = absV v (dV v) ^ ((a : ℝ) ^ 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
      norm_num
    have hA2 : 0 < absV v (dV v) ^ ((a : ℝ) ^ 2) := Real.rpow_pos_of_pos hp _
    rw [e1] at key
    have e3 : ν.real (L : Set (HermR (Fv F v) σ a)) ^ 2 = (absV v (dV v) ^ ((a : ℝ) ^ 2 / 2)) ^ 2 := by
      rw [e2]
      field_simp at key
      linarith
    exact (pow_left_inj₀ measureReal_nonneg (Real.rpow_pos_of_pos hp _).le two_ne_zero).1 e3
  have hle2 : smulSub ϖ L ≤ L := by
    intro S hS'
    rw [mem_smulSub] at hS'
    obtain ⟨p, hp', rfl⟩ := hS'
    exact smul_mem_HO σ v (unif_int v hϖ) hp'
  have hPo : IsOpen (smulSub ϖ L : Set (HermR (Fv F v) σ a)) := isOpen_smulSub _ hϖ0 L hLo
  have hPc : IsCompact (smulSub ϖ L : Set (HermR (Fv F v) σ a)) := isCompact_smulSub _ L hLc
  have hNz2 : (smulSub ϖ L).relIndex L ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hN2
    have := pow_pos (qv_pos v) (a ^ 2)
    linarith
  have h2 := PI.VolStabSW.measure_eq_relIndex_mul ν (smulSub ϖ L) L hle2 hLo.measurableSet
    hPo.measurableSet hNz2
  have h3 : ν.real (L : Set (HermR (Fv F v) σ a)) =
      ((smulSub ϖ L).relIndex L : ℝ) * ν.real (smulSub ϖ L : Set (HermR (Fv F v) σ a)) := by
    rw [measureReal_def, measureReal_def, h2, ENNReal.toReal_mul]
    simp
  rw [hN2, hvolL] at h3
  rw [hermitianDivisible_eq_smul σ v hϖ0, ← ENNReal.ofReal_toReal hPc.measure_lt_top.ne, ← measureReal_def]
  congr 1
  have hq := pow_pos (qv_pos v) (a ^ 2)
  have e4 : qv v ^ (-((a : ℤ) ^ 2)) = (qv v ^ (a ^ 2))⁻¹ := by
    rw [zpow_neg]
    congr 1
  rw [e4, h3]
  field_simp

end Steps

end PI.OmLocU
