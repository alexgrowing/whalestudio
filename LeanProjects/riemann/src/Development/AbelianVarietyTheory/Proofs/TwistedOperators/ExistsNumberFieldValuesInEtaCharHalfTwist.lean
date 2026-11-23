import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharHost
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
open NumberField IsDedekindDomain Formalism.L2.Host

noncomputable section

namespace GlobalTheory.EtaValsNumberField

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def embSum : R.Psi ⊕ R.Psi → (H.E →+* ℂ) :=
  Sum.elim (embPsi H) fun g => (starRingEnd ℂ).comp (embPsi H g)

theorem embSum_injective : Function.Injective (embSum H) := by
  rintro (i | i) (j | j) hij
  · exact congrArg _ (GlobalTheory.HalfIntChars.embPsi_inj H hij)
  · exact absurd hij (GlobalTheory.HalfIntChars.embPsi_ne_conj H i j)
  · exact absurd hij.symm (GlobalTheory.HalfIntChars.embPsi_ne_conj H j i)
  · refine congrArg _ (GlobalTheory.HalfIntChars.embPsi_inj H (RingHom.ext fun x => ?_))
    have := congrArg (fun f : H.E →+* ℂ => starRingEnd ℂ (f x)) hij
    simpa [embSum] using this

theorem card_sum : Fintype.card (R.Psi ⊕ R.Psi) = Fintype.card (H.E →+* ℂ) := by
  rw [Fintype.card_sum, NumberField.Embeddings.card, H.finrank_cmField,
    ← Nat.card_eq_fintype_card, Formalism.HC.Frame.natCard_Psi]
  ring

def embEquiv : R.Psi ⊕ R.Psi ≃ (H.E →+* ℂ) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr ⟨embSum_injective H, card_sum H⟩)

theorem algType_eta : ∃ m : (H.E →+* ℂ) → ℤ, ∀ k : H.Eˣ,
    (∏ g, (embPsi H g (k : H.E) / ((‖embPsi H g (k : H.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)) *
      ∏ φ : H.E →+* ℂ, ((‖φ (k : H.E)‖ : ℝ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = ∏ φ : H.E →+* ℂ, φ (k : H.E) ^ m φ := by
  set bij := embEquiv H
  let g : R.Psi ⊕ R.Psi → ℤ := fun x => Sum.elim (fun _ => 1) (fun _ => 0) x
  refine ⟨fun ψ => g (bij.symm ψ), fun k => ?_⟩
  have hR : ∏ ψ : H.E →+* ℂ, ψ (k : H.E) ^ g (bij.symm ψ) = ∏ x : R.Psi ⊕ R.Psi, (bij x) (k : H.E) ^ g x :=
    (Fintype.prod_equiv bij _ _ fun x => by rw [Equiv.symm_apply_apply]).symm
  have hL : ∏ ψ : H.E →+* ℂ, ((‖ψ (k : H.E)‖ : ℝ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) =
      ∏ x : R.Psi ⊕ R.Psi, ((‖bij x (k : H.E)‖ : ℝ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) :=
    (Fintype.prod_equiv bij _ _ fun x => rfl).symm
  rw [hR, hL, Fintype.prod_sum_type, Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  set z := embPsi H τ (k : H.E) with hzdef
  have hz : z ≠ 0 := (map_ne_zero _).2 k.ne_zero
  have hn : (((‖z‖ : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  show (z / ((‖z‖ : ℝ) : ℂ)) ^ (1 : ℤ) * ((((‖z‖ : ℝ) : ℂ)) ^ (((1 / 2 : ℝ)) : ℂ) *
    (((‖starRingEnd ℂ z‖ : ℝ) : ℂ)) ^ (((1 / 2 : ℝ)) : ℂ)) = z ^ (1 : ℤ) * (starRingEnd ℂ z) ^ (0 : ℤ)
  rw [Complex.norm_conj, ← Complex.cpow_add _ _ hn]
  norm_num
  rw [div_mul_cancel₀ _ hn]

theorem etaVals : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsEtaT H χ →
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn (1 / 2) (algebraMap M ℂ) := by
  intro R H χ hχ
  obtain ⟨m, hm⟩ := algType_eta H
  obtain ⟨C, hC, hv⟩ := PI.AlgValsFin.W.algValsFin_main H.E χ (1 / 2) m (fun k => by rw [hχ.inf k]; exact hm k)
  let M : IntermediateField ℚ ℂ := C.toIntermediateField fun x => by simp
  let e : C ≃+ M :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hM : FiniteDimensional ℚ M := LinearEquiv.finiteDimensional
    { e.toAddMonoidHom.toRatLinearMap with
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv }
  refine ⟨M, hM, fun v hv' => ?_⟩
  obtain ⟨y, hy⟩ := hv v hv'
  exact ⟨e y, hy⟩

end GlobalTheory.EtaValsNumberField
