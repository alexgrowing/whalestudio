import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LSBase
import Formalism.PeriodIntegrals.UnitaryApproxFin

open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct RestrictedProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Ad

open Classical

variable {F : Type} [Field F] [NumberField F]

theorem af_ext {a b : Af F} (h : ∀ w, a w = b w) : a = b := Subtype.ext (funext h)

theorem af_mul_apply (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) : (a * b) w = a w * b w := rfl
theorem af_add_apply (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) : (a + b) w = a w + b w := rfl
theorem af_sub_apply (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) : (a - b) w = a w - b w := rfl
theorem af_one_apply (w : HeightOneSpectrum (𝓞 F)) : (1 : Af F) w = 1 := rfl
theorem af_zero_apply (w : HeightOneSpectrum (𝓞 F)) : (0 : Af F) w = 0 := rfl
theorem af_alg_apply (c : F) (w : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (Af F) c) w = algebraMap F (w.adicCompletion F) c := rfl

theorem mem_intAf_iff (a : Af F) : a ∈ intAf F ↔ ∀ w, a w ∈ w.adicCompletionIntegers F := Iff.rfl

variable (v : HeightOneSpectrum (𝓞 F))

def sgl (x : Fv F v) : Af F :=
  RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x

theorem sgl_apply (x : Fv F v) (w : HeightOneSpectrum (𝓞 F)) : sgl v x w = Pi.single v x w := rfl

theorem sgl_mul (x y : Fv F v) : sgl v (x * y) = sgl v x * sgl v y := af_ext fun w => by
  rw [af_mul_apply, sgl_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, mul_zero]

theorem sgl_add (x y : Fv F v) : sgl v (x + y) = sgl v x + sgl v y := af_ext fun w => by
  rw [af_add_apply, sgl_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, add_zero]

theorem sgl_smul (c : F) (x : Fv F v) : c • sgl v x = sgl v (c • x) := af_ext fun w => by
  rw [Algebra.smul_def, Algebra.smul_def, af_mul_apply, af_alg_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, mul_zero]

theorem sgl_int {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) : sgl v x ∈ intAf F := by
  intro w
  show sgl v x w ∈ w.adicCompletionIntegers F
  rw [sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same]; exact hx
  · rw [Pi.single_eq_of_ne hw]; exact zero_mem _

theorem sgl_one_mul (a : Af F) : sgl v 1 * a = sgl v (a v) := af_ext fun w => by
  rw [af_mul_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, zero_mul]

def ivL : Fv F v →ₗ[F] Af F where
  toFun := sgl v
  map_add' := sgl_add v
  map_smul' c x := (sgl_smul v c x).symm

def evT (T : Set (HeightOneSpectrum (𝓞 F))) : Af F :=
  (⟨fun w => if w ∈ T then (1 : w.adicCompletion F) else 0,
    Filter.Eventually.of_forall fun w => by
      show (if w ∈ T then (1 : w.adicCompletion F) else 0) ∈ w.adicCompletionIntegers F
      split_ifs
      · exact one_mem _
      · exact zero_mem _⟩ :
    Πʳ w : HeightOneSpectrum (𝓞 F), [w.adicCompletion F, w.adicCompletionIntegers F])

theorem evT_apply (T : Set (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)) :
    evT T w = if w ∈ T then 1 else 0 := rfl

theorem evT_int (T : Set (HeightOneSpectrum (𝓞 F))) : evT T ∈ intAf F := by
  intro w
  show evT T w ∈ w.adicCompletionIntegers F
  rw [evT_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem one_sub_evT_int (T : Set (HeightOneSpectrum (𝓞 F))) : 1 - evT T ∈ intAf F := by
  intro w
  show (1 - evT T) w ∈ w.adicCompletionIntegers F
  rw [af_sub_apply, evT_apply, af_one_apply]; split_ifs
  · rw [sub_self]; exact zero_mem _
  · rw [sub_zero]; exact one_mem _

theorem evT_eq_sum (T : Finset (HeightOneSpectrum (𝓞 F))) : evT (T : Set _) = ∑ w ∈ T, sgl w 1 := by
  apply af_ext
  intro w
  rw [evT_apply, show (∑ w' ∈ T, sgl w' 1) w = evalV F w (∑ w' ∈ T, sgl w' 1) from rfl, map_sum]
  simp only [show ∀ w', evalV F w (sgl w' 1) = Pi.single w' 1 w from fun _ => rfl]
  by_cases hw : w ∈ T
  · rw [if_pos (by exact_mod_cast hw), Finset.sum_eq_single w]
    · simp
    · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
    · intro h; exact absurd hw h
  · rw [if_neg (by exact_mod_cast hw)]
    refine (Finset.sum_eq_zero fun b hb => ?_).symm
    have : w ≠ b := fun h => hw (h ▸ hb)
    simp [Pi.single_apply, this]

theorem one_sub_evT_inv_int (T : Set (HeightOneSpectrum (𝓞 F))) (t : 𝓞 F)
    (ht : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → t ∉ w.asIdeal) :
    (1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹) ∈ intAf F := by
  intro w
  show ((1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹)) w ∈ w.adicCompletionIntegers F
  rw [af_mul_apply, af_sub_apply, evT_apply, af_one_apply, af_alg_apply]
  split_ifs with hw
  · rw [sub_self, zero_mul]; exact zero_mem _
  · rw [sub_zero, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers]
    have e1 : algebraMap F (w.adicCompletion F) ((algebraMap (𝓞 F) F t)⁻¹) =
        (((algebraMap (𝓞 F) F t)⁻¹ : F) : w.adicCompletion F) := rfl
    rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
      HeightOneSpectrum.valuation_of_algebraMap,
      (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w t).2 (ht w hw), inv_one]

end Ad

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))

def Psi : Af F ⊗[F] E →ₐ[F] E ⊗[F] Fv F v :=
  (Algebra.TensorProduct.comm F (Fv F v) E).toAlgHom.comp
    (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E))

theorem Psi_tmul (a : Af F) (e : E) : Psi (E := E) v (a ⊗ₜ[F] e) = e ⊗ₜ[F] a v := by
  simp [Psi]; rfl

def Phi : E ⊗[F] Fv F v →ₗ[F] Af F ⊗[F] E :=
  (TensorProduct.map (ivL v) LinearMap.id) ∘ₗ (TensorProduct.comm F E (Fv F v)).toLinearMap

theorem Phi_tmul (e : E) (x : Fv F v) : Phi v (e ⊗ₜ[F] x) = sgl v x ⊗ₜ[F] e := by
  simp [Phi]; rfl

theorem Phi_Psi (r : Af F ⊗[F] E) : Phi v (Psi v r) = (sgl v 1 ⊗ₜ[F] (1 : E)) * r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Psi_tmul, Phi_tmul, Algebra.TensorProduct.tmul_mul_tmul, sgl_one_mul, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

theorem Phi_mul (x y : E ⊗[F] Fv F v) : Phi v (x * y) = Phi v x * Phi v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e' a' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Phi_tmul, Phi_tmul, Phi_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, sgl_mul]
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]

theorem Phi_inclE (e : E) : Phi v (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v) e) = sgl v 1 ⊗ₜ[F] e := by
  show Phi v (e ⊗ₜ[F] (1 : Fv F v)) = _
  rw [Phi_tmul]

theorem Phi_int {s : E ⊗[F] Fv F v}
    (hs : s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (Fv F v) (PI.UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers F).toSubring) :
    Phi v s ∈ Oh F E := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · obtain ⟨o, rfl⟩ := he
      rw [Phi_tmul]
      exact tmul_mem_Oh (sgl_int v (one_mem _)) o.isIntegral_coe
    · rw [Phi_tmul]
      exact tmul_mem_Oh (sgl_int v hy) isIntegral_one
  | zero => rw [map_zero]; exact zero_mem _
  | one =>
    rw [show (1 : E ⊗[F] Fv F v) = (1 : E) ⊗ₜ[F] (1 : Fv F v) from rfl, Phi_tmul]
    exact tmul_mem_Oh (sgl_int v (one_mem _)) isIntegral_one
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg x _ h1 => rw [map_neg]; exact neg_mem h1
  | mul x y _ _ h1 h2 => rw [Phi_mul]; exact Oh_mul h1 h2

end Tens

end PI.UnitaryGroupMassFormula.UJClassMass
