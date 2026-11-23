import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

open scoped RestrictedProduct

namespace GlobalTheory.InvIdem

variable {F : Type} [Field F] [NumberField F]

def ci (w : InfinitePlace F) : AF F →+* w.Completion :=
  (Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp (fstA F).toRingHom

def cf (v : HeightOneSpectrum (𝓞 F)) : AF F →+* Fv F v :=
  (evalV F v).toRingHom.comp (sndA F).toRingHom

theorem continuous_ci (w : InfinitePlace F) : Continuous (ci (F := F) w) :=
  (continuous_apply w).comp continuous_fst

theorem continuous_cf (v : HeightOneSpectrum (𝓞 F)) : Continuous (cf (F := F) v) :=
  (RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v).comp
    continuous_snd

theorem ext_c {a b : AF F} (h1 : ∀ w, ci w a = ci w b) (h2 : ∀ v, cf v a = cf v b) : a = b :=
  Prod.ext (funext h1) (RestrictedProduct.ext _ _ h2)

open Classical in

def sglI (w : InfinitePlace F) (c : w.Completion) : AF F :=
  ((Pi.single w c : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

def sglF (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) : AF F :=
  ((0 : InfiniteAdeleRing F), singleV F v c)

theorem ci_apply (w : InfinitePlace F) (a : AF F) : ci w a = a.1 w := rfl
theorem cf_apply (v : HeightOneSpectrum (𝓞 F)) (a : AF F) : cf v a = a.2 v := rfl

theorem ci_sglI_self (w : InfinitePlace F) (c : w.Completion) : ci w (sglI w c) = c := by
  classical
  rw [ci_apply]; simp [sglI]

theorem ci_sglI_ne {w u : InfinitePlace F} (h : u ≠ w) (c : w.Completion) : ci u (sglI w c) = 0 := by
  classical
  rw [ci_apply]; simp [sglI, Pi.single_apply, h]

theorem cf_sglI (w : InfinitePlace F) (c : w.Completion) (v : HeightOneSpectrum (𝓞 F)) :
    cf v (sglI w c) = 0 := by
  rw [cf_apply]; rfl

theorem ci_sglF (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) (w : InfinitePlace F) :
    ci w (sglF v c) = 0 := by
  rw [ci_apply]; rfl

theorem cf_sglF_self (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) : cf v (sglF v c) = c := by
  classical
  show (singleV F v c) v = c
  unfold singleV
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v c

theorem cf_sglF_ne {v u : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (c : Fv F v) : cf u (sglF v c) = 0 := by
  classical
  show (singleV F v c) u = 0
  unfold singleV
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) c h

open Classical in
theorem continuous_sglI (w : InfinitePlace F) : Continuous (sglI (F := F) w) := by
  unfold sglI
  exact (continuous_single w).prodMk continuous_const

open Classical in
theorem continuous_sglF (v : HeightOneSpectrum (𝓞 F)) : Continuous (sglF (F := F) v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion hS).comp hf)

def invS (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (y : AF F) : AF F :=
  (∑ w ∈ S₁, sglI w (ci w y)⁻¹) + ∑ v ∈ S₂, sglF v (cf v y)⁻¹

variable {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))}

open Classical in
theorem ci_invS (y : AF F) (u : InfinitePlace F) :
    ci u (invS S₁ S₂ y) = if u ∈ S₁ then (ci u y)⁻¹ else 0 := by
  rw [invS, map_add, map_sum, map_sum]
  simp only [ci_sglF, Finset.sum_const_zero, add_zero]
  split_ifs with hu
  · rw [Finset.sum_eq_single_of_mem u hu (fun w _ hw => ci_sglI_ne (Ne.symm hw) _), ci_sglI_self]
  · exact Finset.sum_eq_zero fun w hw => ci_sglI_ne (fun h : u = w => hu (h ▸ hw)) _

open Classical in
theorem cf_invS (y : AF F) (u : HeightOneSpectrum (𝓞 F)) :
    cf u (invS S₁ S₂ y) = if u ∈ S₂ then (cf u y)⁻¹ else 0 := by
  rw [invS, map_add, map_sum, map_sum]
  simp only [cf_sglI, Finset.sum_const_zero, zero_add]
  split_ifs with hu
  · rw [Finset.sum_eq_single_of_mem u hu (fun w _ hw => cf_sglF_ne (Ne.symm hw) _), cf_sglF_self]
  · exact Finset.sum_eq_zero fun w hw => cf_sglF_ne (fun h : u = w => hu (h ▸ hw)) _

theorem invS_mul {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε) {y z : AF F} (hyz : y * z = 1) :
    invS S₁ S₂ (ε * y) = ε * z := by
  obtain ⟨h1, h2, h3, h4⟩ := hε
  have hi : ∀ w, ci w y * ci w z = 1 := fun w => by rw [← map_mul (ci w), hyz, map_one]
  have hf : ∀ v, cf v y * cf v z = 1 := fun v => by rw [← map_mul (cf v), hyz, map_one]
  refine ext_c (fun w => ?_) (fun v => ?_)
  · rw [ci_invS, map_mul, map_mul]
    have e1 : ci w ε = fstA F ε w := rfl
    split_ifs with hw
    · rw [e1, h1 w hw, one_mul, one_mul]; exact inv_eq_of_mul_eq_one_right (hi w)
    · rw [e1, h2 w hw, zero_mul]
  · rw [cf_invS, map_mul, map_mul]
    have e1 : cf v ε = evalV F v (sndA F ε) := rfl
    split_ifs with hv
    · rw [e1, h3 v hv, one_mul, one_mul]; exact inv_eq_of_mul_eq_one_right (hf v)
    · rw [e1, h4 v hv, zero_mul]

theorem continuousAt_invS {y : AF F} (h1 : ∀ w ∈ S₁, ci w y ≠ 0) (h2 : ∀ v ∈ S₂, cf v y ≠ 0) :
    ContinuousAt (invS S₁ S₂) y := by
  unfold invS
  refine ContinuousAt.add ?_ ?_
  · exact tendsto_finset_sum S₁ fun w hw =>
      ((continuous_sglI w).continuousAt.comp ((continuousAt_inv₀ (h1 w hw)).comp (continuous_ci w).continuousAt))
  · exact tendsto_finset_sum S₂ fun v hv =>
      ((continuous_sglF v).continuousAt.comp ((continuousAt_inv₀ (h2 v hv)).comp (continuous_cf v).continuousAt))

end GlobalTheory.InvIdem

namespace GlobalTheory.InvIdem

theorem inv_cont : ∀ (F : Type) [Field F] [NumberField F] (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ∀ x : (AF F)ˣ, ∀ U : Set (AF F),
    U ∈ 𝓝 (ε * ((x⁻¹ : (AF F)ˣ) : AF F)) → ∃ V : Set (AF F), V ∈ 𝓝 (ε * (x : AF F)) ∧
      ∀ t : F, ε * algebraMap F (AF F) t ∈ V → (ε ≠ 0 → t ≠ 0) ∧ ε * algebraMap F (AF F) t⁻¹ ∈ U := by
  intro F _ _ S₁ S₂ ε hε x U hU
  have hx : invS S₁ S₂ (ε * (x : AF F)) = ε * ((x⁻¹ : (AF F)ˣ) : AF F) := invS_mul hε x.mul_inv
  have hci : ∀ w ∈ S₁, ci w (ε * (x : AF F)) ≠ 0 := by
    intro w hw h
    rw [map_mul, show ci w ε = fstA F ε w from rfl, hε.1 w hw, one_mul] at h
    have e := congrArg (ci w) x.mul_inv
    rw [map_mul, h, zero_mul, map_one] at e
    exact zero_ne_one e
  have hcf : ∀ v ∈ S₂, cf v (ε * (x : AF F)) ≠ 0 := by
    intro v hv h
    rw [map_mul, show cf v ε = evalV F v (sndA F ε) from rfl, hε.2.2.1 v hv, one_mul] at h
    have e := congrArg (cf v) x.mul_inv
    rw [map_mul, h, zero_mul, map_one] at e
    exact zero_ne_one e
  have hV1 : invS S₁ S₂ ⁻¹' U ∈ 𝓝 (ε * (x : AF F)) :=
    (continuousAt_invS hci hcf).preimage_mem_nhds (by rw [hx]; exact hU)
  have hV2 : {y : AF F | (∀ w ∈ S₁, ci w y ≠ 0) ∧ ∀ v ∈ S₂, cf v y ≠ 0} ∈ 𝓝 (ε * (x : AF F)) :=
    ((Filter.eventually_all_finset S₁).2 fun w hw => (continuous_ci w).continuousAt.eventually_ne (hci w hw)).and
      ((Filter.eventually_all_finset S₂).2 fun v hv => (continuous_cf v).continuousAt.eventually_ne (hcf v hv))
  refine ⟨_, Filter.inter_mem hV1 hV2, fun t ht => ?_⟩
  have htne : ε ≠ 0 → t ≠ 0 := by
    intro hε0 ht0
    subst ht0
    apply hε0
    have hB := ht.2
    simp only [Set.mem_setOf_eq, map_zero, mul_zero] at hB
    refine ext_c (fun w => ?_) (fun v => ?_)
    · rw [map_zero]
      exact hε.2.1 w fun hw => hB.1 w hw rfl
    · rw [map_zero]
      exact hε.2.2.2 v fun hv => hB.2 v hv rfl
  refine ⟨htne, ?_⟩
  by_cases hε0 : ε = 0
  · subst hε0
    have e := mem_of_mem_nhds hU
    rw [zero_mul] at e
    rwa [zero_mul]
  · have ht0 := htne hε0
    have e := invS_mul (y := algebraMap F (AF F) t) (z := algebraMap F (AF F) t⁻¹) hε
      (by rw [← map_mul, mul_inv_cancel₀ ht0, map_one])
    rw [← e]
    exact ht.1

end GlobalTheory.InvIdem
