import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EmbChart

open GlobalTheory.AdelicU

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))

def atPlace : Fv F v →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F)).comp (singleFin v)

theorem atPlace_apply (a : Fv F v) : atPlace v a = pairA F 0 (singleFin v a) := rfl

theorem atPlace_mul_right (a : Fv F v) (y : AF F) : atPlace v a * y = atPlace v (a * evFin F v y) := by
  refine Prod.ext (zero_mul _) ?_
  change singleFin v a * sndA F y = singleFin v (a * evalV F v (sndA F y))
  refine FiniteAdeleRing.ext _ fun u => ?_
  change evalV F u (singleFin v a * sndA F y) = evalV F u (singleFin v (a * evalV F v (sndA F y)))
  rw [map_mul]
  by_cases e : u = v
  · subst e; rw [evalV_singleFin_self, evalV_singleFin_self]
  · rw [evalV_singleFin_ne e, evalV_singleFin_ne e, zero_mul]

theorem evFin_atPlace (a : Fv F v) : evFin F v (atPlace v a) = a := evalV_singleFin_self v a

variable (E) in

def tensAt : Fv F v ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (atPlace v) LinearMap.id

theorem tensAt_tmul (a : Fv F v) (x : E) : tensAt E v (a ⊗ₜ[F] x) = atPlace v a ⊗ₜ[F] x := rfl

theorem compFin_tensAt (y : Fv F v ⊗[F] E) : compFin F E v (tensAt E v y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => exact congrArg (· ⊗ₜ[F] x) (evFin_atPlace v a)

theorem tensAt_eq_zero {y : Fv F v ⊗[F] E} : tensAt E v y = 0 ↔ y = 0 :=
  ⟨fun h => by rw [← compFin_tensAt v y, h, map_zero], fun h => by rw [h, map_zero]⟩

theorem tensAt_mul_right (y : Fv F v ⊗[F] E) (z : AF F ⊗[F] E) :
    tensAt E v y * z = tensAt E v (y * compFin F E v z) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_mul, hx, hy]
  | tmul a x =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
    | tmul b x' =>
      change _ = tensAt E v (a ⊗ₜ[F] x * evFin F v b ⊗ₜ[F] x')
      rw [tensAt_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, tensAt_tmul,
        atPlace_mul_right]

theorem sigR_tensAt (σ : E →ₐ[F] E) (y : Fv F v ⊗[F] E) :
    sigR (AF F) σ (tensAt E v y) = tensAt E v (sigR _ σ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

theorem map_evalV_map_sndA (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) =
      compFin F E v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

theorem map_evalV_mem {z : Af F ⊗[F] E}
    (hz : z ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) :
    Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) z ∈ intLoc F E v := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    exact tmul_mem_intLoc (hα v) o
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem map_sndA_tensAt_mem {y : Fv F v ⊗[F] E} (h : y ∈ intLoc F E v) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (tensAt E v y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  refine intLoc_induction (p := fun y => Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (tensAt E v y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)})
    (fun a ha x => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) h
  · refine AddSubgroup.subset_closure ⟨singleFin v a, fun u => ?_, x, rfl⟩
    by_cases e : u = v
    · subst e; rw [evalV_singleFin_self]; exact ha
    · rw [evalV_singleFin_ne e]; exact zero_mem _
  · rw [map_zero, map_zero]; exact zero_mem _
  · rw [map_add, map_add]; exact add_mem hy hz
  · rw [map_neg, map_neg]; exact neg_mem hy

end General

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem finPart_tensAt_mem_iff (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    finPart D (tensAt D.host.E v y) ∈ intAE D ↔ y ∈ intLoc D.host.F D.host.E v := by
  refine ⟨fun h => ?_, map_sndA_tensAt_mem v⟩
  have h3 := map_evalV_mem v h
  rwa [show finPart D (tensAt D.host.E v y) = _ from rfl, finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_evalV_map_sndA, compFin_tensAt] at h3

def idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : AE D := tensAt D.host.E v (splitIdem (isCMExt_host D) τ)

theorem idem_mul (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (a : AE D) :
    idem τ * a = tensAt D.host.E v (splitIdem (isCMExt_host D) τ * compFin D.host.F D.host.E v a) :=
  tensAt_mul_right v _ a

theorem compFin_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    compFin D.host.F D.host.E v (idem τ) = splitIdem (isCMExt_host D) τ := compFin_tensAt v _

theorem cA_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    cA D (idem τ) = tensAt D.host.E v (1 - splitIdem (isCMExt_host D) τ) :=
  (sigR_tensAt v _ _).trans (congrArg _ (sigR_splitIdem _ τ))

theorem isSplitIdem_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : IsSplitIdem D (idem τ) := by
  refine ⟨?_, ?_, v, atPlace v 1, ⟨singleFin v 1, rfl, evalV_singleFin_self v 1, fun u hu => evalV_singleFin_ne hu 1⟩,
    ?_⟩
  · rw [idem_mul, compFin_idem, splitIdem_mul_self]; rfl
  · rw [idem_mul, cA_idem, compFin_tensAt, mul_sub, mul_one, splitIdem_mul_self, sub_self, LinearMap.map_zero]
  · rw [cA_idem, idem, ← LinearMap.map_add, add_sub_cancel]; rfl

theorem finPart_idem_mul_mem_iff (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (a : AE D) :
    finPart D (idem τ * a) ∈ intAE D ↔
      splitProj τ (compFin D.host.F D.host.E v a) ∈ v.adicCompletionIntegers D.host.F := by
  rw [idem_mul, finPart_tensAt_mem_iff, mem_intLoc_iff_split (isCMExt_host D) τ, map_mul, map_mul,
    splitProj_splitIdem, splitProj_comp_splitIdem, one_mul, zero_mul]
  exact and_iff_left (zero_mem _)

theorem chart_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Chart (idem τ) v
    ((splitProj τ : Fv D.host.F v ⊗[D.host.F] D.host.E →+* Fv D.host.F v).comp (compFin D.host.F D.host.E v)) := by
  refine ⟨fun a => ⟨tensAt D.host.E v (a ⊗ₜ 1), ?_⟩, fun a => ?_, fun y => ?_, fun a => ?_⟩
  · change splitProj τ (compFin D.host.F D.host.E v (tensAt D.host.E v (a ⊗ₜ[D.host.F] 1))) = a
    rw [compFin_tensAt, splitProj_tmul, map_one, mul_one]
  · rw [idem_mul, tensAt_eq_zero]
    exact splitProj_eq_zero_iff _ τ _
  · change splitProj τ (evFin D.host.F v y ⊗ₜ 1) = _
    rw [splitProj_tmul, map_one, mul_one]; rfl
  · rw [finPart_idem_mul_mem_iff, isInt_Ov]; rfl

theorem isIdemAt_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : IsIdemAt (idem τ) (splitPrime τ) := by
  refine ⟨isSplitIdem_idem τ, fun x hx => ?_⟩
  have h0 : Valued.v (τ x) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero τ).2 (RingOfIntegers.coe_ne_zero_iff.2 hx))
  have h1 : splitProj τ (compFin D.host.F D.host.E v (incA D (x : D.host.E)⁻¹)) = τ (x : D.host.E)⁻¹ := by
    change splitProj τ (evFin D.host.F v 1 ⊗ₜ _) = _
    rw [splitProj_tmul, map_one, one_mul]; rfl
  rw [finPart_idem_mul_mem_iff, h1, mem_splitPrime, HeightOneSpectrum.mem_adicCompletionIntegers,
    map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 h0)]

theorem exists_isIdemAt_chart : ∀ {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), ∃ e : AE D, IsIdemAt e (GlobalTheory.AdelicU.splitPrime τ) ∧ Chart e v ((GlobalTheory.AdelicU.splitProj τ : Fv D.host.F v ⊗[D.host.F] D.host.E →+* Fv D.host.F v).comp (GlobalTheory.AdelicU.compFin D.host.F D.host.E v)) :=
  fun τ => ⟨idem τ, isIdemAt_idem τ, chart_idem τ⟩

end GlobalTheory.EmbChart

end
