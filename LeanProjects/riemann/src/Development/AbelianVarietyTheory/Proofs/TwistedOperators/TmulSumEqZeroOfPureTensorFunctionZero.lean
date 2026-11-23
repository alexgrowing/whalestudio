import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumPureMemAlgD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenIntertwinerModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfProdFunEqStatement

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThK.PureTensIndep

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Filter GlobalTheory.ThK.ModelPol

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem sum_local_eq_zero (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ) (h0 : ∀ v, vac v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (T : Finset (Pl F)) {m : ℕ} (f : Fin m → SInf F κ) (φ : Fin m → ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hφ : ∀ i, ∀ v ∉ T, φ i v = vac v) (hs : ∑ i, pure (f i) (φ i) = 0)
    (x : κ → mixedEmbedding.mixedSpace F) (z : ∀ v : T, κ → Fv F v) :
    ∑ i, f i x * ∏ v : T, φ i v (z v) = 0 := by
  classical
  have key : ∀ v : Pl F, ∃ p : κ → Fv F v, vac v p ≠ 0 ∧
      (vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
        ∀ i, p i ∈ v.adicCompletionIntegers F) := by
    intro v
    obtain ⟨p, hp⟩ := Function.ne_iff.1 (h0 v)
    refine ⟨p, hp, fun h => ?_⟩
    rw [h] at hp
    exact Set.mem_of_indicator_ne_zero hp
  choose p hp hp' using key
  let w : ∀ v : Pl F, κ → Fv F v := fun v => if h : v ∈ T then z ⟨v, h⟩ else p v
  have hw : ∀ i, ∀ᶠ v in cofinite, w v i ∈ v.adicCompletionIntegers F := by
    intro i
    filter_upwards [hstd, T.finite_toSet.compl_mem_cofinite] with v hv hvT
    have hvT' : v ∉ T := hvT
    simp only [w, dif_neg hvT']
    exact hp' v hv i
  let y : κ → Af F := fun i => ⟨fun v => w v i, hw i⟩
  have hy : ∀ v, (fun i => evalV F v (y i)) = w v := fun _ => rfl
  have hS : {v | vac v ≠ Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite :=
    Filter.eventually_cofinite.1 hstd
  have hCfin : (Function.mulSupport fun v => if v ∈ T then (1 : ℂ) else vac v (p v)).Finite := by
    refine hS.subset fun v hv => ?_
    by_cases hvT : v ∈ T
    · simp [hvT] at hv
    · intro he
      apply hv
      simp only [if_neg hvT]
      rw [he, Set.indicator_of_mem (show p v ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from hp' v he)]
      rfl
  have hC : (∏ᶠ v, if v ∈ T then (1 : ℂ) else vac v (p v)) ≠ 0 :=
    finprod_induction (fun c : ℂ => c ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb) fun v => by
      by_cases hvT : v ∈ T
      · simp [hvT]
      · simp only [if_neg hvT]; exact hp v
  have hval : ∀ i, finPr (φ i) y = (∏ v : T, φ i v (z v)) * ∏ᶠ v, if v ∈ T then (1 : ℂ) else vac v (p v) := by
    intro i
    have e1 : (fun v => φ i v fun j => evalV F v (y j)) =
        fun v => (if v ∈ T then φ i v (w v) else 1) * (if v ∈ T then (1 : ℂ) else vac v (p v)) := by
      funext v
      rw [hy v]
      by_cases hvT : v ∈ T
      · simp [hvT]
      · simp [hvT, hφ i v hvT, w]
    have hAfin : (Function.mulSupport fun v => if v ∈ T then φ i v (w v) else 1).Finite := by
      refine T.finite_toSet.subset fun v hv => ?_
      by_contra h
      exact hv (if_neg h)
    show (∏ᶠ v, φ i v fun j => evalV F v (y j)) = _
    rw [e1, finprod_mul_distrib hAfin hCfin]
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset (s := T) _ (fun v hv => by
      by_contra h
      exact hv (if_neg h))]
    rw [← Finset.prod_coe_sort T]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp [v.2, w]
  have h1 := congrFun hs (pt x y)
  simp only [Finset.sum_apply, Pi.zero_apply, pure_eq, pureA_pt, hval] at h1
  have h2 : (∑ i, f i x * ∏ v : T, φ i v (z v)) * ∏ᶠ v, (if v ∈ T then (1 : ℂ) else vac v (p v)) = 0 := by
    rw [Finset.sum_mul]
    simpa [mul_assoc] using h1
  exact (mul_eq_zero.1 h2).resolve_right hC

section Forms

variable (F κ) in

def coeL : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) where
  toFun f := f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

variable (F κ) in
theorem coeL_injective : Function.Injective (coeL F κ) := fun _ _ h => SchwartzMap.ext (congrFun h)

variable (F κ) in

def Xf (T : Finset (Pl F)) : Option T → Type
  | none => κ → mixedEmbedding.mixedSpace F
  | some v => κ → Fv F v

variable (F κ) in

def Vf (T : Finset (Pl F)) : ∀ l : Option T, Submodule ℂ (Xf F κ T l → ℂ)
  | none => LinearMap.range (coeL F κ)
  | some _ => ⊤

def famOf (T : Finset (Pl F)) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : ∀ l, Vf F κ T l
  | none => ⟨coeL F κ f, LinearMap.mem_range_self _ _⟩
  | some v => ⟨φ v, Submodule.mem_top⟩

def back (T : Finset (Pl F)) : Vf F κ T none ≃ₗ[ℂ] SInf F κ :=
  (LinearEquiv.ofInjective _ (coeL_injective F κ)).symm

theorem back_famOf (T : Finset (Pl F)) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    back T (famOf T f φ none) = f :=
  (LinearEquiv.symm_apply_eq _).2 (Subtype.ext rfl)

theorem q_add {T : Finset (Pl F)} {v : T} {Q : Type} [AddCommGroup Q] [Module ℂ Q]
    (q : ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q) (a b : Vf F κ T (some v)) :
    q ((a + b : Vf F κ T (some v)) : Xf F κ T (some v) → ℂ) =
      q (a : Xf F κ T (some v) → ℂ) + q (b : Xf F κ T (some v) → ℂ) :=
  q.map_add (a : Xf F κ T (some v) → ℂ) (b : Xf F κ T (some v) → ℂ)

theorem q_smul {T : Finset (Pl F)} {v : T} {Q : Type} [AddCommGroup Q] [Module ℂ Q]
    (q : ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q) (c : ℂ) (b : Vf F κ T (some v)) :
    q ((c • b : Vf F κ T (some v)) : Xf F κ T (some v) → ℂ) = c • q (b : Xf F κ T (some v) → ℂ) :=
  q.map_smul c (b : Xf F κ T (some v) → ℂ)

theorem upd_some {T : Finset (Pl F)} [DecidableEq (Option T)] {Q : Pl F → Type} [∀ v, AddCommGroup (Q v)]
    [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q v) (w : ∀ l, Vf F κ T l) (v₀ : T)
    (c : Vf F κ T (some v₀)) :
    (fun v : T => q v ((Function.update w (some v₀) c (some v) : Vf F κ T (some v)) : Xf F κ T (some v) → ℂ)) =
      Function.update (fun v : T => q v (w (some v) : Xf F κ T (some v) → ℂ))
        v₀ (q v₀ (c : Xf F κ T (some v₀) → ℂ)) := by
  funext v
  by_cases h : v = v₀
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne (fun e => h (Option.some_injective _ e))]

theorem upd_none {T : Finset (Pl F)} [DecidableEq (Option T)] {Q : Pl F → Type} [∀ v, AddCommGroup (Q v)]
    [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q v) (w : ∀ l, Vf F κ T l) (c : Vf F κ T none) :
    (fun v : T => q v ((Function.update w none c (some v) : Vf F κ T (some v)) : Xf F κ T (some v) → ℂ)) =
      fun v : T => q v (w (some v) : Xf F κ T (some v) → ℂ) := by
  funext v
  rw [Function.update_of_ne (Option.some_ne_none v)]

def formOf {T : Finset (Pl F)} {P : Type} [AddCommGroup P] [Module ℂ P] (p : SInf F κ →ₗ[ℂ] P) {Q : Pl F → Type}
    [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q v)
    (ℓ : Module.Dual ℂ (P ⊗[ℂ] PiTensorProduct ℂ fun v : T => Q v)) :
    MultilinearMap ℂ (fun l => Vf F κ T l) ℂ where
  toFun w := ℓ (p (back T (w none)) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (w (some v) : Xf F κ T (some v) → ℂ))
  map_update_add' := by
    intro _ w l a b
    cases l with
    | none =>
      simp only [upd_none, Function.update_self, map_add, TensorProduct.add_tmul]
    | some v₀ =>
      simp only [upd_some, Function.update_of_ne (Option.some_ne_none v₀).symm, q_add,
        MultilinearMap.map_update_add, TensorProduct.tmul_add, map_add]
  map_update_smul' := by
    intro _ w l a b
    cases l with
    | none =>
      simp only [upd_none, Function.update_self, map_smul]
      rw [← TensorProduct.smul_tmul', map_smul, smul_eq_mul]
    | some v₀ =>
      simp only [upd_some, Function.update_of_ne (Option.some_ne_none v₀).symm, q_smul,
        MultilinearMap.map_update_smul, TensorProduct.tmul_smul, map_smul, smul_eq_mul]

theorem formOf_famOf {T : Finset (Pl F)} {P : Type} [AddCommGroup P] [Module ℂ P] (p : SInf F κ →ₗ[ℂ] P)
    {Q : Pl F → Type} [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q v)
    (ℓ : Module.Dual ℂ (P ⊗[ℂ] PiTensorProduct ℂ fun v : T => Q v)) (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    formOf p q ℓ (famOf T f φ) = ℓ (p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ v)) := by
  show ℓ (p (back T (famOf T f φ none)) ⊗ₜ[ℂ] _) = _
  rw [back_famOf]
  rfl

end Forms

theorem tmul_sum_eq_zero_of_pure : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
    (∀ v, vac v ≠ 0) → (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ {P : Type} [AddCommGroup P] [Module ℂ P] (p : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] P) (Q : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F → Type)
    [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ] Q v)
    (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
    (∀ i, ∀ v ∉ T, φ i v = vac v) → ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) = 0 →
    ∑ i, p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => q v (φ i v)) = 0 := by
  intro F _ _ κ _ vac h0 hstd P _ _ p Q _ _ q T m f φ hφ hs
  have hloc := sum_local_eq_zero vac h0 hstd T f φ hφ hs
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
  have key := GlobalTheory.T.multilinearMap_sum_eq_of_sum_prod_eval_eq (Vf F κ T) (formOf p q ℓ) (Finsupp.equivFunOnFinite.symm fun _ : Fin m => (1 : ℂ))
    (fun i => famOf T (f i) (φ i)) (fun _ => 0) (fun z => by
      rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
      simp only [Finsupp.coe_equivFunOnFinite_symm, one_mul, Fintype.prod_option]
      have h1 := hloc (z none) fun v => z (some v)
      simp only [Pi.zero_apply, ZeroMemClass.coe_zero, zero_mul, Finset.sum_const_zero]
      exact h1)
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Finsupp.sum_fintype _ _ (fun _ => zero_mul _)] at key
  simp only [Finsupp.coe_equivFunOnFinite_symm, one_mul, MultilinearMap.map_zero, Finset.sum_const_zero,
    formOf_famOf] at key
  rw [map_sum]
  exact key

end GlobalTheory.ThK.PureTensIndep
