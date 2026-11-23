import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.IdVMul

variable {D : D7}

theorem intAE_mul_mem' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D)
    (hy : y ∈ intAE D) : x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, w, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w' => ?_, u * w, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w') (hb w')
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

variable {v : Pl D}

theorem intAt_mul {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [(finPart D).map_mul]; exact intAE_mul_mem' ha.2 hb.2⟩

theorem intAt_zero : (0 : AE D) ∈ intAt D (· = v) :=
  ⟨zero_mem _, by rw [(finPart D).map_zero]; exact zero_mem _⟩

theorem intAt_add {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [(finPart D).map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {a : AE D} (ha : a ∈ intAt D (· = v)) : -a ∈ intAt D (· = v) :=
  ⟨neg_mem ha.1, by rw [(finPart D).map_neg]; exact neg_mem ha.2⟩

theorem pairA_zero_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  show ((0 : Ainf D.host.F) * 0, α * β) = ((0 : Ainf D.host.F), α * β)
  rw [zero_mul]

theorem evalV_single_self (v : Pl D) : evalV D.host.F v (singleV D.host.F v 1) = 1 := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v 1

theorem evalV_single_ne {v w : Pl D} (hw : w ≠ v) : evalV D.host.F w (singleV D.host.F v 1) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) 1 hw

theorem single_int (v : Pl D) : singleV D.host.F v 1 ∈ intAf D.host.F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [evalV_single_self]; exact one_mem _
  · rw [evalV_single_ne hw]; exact zero_mem _

theorem mul_single {α : Af D.host.F} (hα : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    α * singleV D.host.F v 1 = α := by
  apply RestrictedProduct.ext
  intro w
  change evalV D.host.F w (α * singleV D.host.F v 1) = evalV D.host.F w α
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [evalV_single_self, mul_one]
  · rw [hα w hw, zero_mul]

theorem gen_mem {𝔞 : FI D} {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0)
    {a : D.host.E} (ha : a ∈ 𝔞) : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] a ∈ idV 𝔞 v :=
  AddSubgroup.subset_closure ⟨α, hα, hαv, a, ha, rfl⟩

theorem tmul_mem_idAt {α : Af D.host.F} (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0) (x : D.host.E) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [hαv _ w.2, TensorProduct.zero_tmul]

theorem tmul_one_mem_intAt {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨tmul_mem_idAt hαv 1, ?_⟩
  change α ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D
  exact AddSubgroup.subset_closure ⟨α, hα, 1, by simp⟩

theorem tmul_mul_tmul' (α β : Af D.host.F) (a b : D.host.E) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] b) =
      (pairA D.host.F 0 (α * β)) ⊗ₜ[D.host.F] (a * b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_zero_mul]

theorem incA_mul_tmul (x : D.host.E) (α : AF D.host.F) (b : D.host.E) :
    incA D x * (α ⊗ₜ[D.host.F] b : AE D) = α ⊗ₜ[D.host.F] (x * b) := by
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) * (α ⊗ₜ[D.host.F] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem mul_mem_idV {𝔞 𝔟 : FI D} {a b : AE D} (ha : a ∈ idV 𝔞 v) (hb : b ∈ idV 𝔟 v) : a * b ∈ idV (𝔞 * 𝔟) v := by
  induction ha using AddSubgroup.closure_induction with
  | mem a' ha' =>
    obtain ⟨α, hα, hαv, a, ha, rfl⟩ := ha'
    induction hb using AddSubgroup.closure_induction with
    | mem b' hb' =>
      obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := hb'
      rw [tmul_mul_tmul']
      refine gen_mem (fun w => ?_) (fun w hw => ?_) (FractionalIdeal.mul_mem_mul ha hb)
      · rw [map_mul]; exact mul_mem (hα w) (hβ w)
      · rw [map_mul, hαv w hw, zero_mul]
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg x _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg x _ h => rw [neg_mul]; exact neg_mem h

theorem incA_mul_mem {𝔞 𝔟 : FI D} {x : D.host.E} (hx0 : x ≠ 0)
    (hx : ∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) {t : AE D} (ht : t ∈ idV 𝔟 v) :
    incA D x * t ∈ idV (𝔞 * 𝔟) v := by
  induction ht using AddSubgroup.closure_induction with
  | mem t' ht' =>
    obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := ht'
    have e : incA D x * ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] b) =
        ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] x : AE D) * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b) := by
      rw [incA_mul_tmul, tmul_mul_tmul', mul_single hβv]
    rw [e]
    refine mul_mem_idV ((hx _).2 ⟨?_, tmul_mem_idAt hβv x⟩)
      (gen_mem (single_int v) (fun w hw => evalV_single_ne hw) hb)
    rw [incA_mul_tmul, inv_mul_cancel₀ hx0]
    exact tmul_one_mem_intAt hβ hβv
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha

theorem idV_mul_gen : ∀ (D : D7) (v : Pl D) (𝔞 𝔟 : FI D) (x y : D.host.E), x ≠ 0 → y ≠ 0 → (∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) → (∀ s, s ∈ idV 𝔟 v ↔ incA D y⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) → ∀ s, s ∈ idV (𝔞 * 𝔟) v ↔ incA D (x * y)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  intro D v 𝔞 𝔟 x y hx0 hy0 hx hy
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  intro s
  constructor
  · intro hs
    refine AddSubgroup.closure_induction (p := fun s _ => incA D (x * y)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v))
      ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨α, hα, hαv, c, hc, rfl⟩
      refine FractionalIdeal.mul_induction_on (C := fun c => incA D (x * y)⁻¹ * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] c) ∈
        intAt D (· = v) ∧ (pairA D.host.F 0 α) ⊗ₜ[D.host.F] c ∈ idAt D (· = v)) hc ?_ ?_
      · intro a ha b hb
        have hA := (hx _).1 (gen_mem hα hαv ha)
        have hB := (hy _).1 (gen_mem (single_int v) (fun w hw => evalV_single_ne hw) hb)
        have e : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * b) =
            ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b) := by
          rw [tmul_mul_tmul', mul_single hαv]
        rw [e]
        refine ⟨?_, Ideal.mul_mem_right _ _ hA.2⟩
        have e2 : incA D (x * y)⁻¹ * (((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) *
            ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b)) =
            (incA D x⁻¹ * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a)) *
              (incA D y⁻¹ * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b)) := by
          rw [mul_inv, (incA D).map_mul]; ring
        rw [e2]
        exact intAt_mul hA.1 hB.1
      · intro c d hc hd
        rw [TensorProduct.tmul_add, mul_add]
        exact ⟨intAt_add hc.1 hd.1, add_mem hc.2 hd.2⟩
    · rw [mul_zero]; exact ⟨intAt_zero, zero_mem _⟩
    · intro a b _ _ ha hb
      rw [mul_add]; exact ⟨intAt_add ha.1 hb.1, add_mem ha.2 hb.2⟩
    · intro a _ ha
      rw [mul_neg]; exact ⟨intAt_neg ha.1, neg_mem ha.2⟩
  · rintro ⟨ho, hs⟩
    have hso : s = incA D x * (incA D y * (incA D (x * y)⁻¹ * s)) := by
      rw [← mul_assoc, ← mul_assoc, ← (incA D).map_mul, ← (incA D).map_mul, mul_inv_cancel₀ hxy0, (incA D).map_one,
        one_mul]
    have ht : incA D y * (incA D (x * y)⁻¹ * s) ∈ idV 𝔟 v := by
      refine (hy _).2 ⟨?_, Ideal.mul_mem_left _ _ ho.1⟩
      rw [← mul_assoc, ← (incA D).map_mul, inv_mul_cancel₀ hy0, (incA D).map_one, one_mul]
      exact ho
    rw [hso]
    exact incA_mul_mem hx0 hx ht

end GlobalTheory.SeeSaw.IdVMul

end
