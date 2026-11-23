import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.InfOrthWW
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CompCoordMem
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GenSL
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.JExExists
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem sbMul {F : Type} [Field F] [NumberField F] {v : P F} {a : M2 v → ℂ} (ha : a ∈ SB (M2 v))
    (p q : M2 v) (h1 : p * q = 1) (h2 : q * p = 1) : (fun m => a (m * p)) ∈ SB (M2 v) := by
  let e : M2 v ≃ₜ M2 v :=
    { toFun := fun m => m * p
      invFun := fun m => m * q
      left_inv := fun m => by simp [Matrix.mul_assoc, h1]
      right_inv := fun m => by simp [Matrix.mul_assoc, h2]
      continuous_toFun := continuous_id.mul continuous_const
      continuous_invFun := continuous_id.mul continuous_const }
  have ha' : IsLocallyConstant a ∧ HasCompactSupport a := ha
  have hr : IsLocallyConstant (a ∘ e) ∧ HasCompactSupport (a ∘ e) :=
    ⟨ha'.1.comp_continuous e.continuous, ha'.2.comp_homeomorph e⟩
  exact hr

private theorem sg0 {F : Type} [Field F] [NumberField F] (v : P F) : sg v 0 = 0 := by
  have h := (sgLaws F v).1 0 0
  simpa using h

private theorem sgNeg {F : Type} [Field F] [NumberField F] (v : P F) (c : Kv v) : sg v (-c) = - sg v c := by
  have h := (sgLaws F v).1 c (-c)
  rw [add_neg_cancel, sg0] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

private theorem exPhi {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {v : P F} {δ : F} {θ : Kv v}
    {u : V4 F → ℂ} (hu : GoodU v δ θ u) {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) :
    ∃ φ : S4 F, φ.1 = ten v θ u (Pt a) := by
  obtain ⟨T, hT⟩ := ptMem F v
  obtain ⟨φ, -, h⟩ := hu (T ⟨a, ha⟩).1 (T ⟨a, ha⟩).2
  exact ⟨φ, h.trans (by rw [hT])⟩

theorem UpperTheory.ConvolutionTheory.R2.I.omSL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (v : P F) (θ : Kv v), θ ^ 2 = algebraMap F (Kv v) D.δ → θ ≠ 0 →
      ∀ u u', GoodU v D.δ θ u → GoodU v D.δ θ u' → (∀ a ∈ SB (M2 v), ∀ φ : S4 F, φ.1 = ten v θ u (Pt a) →
        (W.Om (wW F) φ).1 = ten v θ u' (Pt fun m => a (m * !![0, 1; -1, 0]))) → Mod v θ W u' := by
  intro F E _ _ _ _ _ _ _ D W v θ hθ hθ0 u u' hu hu' hw
  refine ⟨hu', fun j hj => ?_⟩
  have hent := ((jEx F v).2 j hj).2.2.2
  have hn := (omW F E D W v θ hθ hθ0).1
  let H : Subgroup (SL v) :=
    { carrier := {g | ∀ a ∈ SB (M2 v), ∀ φ : S4 F, φ.1 = ten v θ u' (Pt a) →
        (W.Om (j g) φ).1 = ten v θ u' (Pt fun m => a (m * g.1))}
      one_mem' := by
        intro a _ φ h
        have e : (fun m : M2 v => a (m * (1 : SL v).1)) = a := by
          funext m
          simp
        rw [e, map_one, map_one, ← h]
        rfl
      mul_mem' := by
        intro g h hg hh a ha φ hφ
        have hp : (h.1 * (h⁻¹).1 : M2 v) = 1 := congrArg Subtype.val (mul_inv_cancel h)
        have hq : ((h⁻¹).1 * h.1 : M2 v) = 1 := congrArg Subtype.val (inv_mul_cancel h)
        have h1 := hh a ha φ hφ
        have h2 := hg _ (sbMul ha h.1 (h⁻¹).1 hp hq) _ h1
        have e : (fun m : M2 v => a (m * (g * h).1)) = fun m => a (m * g.1 * h.1) := by
          funext m
          rw [Matrix.mul_assoc]
          rfl
        rw [e, ← h2, map_mul, map_mul, Module.End.mul_apply]
      inv_mem' := by
        intro g hg a ha φ hφ
        have hp : (g.1 * (g⁻¹).1 : M2 v) = 1 := congrArg Subtype.val (mul_inv_cancel g)
        have hq : ((g⁻¹).1 * g.1 : M2 v) = 1 := congrArg Subtype.val (inv_mul_cancel g)
        have ha' := sbMul ha (g⁻¹).1 g.1 hq hp
        obtain ⟨φ', h'⟩ := exPhi hu' ha'
        have h1 := hg _ ha' φ' h'
        have e : (fun m : M2 v => a (m * g.1 * (g⁻¹).1)) = a := by
          funext m
          rw [Matrix.mul_assoc, hp, Matrix.mul_one]
        have h2 : W.Om (j g) φ' = φ := by
          apply Subtype.ext
          rw [h1, hφ, e]
        rw [← h2, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
        exact h' }
  have hup : ∀ (g : SL v) (b : Kv v), g.1 = !![1, b; 0, 1] → g ∈ H := by
    intro g b hg a _ φ hφ
    have e : j g = nU (sg v b) := by
      apply Subtype.ext
      ext i k
      have h := hent g i k
      have h' : (j g).1 i k = (1 : Matrix (Fin 2) (Fin 2) (A F)) i k + sg v (g.1 i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k) := h
      rw [h', hg]
      fin_cases i <;> fin_cases k <;> simp [nU, sg0]
    rw [e, hn u' a b φ hφ, hg]
  have hlow : ∀ (g : SL v) (c : Kv v), g.1 = !![1, 0; c, 1] → g ∈ H := by
    intro g c hg a ha φ hφ
    have e1 : (!![0, 1; -1, 0] * !![0, -1; 1, 0] : M2 v) = 1 := by
      simp [Matrix.mul_fin_two, Matrix.one_fin_two]
    have e2 : (!![0, -1; 1, 0] * !![0, 1; -1, 0] : M2 v) = 1 := by
      simp [Matrix.mul_fin_two, Matrix.one_fin_two]
    have e3 : (!![1, -c; 0, 1] * !![1, c; 0, 1] : M2 v) = 1 := by
      simp [Matrix.mul_fin_two, Matrix.one_fin_two]
    have e4 : (!![1, c; 0, 1] * !![1, -c; 0, 1] : M2 v) = 1 := by
      simp [Matrix.mul_fin_two, Matrix.one_fin_two]
    have e5 : (!![0, 1; -1, 0] * (!![1, -c; 0, 1] * !![0, -1; 1, 0]) : M2 v) = !![1, 0; c, 1] := by
      simp [Matrix.mul_fin_two]
    have ha0 := sbMul ha !![0, -1; 1, 0] !![0, 1; -1, 0] e2 e1
    obtain ⟨φ0, h0⟩ := exPhi hu ha0
    have h1 : W.Om (wW F) φ0 = φ := by
      apply Subtype.ext
      rw [hw _ ha0 φ0 h0, hφ]
      have e : (fun m : M2 v => a (m * !![0, 1; -1, 0] * !![0, -1; 1, 0])) = a := by
        funext m
        rw [Matrix.mul_assoc, e1, Matrix.mul_one]
      rw [e]
    have ej : (j g).1 = !![1, 0; sg v c, 1] := by
      ext i k
      have h := hent g i k
      have h' : (j g).1 i k = (1 : Matrix (Fin 2) (Fin 2) (A F)) i k + sg v (g.1 i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k) := h
      rw [h', hg]
      fin_cases i <;> fin_cases k <;> simp [sg0]
    have e : j g * wW F = wW F * nU (sg v (-c)) := by
      apply Subtype.ext
      show (j g).1 * (wW F).1 = (wW F).1 * (nU (sg v (-c))).1
      rw [ej, sgNeg]
      simp [wW, nU, Matrix.mul_fin_two]
    have h2 := hn u _ (-c) φ0 h0
    have ha1 := sbMul ha0 !![1, -c; 0, 1] !![1, c; 0, 1] e3 e4
    have h3 := hw _ ha1 (W.Om (nU (sg v (-c))) φ0) h2
    have h4 : W.Om (j g) (W.Om (wW F) φ0) = W.Om (wW F) (W.Om (nU (sg v (-c))) φ0) := by
      rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
    rw [← h1, h4, h3, hg]
    have e6 : (fun m : M2 v => a (m * !![0, 1; -1, 0] * !![1, -c; 0, 1] * !![0, -1; 1, 0])) =
        fun m => a (m * !![1, 0; c, 1]) := by
      funext m
      rw [Matrix.mul_assoc, Matrix.mul_assoc, e5]
    rw [e6]
  have htop := genSL (Kv v) H hup hlow
  intro g a ha φ hφ
  have hg : g ∈ H := htop ▸ Subgroup.mem_top g
  exact hg a ha φ hφ
