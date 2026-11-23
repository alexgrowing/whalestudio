import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMeasureOfBoundedMoments
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

namespace GlobalTheory.MonomialDense
open GlobalTheory.MultiMahler

variable {p : ℕ} [Fact p.Prime]

noncomputable def incl (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* ℂ_[p] :=
  (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom

theorem continuous_incl : Continuous (incl p) :=
  (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem factorial_mul_binomC (k : ℕ) (x : ℤ_[p]) :
    (k.factorial : ℂ_[p]) * binomC k x
      = incl p (Polynomial.aeval x (descPochhammer ℤ k)) := by
  have h1 : binomC k x = incl p (Ring.choose x k) := rfl
  have h2 := Ring.descPochhammer_eq_factorial_smul_choose x k
  rw [← Polynomial.aeval_eq_smeval] at h2
  rw [h1, h2, nsmul_eq_mul, map_mul, map_natCast]

theorem exists_mahler_expansion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    [IsUltrametricDist E] [CompleteSpace E] (f : C(ℤ_[p], E)) :
    ∃ t : ℕ → C(ℤ_[p], E), HasSum t f ∧
      ∀ n, ∃ a : E, ∀ x, t n x = ((mahler n x : ℤ_[p]) : ℚ_[p]) • a := by
  letI : Module ℤ_[p] E := Module.compHom E (algebraMap ℤ_[p] ℚ_[p])
  haveI : IsBoundedSMul ℤ_[p] E := IsBoundedSMul.of_norm_smul_le fun r x =>
    norm_smul_le (r : ℚ_[p]) x
  exact ⟨_, PadicInt.hasSum_mahler f, fun n => ⟨_, fun _ => rfl⟩⟩

variable {Z : Type} [TopologicalSpace Z] [CompactSpace Z]

omit [CompactSpace Z] in
theorem binomC_comp_mem (S : Subalgebra ℂ_[p] C(Z, ℂ_[p])) (φ : C(Z, ℤ_[p]))
    (X : C(Z, ℂ_[p])) (hX : ∀ z, X z = incl p (φ z)) (hS : X ∈ S) (k : ℕ) :
    (binomC k).comp φ ∈ S := by
  have hmem : ∀ P : Polynomial ℤ, ∃ G ∈ S, ∀ z, G z = incl p (Polynomial.aeval (φ z) P) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
      obtain ⟨G, hG, hG'⟩ := hP
      obtain ⟨G₂, hG₂, hG₂'⟩ := hQ
      exact ⟨G + G₂, S.add_mem hG hG₂, fun z => by simp [hG', hG₂']⟩
    | monomial n a =>
      refine ⟨(a : ℂ_[p]) • X ^ n, S.smul_mem (S.pow_mem hS n) _, fun z => ?_⟩
      simp [hX, Polynomial.aeval_monomial]
  obtain ⟨G, hG, hG'⟩ := hmem (descPochhammer ℤ k)
  have hk : (k.factorial : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have : (binomC k).comp φ = (k.factorial : ℂ_[p])⁻¹ • G := by
    ext z
    change binomC k (φ z) = (k.factorial : ℂ_[p])⁻¹ * G z
    rw [hG', ← factorial_mul_binomC, inv_mul_cancel_left₀ hk]
  rw [this]
  exact S.smul_mem hG _

noncomputable def evalAlong {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (φ : C(Z, ℤ_[p])) (ψ : C(Z, Y)) :
    C(ℤ_[p], C(Y, ℂ_[p])) →L[ℂ_[p]] C(Z, ℂ_[p]) :=
  LinearMap.mkContinuous
    { toFun := fun G => ⟨fun z => G (φ z) (ψ z), by fun_prop⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun G => by
      rw [one_mul, ContinuousMap.norm_le _ (norm_nonneg _)]
      intro z
      exact ((G (φ z)).norm_coe_le_norm _).trans (G.norm_coe_le_norm _))

theorem comp_mem (S : Subalgebra ℂ_[p] C(Z, ℂ_[p])) (hS : IsClosed (S : Set C(Z, ℂ_[p])))
    (g : ℕ) : ∀ (φ : C(Z, Fin g → ℤ_[p])),
      (∀ i, ∃ X ∈ S, ∀ z, X z = incl p (φ z i)) →
      ∀ F : C(Fin g → ℤ_[p], ℂ_[p]), F.comp φ ∈ S := by
  induction g with
  | zero =>
    intro φ _ F
    have : F.comp φ = algebraMap ℂ_[p] C(Z, ℂ_[p]) (F 0) := by
      ext z
      simp [Subsingleton.elim (φ z) 0]
    rw [this]
    exact S.algebraMap_mem _
  | succ g ih =>
    intro φ hφ F
    obtain ⟨t, ht, ht'⟩ := exists_mahler_expansion (curryFirst F)
    let φ0 : C(Z, ℤ_[p]) := ⟨fun z => φ z 0, by fun_prop⟩
    let ψ : C(Z, Fin g → ℤ_[p]) := ⟨fun z i => φ z i.succ, by fun_prop⟩
    have h := (evalAlong φ0 ψ).hasSum ht
    have e : evalAlong φ0 ψ (curryFirst F) = F.comp φ := by
      ext z
      exact congrArg F (Fin.cons_self_tail (φ z))
    rw [e] at h
    refine hS.mem_of_tendsto h (Filter.Eventually.of_forall fun s => S.sum_mem fun n _ => ?_)
    obtain ⟨a, ha⟩ := ht' n
    have e2 : evalAlong φ0 ψ (t n) = (binomC n).comp φ0 * a.comp ψ := by
      ext z
      change t n (φ0 z) (ψ z) = _
      rw [ha]
      change ((mahler n (φ0 z) : ℤ_[p]) : ℚ_[p]) • a (ψ z) = _
      rw [Algebra.smul_def]
      rfl
    rw [e2]
    obtain ⟨X, hX, hX'⟩ := hφ 0
    exact S.mul_mem (binomC_comp_mem S φ0 X hX' hX n) (ih ψ (fun i => hφ i.succ) a)

theorem eq_zero_of_monomials : ∀ (p r : ℕ) [Fact p.Prime] (μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p]), (∀ (m : ℕ) (k : Fin m → Fin r) (g : C(Fin r → ℤ_[p], ℂ_[p])), (∀ a, g a = ∏ j, zc (a (k j))) → μ g = 0) → μ = 0 := by
  intro p r _ μ hμ
  let X : Fin r → C(Fin r → ℤ_[p], ℂ_[p]) := fun i =>
    ⟨fun a => incl p (a i), continuous_incl.comp (continuous_apply i)⟩
  let A : Subalgebra ℂ_[p] C(Fin r → ℤ_[p], ℂ_[p]) := Algebra.adjoin ℂ_[p] (Set.range X)
  have hA : ∀ f ∈ A, μ f = 0 := by
    intro f hf
    have hf' : f ∈ Submodule.span ℂ_[p] (Submonoid.closure (Set.range X) : Set _) := by
      rw [← Algebra.adjoin_eq_span]; exact hf
    refine (Submodule.span_le (p := LinearMap.ker μ.toLinearMap)).mpr ?_ hf'
    intro g hg
    have : ∃ (m : ℕ) (k : Fin m → Fin r), ∀ a, g a = ∏ j, zc (a (k j)) := by
      induction hg using Submonoid.closure_induction_left with
      | one => exact ⟨0, Fin.elim0, fun a => by simp⟩
      | mul_left x hx y _ ih =>
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨m, k, hk⟩ := ih
        refine ⟨m + 1, Fin.cons i k, fun a => ?_⟩
        rw [Fin.prod_univ_succ, ContinuousMap.mul_apply, hk]
        rfl
    obtain ⟨m, k, hk⟩ := this
    exact hμ m k g hk
  ext F
  have hF := comp_mem A.topologicalClosure A.isClosed_topologicalClosure r (ContinuousMap.id _)
    (fun i => ⟨X i, A.le_topologicalClosure (Algebra.subset_adjoin ⟨i, rfl⟩), fun _ => rfl⟩) F
  have hcl : closure (A : Set C(Fin r → ℤ_[p], ℂ_[p])) ⊆ {f | μ f = 0} :=
    closure_minimal hA (isClosed_eq μ.continuous continuous_const)
  exact hcl hF

end GlobalTheory.MonomialDense
