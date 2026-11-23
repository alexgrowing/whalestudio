import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.CvGelfandAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
import GroundTheory.AutomorphicForms.Cartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.BCT GlobalTheory.LFun GroundTheory.Automorphic PositivityTheory.Rg.BcB.G8
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

private def trG {F : Type} [Field F] {n : ℕ} (g : GL (Fin n) F) : GL (Fin n) F :=
  ⟨g.val.transpose, (g⁻¹).val.transpose,
    by rw [← Matrix.transpose_mul]; simp,
    by rw [← Matrix.transpose_mul]; simp⟩

private theorem trG_val {F : Type} [Field F] {n : ℕ} (g : GL (Fin n) F) : (trG g).val = g.val.transpose := rfl

private theorem trG_mul {F : Type} [Field F] {n : ℕ} (x y : GL (Fin n) F) : trG (x * y) = trG y * trG x :=
  Units.ext (by simp [trG_val, Matrix.transpose_mul])

private theorem trG_trG {F : Type} [Field F] {n : ℕ} (x : GL (Fin n) F) : trG (trG x) = x :=
  Units.ext (by simp [trG_val])

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem trG_mem {w : HeightOneSpectrum (𝓞 E)} {k : GL (Fin n) (w.adicCompletion E)}
    (hk : k ∈ KGL w n) : trG k ∈ KGL w n := by
  have h := GlobalTheory.StabInt.mem_integralGL_of_mem_KGL hk
  rw [GLnLocal.mem_integralGL_iff] at h
  refine GlobalTheory.StabInt.mem_KGL_of_mem_integralGL ?_
  rw [GLnLocal.mem_integralGL_iff]
  exact ⟨fun i j => h.1 j i, fun i j => h.2 j i⟩

private theorem trG_diagPow (w : HeightOneSpectrum (𝓞 E)) (μ : Fin n → ℤ) :
    trG (Cartan.diagPow (w.adicCompletion E) n μ) = Cartan.diagPow (w.adicCompletion E) n μ :=
  Units.ext (by rw [trG_val, Cartan.coe_diagPow, Matrix.diagonal_transpose])

private theorem trG_double (w : HeightOneSpectrum (𝓞 E)) (x : GL (Fin n) (w.adicCompletion E)) :
    ∃ k ∈ KGL w n, ∃ k' ∈ KGL w n, trG x = k * x * k' := by
  obtain ⟨μ, -, k₁, h₁, k₂, h₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul (w.adicCompletion E) n x
  have h₁' := GlobalTheory.StabInt.mem_KGL_of_mem_integralGL h₁
  have h₂' := GlobalTheory.StabInt.mem_KGL_of_mem_integralGL h₂
  refine ⟨trG k₂ * k₁⁻¹, (KGL w n).mul_mem (trG_mem h₂') ((KGL w n).inv_mem h₁'),
    k₂⁻¹ * trG k₁, (KGL w n).mul_mem ((KGL w n).inv_mem h₂') (trG_mem h₁'), ?_⟩
  rw [trG_mul, trG_mul, trG_diagPow]
  group

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.cvComm2 :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.CvGelfand → UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.CvComm2 := by
  intro h E _ _ _ a b w f g hf hg
  obtain ⟨hoa, hca⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨hob, hcb⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  refine h (GLw a w × GLw b w) (K2 a b w) (hoa.prod hob) (hca.prod hcb)
    (fun x => (trG x.1, trG x.2)) ?_ ?_ ?_ ?_ f g hf hg
  · intro x y
    exact Prod.ext (trG_mul _ _) (trG_mul _ _)
  · intro x
    exact Prod.ext (trG_trG _) (trG_trG _)
  · intro k hk
    exact ⟨trG_mem hk.1, trG_mem hk.2⟩
  · intro x
    obtain ⟨k₁, h₁, k₂, h₂, e⟩ := trG_double w x.1
    obtain ⟨l₁, i₁, l₂, i₂, e'⟩ := trG_double w x.2
    exact ⟨(k₁, l₁), ⟨h₁, i₁⟩, (k₂, l₂), ⟨h₂, i₂⟩, Prod.ext e e'⟩
