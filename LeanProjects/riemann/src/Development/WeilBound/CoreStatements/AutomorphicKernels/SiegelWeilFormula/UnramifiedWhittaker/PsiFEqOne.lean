import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def psiF {v : HeightOneSpectrum (𝓞 F)} (ψv : Fv F v → ℂ) (ϖ c : Fv F v) (k : ℕ) (a : Fv F v ⊗[F] E) : ℂ :=
  ψv (c * ((2 : Fv F v)⁻¹ * ((ϖ ^ k)⁻¹ * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) a)))

theorem sigR_smul {v : HeightOneSpectrum (𝓞 F)} (σ : E →ₐ[F] E) (c : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

variable {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

namespace GoodLoc

variable (hG : GoodLoc σ J T bs v ψv S σS ϖ ε)
include hG

def pS : S := ⟨_, hG.unif_S⟩

theorem psi_of_mem {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) : ψv x = 1 := by
  have := (hG.psi_cond 1).2 (one_mem _) x hx
  simpa using this

theorem trace_mem {a : Fv F v ⊗[F] E} (ha : a ∈ S) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) a ∈ v.adicCompletionIntegers F := by
  have := (hG.trace_dual a).2 ha 1 (one_mem _)
  simpa using this

theorem half_mem : (2 : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff, norm_inv, hG.two, inv_one]

theorem psiF_eq_one {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) (k : ℕ) {a : S}
    (ha : a ∈ lev hG.pS k) : psiF ψv ϖ c k (a : Fv F v ⊗[F] E) = 1 := by
  obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.1 ha
  apply hG.psi_of_mem
  have e1 : ((c' * hG.pS ^ k : S) : Fv F v ⊗[F] E) = (ϖ ^ k) • (c' : Fv F v ⊗[F] E) := by
    rw [Subring.coe_mul, Subring.coe_pow, Algebra.smul_def, map_pow, mul_comm]
    rfl
  rw [e1, LinearMap.map_smul, smul_eq_mul, ← mul_assoc (ϖ ^ k)⁻¹, inv_mul_cancel₀ (pow_ne_zero _ hG.unif_ne), one_mul]
  exact mul_mem hc (mul_mem hG.half_mem (hG.trace_mem c'.2))

theorem psiF_add (c : Fv F v) (k : ℕ) (a b : Fv F v ⊗[F] E) :
    psiF ψv ϖ c k (a + b) = psiF ψv ϖ c k a * psiF ψv ϖ c k b := by
  simp only [psiF, map_add, mul_add, hG.psi_add]

def psiLev {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) (k : ℕ) : AddChar (S ⧸ lev hG.pS k) ℂ where
  toFun x := Quotient.liftOn' x (fun a : S => psiF ψv ϖ c k (a : Fv F v ⊗[F] E)) (fun a b hab => by
    have h : a - b ∈ lev hG.pS k := (Submodule.quotientRel_def _).1 hab
    have e : (a : Fv F v ⊗[F] E) = ((a - b : S) : Fv F v ⊗[F] E) + (b : Fv F v ⊗[F] E) := by simp
    show psiF ψv ϖ c k (a : Fv F v ⊗[F] E) = psiF ψv ϖ c k (b : Fv F v ⊗[F] E)
    rw [e, hG.psiF_add, hG.psiF_eq_one hc k h, one_mul])
  map_zero_eq_one' := by
    show psiF ψv ϖ c k ((0 : S) : Fv F v ⊗[F] E) = 1
    simp only [psiF, ZeroMemClass.coe_zero, map_zero, mul_zero, hG.psi_zero]
  map_add_eq_mul' x y := by
    induction x using Quotient.inductionOn' with
    | h a =>
      induction y using Quotient.inductionOn' with
      | h b =>
        show psiF ψv ϖ c k ((a + b : S) : Fv F v ⊗[F] E) = psiF ψv ϖ c k (a : Fv F v ⊗[F] E) * psiF ψv ϖ c k (b : Fv F v ⊗[F] E)
        rw [Subring.coe_add, hG.psiF_add]

theorem psiLev_mk {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) (k : ℕ) (a : S) :
    hG.psiLev hc k (Ideal.Quotient.mk _ a) = psiF ψv ϖ c k (a : Fv F v ⊗[F] E) := rfl

def hermLev (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X) : HermR (Fv F v) σ n :=
  ⟨fun a b => (ϖ ^ k)⁻¹ • (X a b : Fv F v ⊗[F] E), fun a b => by
    rw [sigR_smul, ← hG.sig]
    congr 2
    have := congrFun (congrFun hX a) b
    simpa [PositivityTheory.PfSWUS.Loc.cT] using this⟩

end GoodLoc

def H0 (S : Subring (Fv F v ⊗[F] E)) (σ : E →ₐ[F] E) (n : ℕ) : AddSubgroup (HermR (Fv F v) σ n) where
  carrier := {b | ∀ i j, (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j ∈ S}
  zero_mem' := fun i j => by simp
  add_mem' := fun ha hb i j => by simpa using add_mem (ha i j) (hb i j)
  neg_mem' := fun ha i j => by simpa using neg_mem (ha i j)

end PositivityTheory.SiegelWeilFormula.Gunr

end
