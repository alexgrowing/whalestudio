import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdIntegralMonicCoprimeDerivativeBezoutFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAevalKernelsOrthogonalOfCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalProjectionIntegralAdicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenOrdLConjGramDetOfUnitGramAdicCompletionStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem kapSign_eq_one_of_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    γ ∈ KL n w → ∀ Q₁ : (w.adicCompletion E)[X],
    Q₁ ∣ P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) → kapSign n w Q₁ γ.1 = 1 := by
  intro E _ _ _ n w hinv hv P₀ hcop γ hchar hK Q₁ hdvd
  unfold kapSign
  split_ifs with hs
  · rfl
  simp only
  have hU : (γ.1.val.map (cj w))ᵀ * γ.1.val = 1 := by
    have h2 : (UL n w : Subgroup (GLw n w)) = UJ (cj w) 1 := by unfold UL; rw [if_neg hs]
    have h : γ.1 ∈ UJ (cj w) 1 := by rw [← h2]; exact γ.2
    simpa [UJ, cT] using h
  set K := w.adicCompletion E
  set f := algebraMap (w.adicCompletionIntegers E) K with hf
  have finj : Function.Injective f := fun a b h => Subtype.ext h
  set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₁)) with hV₁
  set G := (Matrix.of fun i j => ∑ k, cj w ((Module.finBasis K V₁ i).1 k) * (Module.finBasis K V₁ j).1 k) with hG
  by_cases h0 : G.det = 0
  · rw [h0]; simp [ordL]
  obtain ⟨g, hg⟩ := hK
  have hγ : γ.1.val = g.val.map (fun x => (x : K)) := by
    have := congrArg (fun u => (u : GLw n w).val) hg
    simpa [bc] using this.symm
  have hmon : P₀.Monic := by
    apply Polynomial.monic_of_injective finj
    rw [← hchar]; exact Matrix.charpoly_monic _
  obtain ⟨Q₁₀, Q₂₀, A, B, c, hc, hP, hAB, hQ⟩ := GlobalTheory.T.dvd_integral_monic_coprime_derivative_bezout_factor E w P₀ hmon hcop Q₁ hdvd
  set q₁ := Q₁₀.map f
  set q₂ := Q₂₀.map f
  have hAB' : A.map f * q₁ + B.map f * q₂ = 1 := by
    have := congrArg (Polynomial.map f) hAB
    simpa [Polynomial.map_add, Polynomial.map_mul] using this
  have hCH : aeval γ.1.val (q₁ * q₂) = 0 := by
    rw [← Polynomial.map_mul, ← hP, ← hchar]; exact Matrix.aeval_self_charpoly _
  have hmem : ∀ x, x ∈ V₁ ↔ aeval γ.1.val q₁ *ᵥ x = 0 := by
    intro x
    rw [hV₁, LinearMap.mem_ker, Matrix.toLin'_apply, hQ, map_mul, aeval_C]
    rw [show (algebraMap K (Matrix (Fin n) (Fin n) K) c) = c • (1 : Matrix (Fin n) (Fin n) K) from
      (Algebra.algebraMap_eq_smul_one c)]
    rw [smul_mul_assoc, one_mul, Matrix.smul_mulVec, smul_eq_zero]
    simp [hc]
  set e := aeval γ.1.val (q₂ * B.map f) with he
  have heint : ∀ i j, Valued.v (e i j) ≤ 1 := by
    intro i j
    have : e = (aeval g.val (Q₂₀ * B)).map (fun x => (x : K)) := by
      rw [he, ← Polynomial.map_mul, Polynomial.aeval_map_algebraMap, hγ,
        show g.val.map (fun x => (x : K)) = (Algebra.ofId (w.adicCompletionIntegers E) K).mapMatrix g.val from rfl,
        Polynomial.aeval_algHom_apply]
      rfl
    rw [this, Matrix.map_apply]
    exact ((aeval g.val (Q₂₀ * B)) i j).2
  have hcomm1 : ∀ x, aeval γ.1.val q₁ *ᵥ (e *ᵥ x) = 0 := by
    intro x
    rw [Matrix.mulVec_mulVec, he, ← map_mul, ← mul_assoc, map_mul, hCH, zero_mul, Matrix.zero_mulVec]
  have he1 : e = 1 - aeval γ.1.val (A.map f) * aeval γ.1.val q₁ := by
    rw [he, ← map_mul, mul_comm q₂, eq_sub_iff_add_eq, ← map_add, add_comm, hAB', map_one]
  have hfix : ∀ x ∈ V₁, e *ᵥ x = x := by
    intro x hx
    rw [he1, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, (hmem x).1 hx,
      Matrix.mulVec_zero, sub_zero]
  have hker2 : ∀ y, aeval γ.1.val q₂ *ᵥ (y - e *ᵥ y) = 0 := by
    intro y
    rw [he1, Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel, Matrix.mulVec_mulVec, ← map_mul, ← map_mul,
      show q₂ * (A.map f * q₁) = A.map f * (q₁ * q₂) by ring, map_mul, hCH, mul_zero, Matrix.zero_mulVec]
  have horth := GlobalTheory.T.unitary_aeval_kernels_orthogonal_of_coprime K (cj w) n γ.1.val hU q₁ q₂ (A.map f) (B.map f) hAB' hCH V₁ hmem (Module.finBasis K V₁) h0
  obtain ⟨s, fb, hfb⟩ := GlobalTheory.T.orthogonal_projection_integral_adic E w (cj w) hinv hv n V₁ e heint (fun x => (hmem _).2 (hcomm1 x)) hfix
    (fun x hx y => horth x hx _ (hker2 y))
  exact GlobalTheory.T.even_ordL_conjGramDet_of_unit_gram_adicCompletion E w (cj w) hv n V₁ (Module.finBasis K V₁) fb hfb

end GlobalTheory.BCT
