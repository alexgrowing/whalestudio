import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (LatPair latRel eisClass eisTerm latPt eisClass_mk)

namespace GlobalTheory.HilbFam.EisCmp

variable {F : Type} [Field F] [NumberField F]

theorem card_realEmb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (Emb F) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ ↦ (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
  · intro τ τ' hτ
    ext y
    have := DFunLike.congr_fun hτ y
    simpa using this
  · intro φ
    have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
    exact ⟨hr.embedding, by ext y; simp⟩

theorem mem_split (𝔞 𝔟 : Frac F) (v : Fin 2 → F) :
    v ∈ split 𝔞 𝔟 0 ↔ v 0 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ v 1 ∈ latM 𝔞 := by
  show v 0 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ v 1 - v 0 * 0 ∈ latM 𝔞 ↔ _
  rw [mul_zero, sub_zero]

theorem unit_smul_apply (ε : (𝓞 F)ˣ) (v : Fin 2 → F) (i : Fin 2) : (ε • v) i = ((ε : 𝓞 F) : F) * v i := by
  rw [Pi.smul_apply, Units.smul_def, Algebra.smul_def]

def pair (𝔞 𝔟 : Frac F) (q : cls (split 𝔞 𝔟 0)) : LatPair 𝔞 𝔟 :=
  ⟨(q.1.out 1, q.1.out 0), ((mem_split 𝔞 𝔟 _).1 q.2.1).2, ((mem_split 𝔞 𝔟 _).1 q.2.1).1, fun h ↦ q.2.2 (by
    funext i
    fin_cases i
    · exact congrArg Prod.snd h
    · exact congrArg Prod.fst h)⟩

theorem bij (𝔞 𝔟 : Frac F) :
    Function.Bijective (fun q : cls (split 𝔞 𝔟 0) ↦ Quotient.mk (latRel 𝔞 𝔟) (pair 𝔞 𝔟 q)) := by
  constructor
  · intro q1 q2 h
    obtain ⟨ε, h1, h2⟩ := Quotient.exact h
    apply Subtype.ext
    rw [← Quotient.out_eq q1.1, ← Quotient.out_eq q2.1]
    refine (Quotient.sound ?_).symm
    refine ⟨ε, ?_⟩
    funext i
    show (ε • q1.1.out) i = _
    rw [unit_smul_apply]
    fin_cases i
    · exact h2.symm
    · exact h1.symm
  · intro cl
    obtain ⟨p, rfl⟩ := Quotient.exists_rep cl
    let v : Fin 2 → F := ![p.1.2, p.1.1]
    have hv : v ∈ split 𝔞 𝔟 0 := (mem_split 𝔞 𝔟 v).2 ⟨p.2.2.1, p.2.1⟩
    have hv0 : v ≠ 0 := fun h ↦ p.2.2.2 (Prod.ext (congrFun h 1) (congrFun h 0))
    obtain ⟨ε, hε⟩ : (Quotient.mk (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) v).out ∈ MulAction.orbit (𝓞 F)ˣ v :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) v))
    have hε' : (Quotient.mk (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) v).out = ε • v := hε.symm
    refine ⟨⟨Quotient.mk _ v, ?_, ?_⟩, ?_⟩
    · rw [hε']; exact Submodule.smul_mem _ (ε : 𝓞 F) hv
    · rw [hε']; exact (smul_ne_zero_iff_ne ε).2 hv0
    · refine (Quotient.sound (show (latRel 𝔞 𝔟).r p _ from ⟨ε, ?_, ?_⟩)).symm
      · exact (congrFun hε' 1).trans (unit_smul_apply ε v 1)
      · exact (congrFun hε' 0).trans (unit_smul_apply ε v 0)

theorem term_eq [IsTotallyReal F] (k : ℕ) (σ : ℂ) (w : Emb F → ℂ) (x : Fin 2 → F) :
    gTerm k σ w 1 x = (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
      ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) * eisTerm k σ w (x 1, x 0) := by
  have hP : ∏ τ, latPt w (x 1, x 0) τ = (2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * ∏ τ, coord w 1 x τ := by
    rw [← card_realEmb, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ ↦ ?_
    simp only [latPt, coord, Pi.one_apply]; ring
  have hΛ : (2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F ≠ 0 := pow_ne_zero _ Complex.two_pi_I_ne_zero
  unfold gTerm eisTerm
  rw [hP]
  generalize (2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F = Λ at hΛ
  have hn : ((‖Λ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hΛ)
  have h1 : Λ ^ k * Λ⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hΛ, one_pow]
  have h2 : ((‖Λ‖ : ℝ) : ℂ) ^ (2 * σ) * ((‖Λ‖ : ℝ) : ℂ) ^ (-2 * σ) = 1 := by
    rw [← Complex.cpow_add _ _ hn, show 2 * σ + -2 * σ = 0 by ring, Complex.cpow_zero]
  rw [mul_inv, mul_pow, norm_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  generalize (∏ τ, coord w 1 x τ)⁻¹ ^ k = A
  generalize ((‖∏ τ, coord w 1 x τ‖ : ℝ) : ℂ) ^ (-2 * σ) = B
  linear_combination (-(A * B) * (((‖Λ‖ : ℝ) : ℂ) ^ (2 * σ) * ((‖Λ‖ : ℝ) : ℂ) ^ (-2 * σ))) * h1 - (A * B) * h2

theorem hasSum_gTerm [IsTotallyReal F] (𝔞 𝔟 : Frac F) {k : ℕ} (hk : Even k) (σ : ℂ) (w : Emb F → ℂ) (S : ℂ)
    (h : HasSum (eisClass 𝔞 𝔟 k σ w) S) :
    HasSum (fun q : cls (split 𝔞 𝔟 0) ↦ gTerm k σ w 1 q.1.out)
      ((((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) * S) := by
  have h1 := ((Equiv.hasSum_iff (Equiv.ofBijective _ (bij 𝔞 𝔟))).2 h).mul_left
    (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ))
  have h2 : (fun q : cls (split 𝔞 𝔟 0) ↦ gTerm k σ w 1 q.1.out) = fun q : cls (split 𝔞 𝔟 0) ↦
      (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) *
        eisClass 𝔞 𝔟 k σ w (Quotient.mk (latRel 𝔞 𝔟) (pair 𝔞 𝔟 q)) := by
    funext q
    rw [eisClass_mk 𝔞 𝔟 hk, term_eq]
    rfl
  rw [h2]
  exact h1

theorem isGVal_of_isEis : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ)
    (w : Emb F → ℂ), Even k → IsEis 𝔞 𝔟 k G → w ∈ upperHalf F →
    IsGVal k (split 𝔞 𝔟 0) w 1 (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k * G w) := by
  intro F _ _ _ k 𝔞 𝔟 G w hk hG hw
  constructor
  · intro h2
    have h := hasSum_gTerm 𝔞 𝔟 hk 0 w _ (hG.1 h2 w hw)
    rwa [mul_zero, Complex.cpow_zero, mul_one] at h
  · rintro rfl
    obtain ⟨H, hH, rfl⟩ := hG.2 rfl
    have hn : ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (pow_ne_zero _ Complex.two_pi_I_ne_zero))
    refine ⟨fun σ ↦ (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ 2 *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) * H σ w, ?_, ?_, ?_⟩
    · have hHd : DifferentiableOn ℂ (fun σ ↦ H σ w) {σ : ℂ | -1 / 2 < σ.re} := hH.2.2 [] w hw
      have hAd : Differentiable ℂ fun σ : ℂ ↦ ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ 2 *
          ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ) := fun σ ↦
        (differentiableAt_const _).mul (((differentiableAt_const (2 : ℂ)).mul differentiableAt_id).const_cpow (Or.inl hn))
      exact hAd.differentiableOn.mul hHd
    · intro σ hσ
      obtain ⟨hsm, hHe⟩ := hH.1 σ hσ w hw
      exact hasSum_gTerm 𝔞 𝔟 hk σ w _ (by rw [hHe]; exact hsm.hasSum)
    · simp only [mul_zero, Complex.cpow_zero, mul_one]

end GlobalTheory.HilbFam.EisCmp
