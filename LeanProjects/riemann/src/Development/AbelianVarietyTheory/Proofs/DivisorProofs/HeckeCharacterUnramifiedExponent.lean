import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormDifferentEqProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharIsUnitaryOfUnitaryInfinityType

noncomputable section

namespace GlobalTheory.BotLValue

section General

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem gamma_ne_zero {s : ℂ} {n : ℤ} (h : 0 < 2 * s.re + ((|n| : ℤ) : ℝ)) :
    Complex.Gamma (s + ((|n| : ℤ) : ℂ) / 2) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by
    have e : (s + ((|n| : ℤ) : ℂ) / 2).re = s.re + ((|n| : ℤ) : ℝ) / 2 := by
      rw [Complex.add_re, ← Complex.ofReal_intCast, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [e]
    linarith)

theorem exists_isHeckeL_of_completed {χ : HChar E} {n : I → ℤ} {Λ : ℂ → ℂ} (h : IsCompletedL χ n Λ) :
    ∃ L, IsHeckeL χ L := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hA : ∀ (z : ℂ) i, (2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2))) ≠ 0 := fun z i =>
    mul_ne_zero two_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto)
  refine ⟨fun z => Λ z * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
    (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹), ?_, fun z hz => ?_⟩
  · refine h.1.mul (Differentiable.fun_finsetProd fun i _ => ?_)
    refine Differentiable.mul (fun z => ?_) ?_
    · refine DifferentiableAt.inv ?_ (hA z i)
      exact (((differentiableAt_id.add_const _).neg).const_cpow (Or.inl hpi)).const_mul 2
    · exact Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  · obtain ⟨L, h1, h2⟩ := h.2 z hz
    have key : archFactor n z * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
        (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹) = 1 := by
      unfold archFactor
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun i _ => ?_
      have h0 : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
      rw [mul_mul_mul_comm, mul_inv_cancel₀ (hA z i), mul_inv_cancel₀ (gamma_ne_zero (by linarith)), one_mul]
    show HasProd _ (Λ z * _)
    rwa [h2, mul_comm (archFactor n z), mul_assoc, key, mul_one]

theorem exists_heckeL_ne_zero (hFE : GlobalTheory.Published.HeckeFunctionalEquationAbs) [IsTotallyComplex E]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {n : I → ℤ} (hu : IsUnitary χ)
    (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (hn : ∃ i, n i ≠ 0) :
    ∃ L, IsHeckeL χ L ∧ ∀ s : ℤ, (∀ i, 0 < 2 * s + |n i|) → L s ≠ 0 := by
  have hB := GlobalTheory.HeckeStrip.completedLBoundedInStrips
  have hn' : ∃ i, -n i ≠ 0 := hn.imp fun i h => neg_ne_zero.2 h
  have hi' := GlobalTheory.Published.HeckeFEModel.hasInf_inv hi
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  obtain ⟨Λ, hΛ, -⟩ := hB E I φ hφ χ n hu hi hn
  obtain ⟨Λ', hΛ', -⟩ := hB E I φ hφ χ⁻¹ (fun i => -n i) hu' hi' hn'
  obtain ⟨L, hL⟩ := exists_isHeckeL_of_completed hΛ
  obtain ⟨L', hL'⟩ := exists_isHeckeL_of_completed hΛ'
  refine ⟨L, hL, fun s hs => ?_⟩
  rcases le_or_gt 1 s with h1 | h1
  · have e : ((s.toNat : ℕ) : ℂ) = (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [← e]
    exact hL.ne_zero_nat hu (by omega)
  have g1 : ∀ i, Complex.Gamma ((1 - (s : ℂ)) + ((|-n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => gamma_ne_zero (by
    have h0 : (0 : ℝ) ≤ ((|-n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (-n i)
    have h2 : (s : ℝ) < 1 := by exact_mod_cast h1
    rw [Complex.sub_re, Complex.one_re, Complex.intCast_re]
    linarith)
  have hL1 : L' (1 - (s : ℂ)) ≠ 0 := by
    have e : (((1 - s).toNat : ℕ) : ℂ) = 1 - (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [← e]
    exact hL'.ne_zero_nat hu' (by omega)
  have hΛ'1 : Λ' (1 - (s : ℂ)) ≠ 0 := by
    rw [GlobalTheory.LValNe.completed_eq hΛ' hL' g1]
    exact mul_ne_zero (GlobalTheory.LValNe.archFactor_ne_zero g1) hL1
  have hΛs : Λ s ≠ 0 := fun h0 => hΛ'1 ((GlobalTheory.Published.HeckeFEModel.zero_iff hFE hφ hu hi hn hΛ hΛ' s).1 h0)
  have g0 : ∀ i, Complex.Gamma ((s : ℂ) + ((|n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => gamma_ne_zero (by
    rw [Complex.intCast_re]
    exact_mod_cast hs i)
  rw [GlobalTheory.LValNe.completed_eq hΛ hL g0] at hΛs
  exact right_ne_zero_of_mul hΛs

end General

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)

open NumberField IsDedekindDomain in
private theorem eq_or_eq_of_comp_eq_of_finrank_two {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (h2 : Module.finrank F E = 2) (ψ : F →+* ℂ)
    (ρ α β : E →+* ℂ) (hρ : ρ.comp (algebraMap F E) = ψ) (hα : α.comp (algebraMap F E) = ψ)
    (hβ : β.comp (algebraMap F E) = ψ) (hαβ : α ≠ β) : ρ = α ∨ ρ = β := by
  classical
  letI : Algebra F ℂ := ψ.toAlgebra
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let mk : ∀ γ : E →+* ℂ, γ.comp (algebraMap F E) = ψ → E →ₐ[F] ℂ := fun γ hγ =>
    { toRingHom := γ
      commutes' := fun a => (congrArg (fun f : F →+* ℂ => f a) hγ : _) }
  have hcoe : ∀ (γ : E →+* ℂ) (hγ : γ.comp (algebraMap F E) = ψ), ((mk γ hγ : E →ₐ[F] ℂ) : E →+* ℂ) = γ :=
    fun γ hγ => rfl
  by_contra hne
  push_neg at hne
  have hcard := AlgHom.card F E ℂ
  rw [h2] at hcard
  have hfa : mk ρ hρ ≠ mk α hα := fun e => hne.1 (by rw [← hcoe ρ hρ, ← hcoe α hα, e])
  have hfb : mk ρ hρ ≠ mk β hβ := fun e => hne.2 (by rw [← hcoe ρ hρ, ← hcoe β hβ, e])
  have hab : mk α hα ≠ mk β hβ := fun e => hαβ (by rw [← hcoe α hα, ← hcoe β hβ, e])
  have h3 : ({mk ρ hρ, mk α hα, mk β hβ} : Finset (E →ₐ[F] ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hfa, hfb]), Finset.card_pair hab]
  have := Finset.card_le_univ ({mk ρ hρ, mk α hα, mk β hβ} : Finset (E →ₐ[F] ℂ))
  omega

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.BotLValue.isCMType_embOver {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, _root_.GlobalTheory.AdelicU.EmbOver E w) :
    _root_.GlobalTheory.CMVal.IsCMType fun w => (τ w).1 := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt at h
  obtain ⟨hF, hE, h2, hσ⟩ := h
  unfold _root_.GlobalTheory.CMVal.IsCMType
  have hreal : ∀ v : InfinitePlace F, ComplexEmbedding.conjugate v.embedding = v.embedding :=
    fun v => ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp (hF.isReal v))
  have hconj : ∀ (v : InfinitePlace F) (γ : E →+* ℂ), γ.comp (algebraMap F E) = v.embedding →
      (ComplexEmbedding.conjugate γ).comp (algebraMap F E) = v.embedding := by
    intro v γ hγ
    rw [← hreal v, ← hγ]
    rfl
  have hτ : ∀ v : InfinitePlace F, ((τ v).1).comp (algebraMap F E) = v.embedding := fun v => (τ v).2
  have hne : ∀ v : InfinitePlace F, (τ v).1 ≠ ComplexEmbedding.conjugate (τ v).1 := by
    intro v e
    have hc := hE.isComplex (InfinitePlace.mk (τ v).1)
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff,
      ComplexEmbedding.isReal_iff] at hc
    exact hc e.symm
  intro ρ
  set v := InfinitePlace.mk (ρ.comp (algebraMap F E)) with hvdef
  have hv : ρ.comp (algebraMap F E) = v.embedding := by
    rcases InfinitePlace.embedding_mk_eq (ρ.comp (algebraMap F E)) with e | e
    · exact e.symm
    · rw [← hreal v, e]
      exact (star_star _).symm
  refine ⟨v, eq_or_eq_of_comp_eq_of_finrank_two h2 v.embedding ρ _ _ hv (hτ v) (hconj v _ (hτ v)) (hne v), ?_⟩
  intro w hw
  have hw' : ρ.comp (algebraMap F E) = w.embedding := by
    rcases hw with e | e
    · rw [e]; exact hτ w
    · rw [e]; exact hconj w _ (hτ w)
  rw [hvdef, hw', InfinitePlace.mk_embedding]

theorem charL_holValueAt_ne_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (χ : Chr F E), IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0 →
    ∀ (k : InfinitePlace F → ℤ) (d : ℕ), HasExp B.emb χ k → (∀ w, (d : ℤ) < |k w|) → ∀ T : Finset (Pl F), UnrOff χ (T : Set (Pl F)) →
    (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ T → ¬ UnrAt χ w) → ∀ z : ℤ, -(d : ℤ) ≤ 2 * z →
      ∃ c : ℂ, c ≠ 0 ∧ GlobalTheory.Cont.HolValueAt (charL χ (T : Set (Pl F))) (z : ℂ) c := by
  intro hK F E _ _ _ _ _ σ B hB χ hχ _ k d hk hd T _ hram z hz
  have := hB.cm.2.1
  obtain ⟨H, hloc, hinf⟩ := GlobalTheory.HeckeBridge.exists_hchar F E σ hB.cm χ hχ
  have hi := hinf _ _ hk
  have hu := GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf E H _ _ hi
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨L, hL, hne⟩ := exists_heckeL_ne_zero hK.heckeTateFunctionalEquation.abs (isCMType_embOver hB.cm B.emb) hu hi
    ⟨w₀, fun h => by have := hd w₀; rw [h, abs_zero] at this; omega⟩
  have hun : ∀ w, UnrAt χ w ↔ H.UnrAt w := fun w => forall₂_congr fun x _ => by rw [hloc]
  have hfam : charFam χ = heckeFam H := funext fun w => by
    by_cases h : H.UnrAt w
    · rw [heckeFam_of_unrAt h, charFam_of_unrAt ((hun w).2 h)]
      exact congrArg _ (hloc _ _).symm
    · rw [heckeFam_of_not_unrAt h]
      exact if_neg (mt (hun w).1 h)
  refine ⟨L z, hne z fun w => by have := hd w; omega, ?_⟩
  refine (GlobalTheory.Cont.holValueAt_self (σ := (z : ℂ).re - 1) (fun s _ => hL.1.analyticAt s) (by linarith)).congr
    ⟨1, fun s hs => ?_⟩
  rw [charL, hfam]
  exact (GlobalTheory.SqStep.heckeL_eq_of_ram (S := above E (T : Set (Pl F))) (fun w hw => mt (hun w).2 (hram w hw)) hL hs).symm

end GlobalTheory.BotLValue

end
