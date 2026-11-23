import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoExcludedParameterOfLiftParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumNormSphericalZetaKernelGLTrivialRepStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGLZetaSumTrivialParameterSubOneLeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumNormSphericalZetaKernelUnramifiedUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormUnitaryZetaSumTrivialBoundSubOneLeStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta.AbsConv

theorem invGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r N : ℕ) (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), KerGL w N z φ → ∀ g, ∀ k ∈ KGL w r, φ (g * k) = φ g := by
  intro E _ _ w r N z φ h g k hk
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV (E := E) w
  obtain ⟨d, -, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w r ϖ (mem_Ov_of_isUnifV hϖ) hϖ g
  have htd : (k₁⁻¹ * g * k₂⁻¹ : GL (Fin r) (w.adicCompletion E)).1 = Matrix.diagonal (fun i => ϖ ^ d i) := by
    rw [Units.val_mul, Units.val_mul, e]
    simp [Matrix.mul_assoc]
    rfl
  calc φ (g * k) = φ (k₁ * (k₁⁻¹ * g * k₂⁻¹) * (k₂ * k)) := by congr 1; group
    _ = φ (k₁ * (k₁⁻¹ * g * k₂⁻¹) * k₂) := by
      rw [h ϖ hϖ d _ htd k₁ hk₁ (k₂ * k) (mul_mem hk₂ hk), h ϖ hϖ d _ htd k₁ hk₁ k₂ hk₂]
    _ = φ g := by congr 1; group

theorem invU : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (ϖ : w.adicCompletion E) (σ : w.adicCompletion E →+* w.adicCompletion E) (q r N : ℕ), IsUnramInv ϖ σ q → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), KerU ϖ q N z φ → ∀ g, ∀ k ∈ KU σ r, φ (g * k) = φ g := by
  intro E _ _ w ϖ σ q r N hU z φ h g k hk
  obtain ⟨d, t, -, htd, k₁, hk₁, k₂, hk₂, rfl⟩ := cartanU hU g
  rw [show k₁ * t * k₂ * k = k₁ * t * (k₂ * k) by group, h d t htd k₁ hk₁ _ (mul_mem hk₂ hk), h d t htd k₁ hk₁ k₂ hk₂]

theorem transport : ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H), (∀ g, g ∈ K ↔ e g ∈ K') → ∀ (f : H → ℝ), (∀ h, ∀ k ∈ K', f (h * k) = f h) → ∀ A : ℝ, HasSum (fun a : H ⧸ K' => f a.out) A → HasSum (fun a : G ⧸ K => f (e a.out)) A := by
  intro G H _ _ e K K' hK f hf A hA
  let Φ : G ⧸ K ≃ H ⧸ K' := Quotient.congr e.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hK]
    simp)
  have key : ∀ a : G ⧸ K, f (Φ a).out = f (e a.out) := by
    intro a
    have h1 : Φ a = (QuotientGroup.mk (e a.out) : H ⧸ K') := by
      conv_lhs => rw [← Quotient.out_eq a]
      rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K' (e a.out)
    rw [h1, hk, hf _ _ k.2]
  have := (Φ.hasSum_iff (f := fun b : H ⧸ K' => f b.out)).2 hA
  simpa [Function.comp_def, key] using this

theorem glSum : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r + 5 ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∃ A : ℝ, HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r => ‖φ a.out‖) A ∧ |A - 1| ≤ 27 ^ r * ((qV E w : ℝ) ^ 2)⁻¹ := by
  intro hP E _ _ w r t ht z φ hz hk
  obtain ⟨B, hc, hb, hs⟩ := GlobalTheory.T.hasSum_norm_sphericalZetaKernelGL_trivialRep hP E w r t (by omega) z φ hz hk
  refine ⟨_, by simpa using Complex.hasSum_re hs, ?_⟩
  have hq2 : 2 ≤ qV E w := one_lt_absNorm w
  have hX : ‖npow w (-((1 + (t : ℂ)) / 2))‖ = (qV E w : ℝ) ^ (-((1 + (t : ℝ)) / 2)) := by
    rw [norm_npow]
    congr 1
    simp
  refine le_trans ?_ (GlobalTheory.T.norm_GL_zetaSum_trivialParameter_sub_one_le (qV E w) hq2 r t ht B hc hb _ hX)
  have := Complex.abs_re_le_norm (eulerFac B (npow w (-((1 + (t : ℂ)) / 2))) *
    eulerFac (B.map fun β => β⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) *
      ∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹) - 1)
  simpa using this

theorem uSum : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r + 5 ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∃ A : ℝ, HasSum (fun a : GU σ r ⧸ KU σ r => ‖φ a.out‖) A ∧ |A - 1| ≤ 27 ^ r * ((q : ℝ) ^ 2)⁻¹ := by
  intro L _ _ _ ϖ σ q r t hU ht z φ hz hk
  obtain ⟨α, hb, hs⟩ := GlobalTheory.T.hasSum_norm_sphericalZetaKernel_unramifiedUnitary L ϖ σ q r t hU (by omega) z φ hz hk
  refine ⟨_, by simpa using Complex.hasSum_re hs, ?_⟩
  refine le_trans ?_ (GlobalTheory.T.norm_unitaryZetaSum_trivialBound_sub_one_le q r t hU.2.2.2.2.2.1 ht α hb)
  have := Complex.abs_re_le_norm (eulerFac (bcParam r α) (((q : ℂ) ^ (t + 1))⁻¹) *
    ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹) - 1)
  simpa using this

theorem local_place (hP : GlobalTheory.Published.UnramifiedDoublingGL) (D : D7) (V : HSp D) (hr : V.rank = D.R.r)
    (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (hz : ∀ w, ‖(z w : ℂ)‖ = 1) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Gv V v → ℂ) (hφ : IsLocKer V D.R.nV z v φ) :
    ∃ A : ℝ, HasSum (fun a : Gv V v ⧸ Kv V v => ‖φ a.out‖) A ∧
      |A - 1| ≤ 27 ^ D.R.r * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ := by
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hN : D.R.nV = V.rank + D.R.t := by rw [hr]; rfl
  have ht : V.rank + 5 ≤ D.R.t := by rw [hr]; exact D.R.rank_add_five_le
  rw [← hr]
  rcases GlobalTheory.LPositivity.split_or_inert D w with hs | hi
  · rw [hw] at hs
    obtain ⟨⟨e, he⟩, hq⟩ := GlobalTheory.NoExcl.chart V hw hs
    have hk := (hφ w hw).1 hs e he
    rw [hN] at hk
    obtain ⟨A, hA, hb⟩ := glSum hP D.host.E w V.rank D.R.t ht (z w) _ (hz w) hk
    refine ⟨A, ?_, ?_⟩
    · have := transport _ _ e (Kv V v) (KGL w V.rank) he.2 (fun g => ‖(φ ∘ e.symm) g‖)
        (fun g k hk' => congrArg norm (invGL _ w _ _ _ _ hk g k hk')) A hA
      simpa using this
    · have hq' : (qV D.host.E w : ℝ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
        rw [show qV D.host.E w = Ideal.absNorm w.asIdeal from rfl, hq]; rfl
      rwa [hq'] at hb
  · rw [hw] at hi
    obtain ⟨c, ϖ, e, hU, he, -, -⟩ := GlobalTheory.LPositivity.exists_inert_chart (isCMExt_host D) (GlobalTheory.NoExcl.isHermND_gram V)
      (SelfDual.isLattice_frameLat V) (SelfDual.isSelfDualAt_frameLat D V v) hw hi
    have hk := (hφ w hw).2 hi c ϖ e hU he
    rw [hN] at hk
    obtain ⟨A, hA, hb⟩ := uSum _ ϖ c (qV D.host.F v) V.rank D.R.t hU ht (z w) _ (hz w) hk
    refine ⟨A, ?_, hb⟩
    have := transport _ _ e (Kv V v) (KU c V.rank) he.2.2 (fun g => ‖(φ ∘ e.symm) g‖)
      (fun g k hk' => congrArg norm (invU _ w ϖ c _ _ _ hU _ _ hk g k hk')) A hA
    simpa using this

theorem absConv_localZeta : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (D : D7) (V : HSp D), V.rank = D.R.r → ∀ (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ), (∀ w, ‖(z w : ℂ)‖ = 1) → ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (φ : ∀ v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb}, Gv V v.1 → ℂ), (∀ v, IsLocKer V D.R.nV z v.1 (φ v)) → ∃ A : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} → ℝ, Summable (fun v => A v - 1) ∧ ∀ v, HasSum (fun a : Gv V v.1 ⧸ Kv V v.1 => ‖φ v a.out‖) (A v) := by
  intro hP D V hr z hz Sb φ hφ
  choose A hA hB using fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => local_place hP D V hr z hz v.1 (φ v) (hφ v)
  refine ⟨A, ?_, hA⟩
  have hs := (summable_rpow (K := D.host.F) ((Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) (σ := 2) (by norm_num)).mul_left (27 ^ D.R.r)
  refine Summable.of_norm_bounded hs fun v => ?_
  rw [Real.norm_eq_abs]
  refine (hB v).trans (le_of_eq ?_)
  congr 1
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

end GlobalTheory.FinZeta.AbsConv

end
