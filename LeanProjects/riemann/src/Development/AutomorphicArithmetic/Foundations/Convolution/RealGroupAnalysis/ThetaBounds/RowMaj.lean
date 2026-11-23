import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.HatMaj
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.EmbPiInjective

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_nonneg' {F : Type} [Field F] [NumberField F]
    (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : 0 ≤ wt K N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

theorem UpperTheory.ConvolutionTheory.R2.Ff.rowMaj :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), RowMaj W := by
  intro F E _ _ _ _ _ _ _ D W φ hφ y hy c hc
  obtain ⟨K, hK, hBK⟩ := hatMaj F E D W φ hφ y hy
  obtain ⟨N, hN⟩ := wtSum F
  obtain ⟨C, hC⟩ := hN K hK c hc
  obtain ⟨B, hB⟩ := hBK N
  refine ⟨|B| * C, fun b a k hk hca => ?_⟩
  obtain ⟨hs, hle⟩ := hC a hca
  have hab : 0 < ab a := (IdeleGroup.ideleModule F a).2
  let ι : (Fin 2 → F) → (Fin 4 → F) := fun ξ => ![0, 0, ξ 0, ξ 1]
  have hι : Function.Injective ι := by
    intro ξ ξ' h
    funext i
    fin_cases i
    · exact congrFun h 2
    · exact congrFun h 3
  have hpt : ∀ ξ : Fin 2 → F,
      (![0, ((a⁻¹ : (A F)ˣ) : A F) * 0, a * rt (ξ 0), a * rt (ξ 1)] : V4 F) = sc a (ι ξ) := by
    intro ξ
    funext i
    fin_cases i <;> simp [sc, ι]
  have hterm : ∀ ξ : Fin 2 → F,
      ‖hat (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 0, rt (ξ 0), rt (ξ 1)]‖ ≤
        |B| * ab a * wt K N (sc a (ι ξ)) := by
    intro ξ
    have h := hB b a k hk 0 (rt (ξ 0)) (rt (ξ 1))
    rw [hpt] at h
    refine h.trans ?_
    have hw := wt_nonneg' K N (sc a (ι ξ))
    have : B ≤ |B| := le_abs_self B
    gcongr
  have hsι : Summable fun ξ : Fin 2 → F => wt K N (sc a (ι ξ)) := hs.comp_injective hι
  have hsn : Summable fun ξ : Fin 2 → F =>
      ‖hat (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 0, rt (ξ 0), rt (ξ 1)]‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hsι.mul_left _)
  have hsum : ∑' ξ : Fin 2 → F, wt K N (sc a (ι ξ)) ≤ C :=
    (Summable.tsum_le_tsum_of_inj ι hι (fun _ _ => wt_nonneg' K N _) (fun _ => le_rfl) hsι hs).trans hle
  unfold ThRow
  calc ‖∑' ξ : Fin 2 → F, hat (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 0, rt (ξ 0), rt (ξ 1)]‖
      ≤ ∑' ξ : Fin 2 → F, ‖hat (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 0, rt (ξ 0), rt (ξ 1)]‖ :=
        norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' ξ : Fin 2 → F, |B| * ab a * wt K N (sc a (ι ξ)) :=
        Summable.tsum_le_tsum hterm hsn (hsι.mul_left _)
    _ = |B| * ab a * ∑' ξ : Fin 2 → F, wt K N (sc a (ι ξ)) := tsum_mul_left
    _ ≤ |B| * ab a * C := by gcongr
    _ = |B| * C * ab a := by ring
