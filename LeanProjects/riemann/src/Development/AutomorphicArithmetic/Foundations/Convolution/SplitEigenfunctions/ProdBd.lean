import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SpanGrow
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AbLower
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SpanCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.LiftCentre
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt
import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Assemble
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical Pointwise

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem scal_eq {K : Type} [Field K] [NumberField K] (u : (A K)ˣ) :
    GroundTheory.Automorphic.Reduction.scalarUnits K 2 u = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  ext i j
  rw [GroundTheory.Automorphic.Reduction.scalarUnits_apply, GroundTheory.Automorphic.Reduction.coe_diagUnits]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]

private theorem norm_central (s : {r : ℝ // 0 < r}) :
    ∃ z : (A E)ˣ, GroundTheory.Automorphic.Reduction.centralSection E 2 s = Matrix.GeneralLinearGroup.scalar (Fin 2) z ∧
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleNorm ℚ E z) = GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s := by
  have hd : Module.finrank ℚ E ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : {r : ℝ // 0 < r}, s₀ ^ Module.finrank ℚ E = s := by
    refine ⟨⟨s.1 ^ ((Module.finrank ℚ E : ℝ))⁻¹, Real.rpow_pos_of_pos s.2 _⟩, Subtype.ext ?_⟩
    rw [Positive.val_pow]
    exact Real.rpow_inv_natCast_pow s.2.le hd
  obtain ⟨y, hy⟩ : ∃ y : (A ℚ)ˣ, GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s₀ = Matrix.GeneralLinearGroup.scalar (Fin 2) y :=
    ⟨_, (rfl : _ = GroundTheory.Automorphic.Reduction.scalarUnits ℚ 2 _).trans (scal_eq _)⟩
  refine ⟨ideleEmbedding ℚ E y, ?_, ?_⟩
  · rw [← hs₀, ← UpperTheory.centralSection_baseChange ℚ E 2 s₀, hy]
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]
  · rw [ideleNorm_ideleEmbedding, map_pow, ← hy, ← map_pow, hs₀]

end SlopeTestRemainingChoices

section Span

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {D : Dat ℚ E}

private theorem span_pos (W : Weil D) (M : Meas ℚ) (π : TR.CuspSub ℚ 2) (hπ : PosInv π) (s : {r : ℝ // 0 < r}) :
    ∀ Φ ∈ span W M π, ∀ g, Φ.1 (GroundTheory.Automorphic.Reduction.centralSection E 2 s * g) = Φ.1 g := by
  obtain ⟨z, hz, hn⟩ := norm_central (E := E) s
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen ℚ π
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Ψ h =>
    obtain ⟨f, hf, ph, hph, e⟩ := h
    intro g
    rw [e]
    by_cases h0 : ∀ x, f.1 x = 0
    · simp [lift, h0]
    · push_neg at h0
      obtain ⟨x, hx⟩ := h0
      have h1 : ((ω (ideleNorm ℚ E z) : ℂˣ) : ℂ) = 1 := by
        have h2 := hω f hf (ideleNorm ℚ E z) x
        rw [hn, hπ f hf s x] at h2
        exact mul_right_cancel₀ hx (by rw [one_mul]; exact h2.symm)
      rw [hz, (UpperTheory.ConvolutionTheory.R2.equiv ℚ E D W M π f hf ph).2 ω (hω f hf) z g, h1, one_mul]
  | zero => exact fun _ => rfl
  | add x y _ _ ix iy => exact fun g => congrArg₂ (· + ·) (ix g) (iy g)
  | smul c x _ ix => exact fun g => congrArg (c • ·) (ix g)

end Span

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.prodBd :
    ProdBd := by
  intro E _ _ _ D W M N P π Φ hΦ φ hφ
  have hS := UpperTheory.ConvolutionTheory.R2.H.spanCont ℚ E D W M π Φ hΦ
  obtain ⟨hL, -, hd⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.decE E P φ hφ
  refine ⟨⟨hS.1.mul hL.1, fun γ g => by rw [hS.2, hL.2], fun C hC => ?_⟩, fun hπ hP s g => ?_⟩
  · obtain ⟨c, C₀, hc, hC₀, hred⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.redE E
    have hC' : IsCompact ((gl (F := E) '' C₀) * C) := (hC₀.image continuous_gl).mul hC
    obtain ⟨r, B, hB⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.spanGrow E D W M N P π Φ hΦ _ hC' c hc
    obtain ⟨B', hB'⟩ := hd _ hC' c hc r
    refine ⟨B * B', fun h k hk => ?_⟩
    obtain ⟨γ, u, b, k₀, hk₀, hg, hb⟩ := hred h
    have e : ∀ f : GL (Fin 2) (A E) → ℂ, (∀ γ g, f (ratGL E 2 γ * g) = f g) →
        f (gl h * k) = f (gl (nU u * mD b) * (gl k₀ * k)) := fun f hf => by
      rw [← mul_assoc, ← gl_mul, ← hg, gl_mul, gl_ratS, mul_assoc, hf]
    have hm : gl k₀ * k ∈ (gl (F := E) '' C₀) * C := Set.mul_mem_mul ⟨k₀, hk₀, rfl⟩ hk
    have h1 := hB u b _ hm hb
    have h2 := hB' u b _ hm hb
    have hab : ab b ^ r * (ab b)⁻¹ ^ r = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (hc.trans_le hb).ne', one_pow]
    rw [e _ hS.2, e _ hL.2, norm_mul]
    calc _ ≤ (B * ab b ^ r) * (B' * (ab b)⁻¹ ^ r) :=
          mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = B * B' * (ab b ^ r * (ab b)⁻¹ ^ r) := by ring
      _ = B * B' := by rw [hab, mul_one]
  · obtain ⟨t, ht⟩ := UpperTheory.V.KernelIndexFullLattice.exists_split (E := E) (a := 2) UpperTheory.V.KernelIndexFullLattice.splitEq_holds s
    have h2 : φ.1 (GroundTheory.Automorphic.Reduction.centralSection E 2 s * g) = φ.1 g := by
      rw [ht]
      exact hP φ hφ t g
    show Φ.1 _ * φ.1 _ = Φ.1 g * φ.1 g
    rw [span_pos W M π hπ s Φ hΦ g, h2]
