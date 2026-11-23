import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistY
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactorAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ZBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistPerm
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InnerOps
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.CommProj
import Development.AutomorphicArithmetic.LyingOver.TypedVectorsLeFixedOfFitsLevel
import Development.AutomorphicArithmetic.LyingOver.ExistsPosConstTypedTestFunctionBound
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.L1
open scoped ComplexConjugate Classical InnerProductSpace
namespace UpperTheory.ConvolutionTheory.L1.SideTr

section Hil
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem prj_mem_cl {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : v ∈ V.topologicalClosure ↔ v ∈ V := by
  rw [hV.submodule_topologicalClosure_eq]

private theorem prj_mem {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v ∈ V :=
  (prj_mem_cl hV _).1 (Submodule.starProjection_apply_mem _ v)

private theorem prj_self {V : Submodule ℂ H} {v : H} (hv : v ∈ V) : prj V v = v :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hv)

private theorem prj_adj (V : Submodule ℂ H) : ContinuousLinearMap.adjoint (prj V) = prj V :=
  (isSelfAdjoint_starProjection _).adjoint_eq

private theorem prj_comm {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H)
    (hT : ContinuousLinearMap.adjoint T = T) (h : ∀ v ∈ V, T v ∈ V) : T * prj V = prj V * T := by
  refine ContinuousLinearMap.ext fun v => ?_
  show T (prj V v) = prj V (T v)
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((prj_mem_cl hV _).2 (h _ (prj_mem hV v))) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right, hT]
  exact Submodule.starProjection_inner_eq_zero v _ ((prj_mem_cl hV _).2 (h w ((prj_mem_cl hV _).1 hw)))

private theorem eigIn_closed {W : Submodule ℂ H} (hW : IsClosed (W : Set H)) (A : H →L[ℂ] H) (x : ℝ) :
    IsClosed (eigIn W A x : Set H) := by
  have : (eigIn W A x : Set H) = (W : Set H) ∩ {v | A v = (x : ℂ) • v} := by
    ext v
    simp [eigIn, Module.End.mem_eigenspace_iff]
  rw [this]
  exact hW.inter (isClosed_eq A.continuous (continuous_const_smul _))

private theorem mem_eigIn {W : Submodule ℂ H} {A : H →L[ℂ] H} {x : ℝ} {v : H} :
    v ∈ eigIn W A x ↔ v ∈ W ∧ A v = (x : ℂ) • v := by
  simp [eigIn, Module.End.mem_eigenspace_iff]

private theorem prj_inf {P X : Submodule ℂ H} (hP : IsClosed (P : Set H)) (hX : IsClosed (X : Set H))
    (h : ∀ v ∈ X, prj P v ∈ X) : prj X * prj P = prj (X ⊓ P) ∧ prj P * prj X = prj (X ⊓ P) := by
  have hc := prj_comm hX (prj P) (prj_adj P) h
  have hXP : IsClosed ((X ⊓ P : Submodule ℂ H) : Set H) := by
    rw [Submodule.coe_inf]; exact hX.inter hP
  have key : prj X * prj P = prj (X ⊓ P) := by
    refine ContinuousLinearMap.ext fun v => ?_
    show prj X (prj P v) = (X ⊓ P).topologicalClosure.starProjection v
    symm
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
    · refine (prj_mem_cl hXP _).2 ⟨prj_mem hX _, ?_⟩
      have := congrArg (fun S : H →L[ℂ] H => S v) hc
      simp only [ContinuousLinearMap.mul_apply] at this
      rw [← this]
      exact prj_mem hP _
    · have hw' := (prj_mem_cl hXP _).1 hw
      have hs : ∀ (Q : Submodule ℂ H) (a b : H), ⟪prj Q a, b⟫_ℂ = ⟪a, prj Q b⟫_ℂ := fun Q a b => by
        rw [← ContinuousLinearMap.adjoint_inner_right, prj_adj]
      rw [inner_sub_left, hs, hs, prj_self hw'.1, prj_self hw'.2, sub_self]
  exact ⟨key, hc.trans key⟩

private theorem core (Ty Fx V : Submodule ℂ H) (hTy : IsClosed (Ty : Set H)) (hFx : IsClosed (Fx : Set H))
    (hV : IsClosed (V : Set H)) (hle : Ty ≤ Fx) (Oa : H →L[ℂ] H) (hOa : ContinuousLinearMap.adjoint Oa = Oa)
    (hOT : ∀ v ∈ Ty, Oa v ∈ Ty) (hOF : ∀ v ∈ Fx, Oa v ∈ Fx) (hVT : ∀ v ∈ Ty, prj V v ∈ Ty) (x : ℝ) :
    prj (eigIn V (Oa ∘L prj Fx) x) * prj Ty = prj (eigIn (V ⊓ Ty) Oa x) ∧
    prj Ty * prj (eigIn V (Oa ∘L prj Fx) x) = prj (eigIn (V ⊓ Ty) Oa x) ∧
    prj (eigIn V (Oa ∘L prj Fx) x) * (Oa ∘L prj Fx) = (x : ℂ) • prj (eigIn V (Oa ∘L prj Fx) x) := by
  set A := Oa ∘L prj Fx with hA
  set X := eigIn V A x with hXd
  have hXc : IsClosed (X : Set H) := eigIn_closed hV A x
  have hOP : Oa * prj Ty = prj Ty * Oa := prj_comm hTy Oa hOa hOT
  have hOFx : Oa * prj Fx = prj Fx * Oa := prj_comm hFx Oa hOa hOF
  have hVP : prj V * prj Ty = prj Ty * prj V := prj_comm hTy (prj V) (prj_adj V) hVT
  have hFP : prj Fx * prj Ty = prj Ty := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact prj_self (hle (prj_mem hTy v))
  have hPF : prj Ty * prj Fx = prj Ty :=
    (prj_comm hFx (prj Ty) (prj_adj Ty) fun v _ => hle (prj_mem hTy v)).trans hFP
  have hAP : A * prj Ty = prj Ty * A := by
    show Oa * prj Fx * prj Ty = prj Ty * (Oa * prj Fx)
    rw [mul_assoc, hFP, hOP, ← mul_assoc, ← hOP, mul_assoc, hPF, hOP]
  have hAadj : star A = A := by
    show star (Oa * prj Fx) = Oa * prj Fx
    rw [star_mul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint, hOa, prj_adj, hOFx]
  have heq : X ⊓ Ty = eigIn (V ⊓ Ty) Oa x := by
    ext v
    simp only [Submodule.mem_inf, mem_eigIn, hXd]
    have hA1 : v ∈ Ty → A v = Oa v := fun hv => by
      show Oa (prj Fx v) = Oa v
      rw [prj_self (hle hv)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, by rwa [← hA1 h3]⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨⟨h1, by rwa [hA1 h3]⟩, h3⟩
  have hPX : ∀ v ∈ X, prj Ty v ∈ X := by
    intro v hv
    obtain ⟨h1, h2⟩ := mem_eigIn.1 hv
    refine mem_eigIn.2 ⟨?_, ?_⟩
    · have := congrArg (fun S : H →L[ℂ] H => S v) hVP
      simp only [ContinuousLinearMap.mul_apply, prj_self h1] at this
      rw [← this]
      exact prj_mem hV _
    · have := congrArg (fun S : H →L[ℂ] H => S v) hAP
      simp only [ContinuousLinearMap.mul_apply] at this
      rw [this, h2, map_smul]
  obtain ⟨k1, k2⟩ := prj_inf hTy hXc hPX
  rw [heq] at k1 k2
  refine ⟨k1, k2, ?_⟩
  have hAX : A * prj X = (x : ℂ) • prj X := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact (mem_eigIn.1 (prj_mem hXc v)).2
  have hsX : star (prj X) = prj X := by
    rw [ContinuousLinearMap.star_eq_adjoint, prj_adj]
  have := congrArg star hAX
  rwa [star_mul, star_smul, hAadj, hsX, RCLike.star_def, Complex.conj_ofReal] at this

private theorem alg {R : Type} [Ring R] [Algebra ℂ R] (PX P PZ A Oa Ui Bp U : R) (k x : ℂ)
    (h1 : PX * P = PZ) (h2 : P * PX = PZ) (h3 : PX * A = x • PX) (h4 : Ui * A = A * Ui)
    (h5 : Oa * (Bp * P) = A * (Bp * P)) (h6 : (Ui * Bp) * P = P * ((Ui * Bp) * P)) (h7 : P * U = U * P) :
    PX * ((Ui * ((k • (Oa * (Bp * P))) * U)) * PX) = (k * x) • (PZ * (((Ui * Bp) * U) * PZ)) := by
  have e2 : PX * (Ui * Bp * P * U) * PX = PZ * (Ui * Bp * U * PZ) := by
    calc PX * (Ui * Bp * P * U) * PX = PX * (P * (Ui * Bp * P)) * U * PX := by
          rw [← h6]; simp only [mul_assoc]
      _ = PZ * (Ui * Bp) * (P * U) * PX := by rw [← h1]; simp only [mul_assoc]
      _ = PZ * (Ui * Bp) * U * (P * PX) := by rw [h7]; simp only [mul_assoc]
      _ = PZ * (Ui * Bp * U * PZ) := by rw [h2]; simp only [mul_assoc]
  have e1 : Ui * ((k • (Oa * (Bp * P))) * U) = k • (A * (Ui * Bp * P * U)) := by
    rw [h5, smul_mul_assoc, mul_smul_comm]
    congr 1
    simp only [← mul_assoc]
    rw [h4]
  rw [e1, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← mul_assoc, h3, smul_mul_assoc, smul_mul_assoc, smul_smul, ← e2,
    mul_assoc PX]

private theorem trace_sm (c : ℂ) (S : H →L[ℂ] H) : trace (c • S) = c * trace S := by
  simp only [trace, ContinuousLinearMap.smul_apply, inner_smul_right, tsum_mul_left]

end Hil

section Ops
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

private theorem rhoL_mul (w : Pl K) (g h : Gw n w) : rhoL μ w (g * h) = rhoL μ w g ∘L rhoL μ w h := by
  have := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  simp only [rhoL, map_mul, this]

private theorem rhoL_comm {w w' : Pl K} (h : w ≠ w') (g : Gw n w) (g' : Gw n w') : Commute (rhoL μ w g) (rhoL μ w' g') := by
  have h1 := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  have h2 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' h.symm g g'
  show rhoL μ w g ∘L rhoL μ w' g' = rhoL μ w' g' ∘L rhoL μ w g
  simp only [rhoL, ← h1, h2]

private theorem arch_comm (a : archGroup K n) (w : Pl K) (g : Gw n w) :
    Commute (rightRegularRep (rationalGLOne K n) μ (archP K n a)) (rhoL μ w g) := by
  show rightRegularRep (rationalGLOne K n) μ (archP K n a) * rightRegularRep (rationalGLOne K n) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) =
    rightRegularRep (rationalGLOne K n) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) * rightRegularRep (rationalGLOne K n) μ (archP K n a)
  rw [← UnitaryRep.map_mul, ← UnitaryRep.map_mul, archimedeanProjection_apply, MultiplicityOne.finProj_mul_archProj_comm]

private theorem oloc_comm {w : Pl K} [MeasurableSpace (Gw n w)] {m : Measure (Gw n w)} {ψ : Gw n w → ℂ}
    {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (R : LL μ →L[ℂ] LL μ) (hR : ∀ g, Commute R (rhoL μ w g)) :
    Commute R Bo := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  show ⟪u, R (Bo v)⟫_ℂ = ⟪u, Bo (R v)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left R, h, h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show ψ g * _ = ψ g * _
  congr 1
  rw [ContinuousLinearMap.adjoint_inner_left]
  have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hR g).eq
  simp only [ContinuousLinearMap.mul_apply] at this
  rw [this]

private theorem oloc_fix {w : Pl K} [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] {m : Measure (Gw n w)} [m.IsHaarMeasure]
    {ψ : Gw n w → ℂ} {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (J : Subgroup (Gw n w))
    (hJ : ∀ u ∈ J, ∀ g, ψ (u * g) = ψ g) (v : LL μ) : Bo v ∈ fixL μ w J := by
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 _).2 ?_
  rintro _ ⟨u, hu, rfl⟩
  refine ext_inner_left ℂ fun a => ?_
  show ⟪a, rhoL μ w u (Bo v)⟫_ℂ = ⟪a, Bo v⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left (rhoL μ w u), h, h,
    ← integral_mul_left_eq_self (μ := m) (fun g => ψ g * ⟪a, rhoL μ w g v⟫_ℂ) u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show ψ g * _ = ψ (u * g) * _
  rw [hJ u hu, rhoL_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

private theorem mem_eigL {w : Pl K} {J : Subgroup (Gw n w)} {χ : Gw n w → ℂ} {v : LL μ} :
    v ∈ eigL μ w J χ ↔ ∀ x ∈ J, rhoL μ w x v = χ x • v := by
  simp [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus]

end Ops

section Ty
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {n : ℕ} {q : Pl F} {w₀ : PlacesOver E q} (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]

private theorem mem_typed (T : Ty σ n q w₀) {v : LL μ} :
    v ∈ T.typed μ ↔ ∀ w, ∀ x ∈ T.J w, rhoL μ w x v = T.χ w x • v := by
  simp only [Ty.typed, Submodule.mem_iInf, mem_eigL]

private theorem typed_closed (T : Ty σ n q w₀) : IsClosed (T.typed μ : Set (LL μ)) := by
  simp only [Ty.typed, Submodule.coe_iInf]
  exact isClosed_iInter fun w => (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w _ _ (T.co w) (T.chr w)).1

private theorem comm_typed (T : Ty σ n q w₀) (R : LL μ →L[ℂ] LL μ) (hR : ∀ w g, Commute R (rhoL μ w g)) (v : LL μ)
    (hv : v ∈ T.typed μ) : R v ∈ T.typed μ := by
  rw [mem_typed] at hv ⊢
  intro w x hx
  have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hR w x).eq
  simp only [ContinuousLinearMap.mul_apply] at this
  rw [← this, hv w x hx, map_smul]

private theorem typed_step (T : Ty σ n q w₀) (Bo : LL μ →L[ℂ] LL μ) (w₁ : Pl E)
    (hfix : ∀ v, Bo v ∈ fixL μ w₁ (T.J w₁)) (hχ : T.χ w₁ = 1)
    (hc : ∀ w, w ≠ w₁ → ∀ g, Commute Bo (rhoL μ w g)) (v : LL μ) (hv : v ∈ T.typed μ) : Bo v ∈ T.typed μ := by
  rw [mem_typed] at hv ⊢
  intro w x hx
  by_cases h : w = w₁
  · subst h
    have hch : IsChr (T.J w) 1 := hχ ▸ T.chr w
    have h1 := (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) 1 (T.co w) hch).2.1
    have h2 : Bo v ∈ eigL μ w (T.J w) 1 := by rw [h1]; exact hfix v
    rw [hχ]
    exact (mem_eigL μ).1 h2 x hx
  · have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hc w h x).eq
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [← this, hv w x hx, map_smul]

end Ty

private theorem oinf_congr {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    {ν₁ ν₂ : Measure (archGroup K n)} [ν₁.IsHaarMeasure] [ν₂.IsHaarMeasure] (h : ν₁ = ν₂) (β : TI K n) :
    Oinf μ ν₁ β = Oinf μ ν₂ β := by
  subst h; rfl

end UpperTheory.ConvolutionTheory.L1.SideTr

set_option maxHeartbeats 1600000 in
open UpperTheory.ConvolutionTheory.L1.SideTr in
theorem UpperTheory.ConvolutionTheory.L1.sideTrace :
    UpperTheory.ConvolutionTheory.L1.SideTrace := by
  intro F E _ _ _ _ _ _ σ hσ m n hfr hn μ _ θ hθ D s hs hsl νE _ νF _ b a aE aF hA q w₀ hq T V hV hVU hR y hy
  obtain ⟨c₀, hc₀, hB⟩ := (UpperTheory.ConvolutionTheory.L1.twistY F E σ hσ m n hfr hn μ θ hθ D s hs hsl νE νF b a aE aF hA q w₀ hq T V hV hVU hR).2 y hy
  obtain ⟨κ, hκ, hK⟩ := UpperTheory.exists_pos_const_typed_test_function_bound F E σ n hn μ νE aE q w₀ hq T
  have hx : (0 : ℝ) < y ^ (m + 1) := pow_pos hy _
  refine ⟨(κ : ℂ) * ((y ^ (m + 1) : ℝ) : ℂ) * c₀, mul_ne_zero (mul_ne_zero (by exact_mod_cast hκ.ne') (by exact_mod_cast hx.ne')) hc₀, ?_⟩
  intro L ψ hF ν l 𝔢 hE r p hp hpr _ _ mm hmm B hBo j
  obtain ⟨hν, ha, -, hU, hg, hUq⟩ := hE
  have hKg := hK L ψ hF r p hp hpr mm hmm B hBo 𝔢.g hg
  have hle : T.typed μ ≤ fixF μ (GM.levE L.UE) := UpperTheory.typed_vectors_le_fixed_of_fits_level F E σ n q w₀ hq μ T L ψ hF
  have hcp := UpperTheory.ConvolutionTheory.Tf.commPrj E n μ (GM.levE L.UE)
  have hAeq : 𝔢.toAmp.A = Oinf μ νE aE ∘L prj (fixF μ (GM.levE L.UE)) := by
    show Oinf μ 𝔢.ν 𝔢.a₀ ∘L prj (fixF μ 𝔢.U) = _
    rw [ha, hU, oinf_congr μ hν]
  have hpos : 0 ≤ Oinf μ νE aE := by
    have := 𝔢.pos
    rwa [ha, oinf_congr μ hν] at this
  have hOsa : ContinuousLinearMap.adjoint (Oinf μ νE aE) = Oinf μ νE aE :=
    (IsSelfAdjoint.of_nonneg hpos).adjoint_eq
  have hOF : ∀ h, Commute (Oinf μ νE aE) (rhoF μ h) := fun h =>
    (UpperTheory.ConvolutionTheory.Tf.opAlg E n μ νE MeasureTheory.Measure.haar).2.2.2.2.2.2.2.2 aE h
  have hOT : ∀ v ∈ T.typed μ, Oinf μ νE aE v ∈ T.typed μ :=
    comm_typed μ T _ fun w g => hOF _
  have hOFx : ∀ v ∈ fixF μ (GM.levE L.UE), Oinf μ νE aE v ∈ fixF μ (GM.levE L.UE) := by
    intro v hv
    refine (hcp.2.1 _).2 fun u hu => ?_
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hOF u).eq
    simp only [ContinuousLinearMap.mul_apply, (hcp.2.1 v).1 hv u hu] at this
    exact this.symm
  have hVc : IsClosed (V : Set (LL μ)) := IsSummandOf.closed hV
  have hVT : ∀ v ∈ T.typed μ, prj V v ∈ T.typed μ := by
    refine comm_typed μ T _ fun w g => ?_
    exact ((UpperTheory.ConvolutionTheory.Tf.innerOps E n μ).2.2.2.1 _ V hVc (IsSummandOf.inv hV)).symm
  obtain ⟨k1, k2, k3⟩ := core (T.typed μ) (fixF μ (GM.levE L.UE)) V (typed_closed μ T) hcp.1 hVc hle (Oinf μ νE aE) hOsa hOT hOFx hVT (y ^ (m + 1))
  have hθP : Commute θ.U (prj (T.typed μ)) := by
    have h0 := (UpperTheory.ConvolutionTheory.L1.twistPerm F E σ hσ m n μ θ hθ).2.2 q w₀ T ∅
    have h1 : (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ (∅ : Set (Pl F))), eigL μ w (T.J w) (T.χ w)) = T.typed μ := by
      simp [Ty.typed]
    rwa [h1] at h0

  let Good : (LL μ →L[ℂ] LL μ) → Prop := fun O => (∀ v ∈ T.typed μ, O v ∈ T.typed μ) ∧
    (∀ g, Commute O (rightRegularRep (rationalGLOne E n) μ (archP E n g))) ∧ (∀ w ∉ T.marked, ∀ g, Commute O (rhoL μ w g))
  have hGone : Good 1 := ⟨fun v hv => hv, fun g => Commute.one_left _, fun w _ g => Commute.one_left _⟩
  have hGmul : ∀ O₁ O₂, Good O₁ → Good O₂ → Good (O₁ * O₂) := fun O₁ O₂ h₁ h₂ =>
    ⟨fun v hv => h₁.1 _ (h₂.1 v hv), fun g => (h₁.2.1 g).mul_left (h₂.2.1 g),
      fun w hw g => (h₁.2.2 w hw g).mul_left (h₂.2.2 w hw g)⟩
  have hBG : Good (List.ofFn B).prod := by
    refine List.prod_induction _ hGmul hGone fun O hO => ?_
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hO
    haveI := (hmm i).1
    have hsp : p i ∈ T.sp := (hpr _).2 ⟨i, rfl⟩
    have hspl : GM.Split E (p i) := (Finset.mem_filter.1 hsp).2
    have ht := (hF.test (p i) hsp).2
    have hne : ∀ w ∉ T.marked, w ≠ (T.mk' (p i)).1 := fun w hw h => hw (Or.inr ⟨p i, hsp, h⟩)
    refine ⟨typed_step μ T (B i) _ (oloc_fix μ (hBo i) _ fun u hu g => (ht u hu g).1) (T.triv _ hspl _) (fun w hw g => ?_),
      fun g => ?_, fun w hw g => ?_⟩
    · exact (oloc_comm μ (hBo i) _ fun g' => rhoL_comm μ hw g g').symm
    · exact (oloc_comm μ (hBo i) _ fun g' => arch_comm μ g _ g').symm
    · exact (oloc_comm μ (hBo i) _ fun g' => rhoL_comm μ (hne w hw) g g').symm
  have hUG : Good (Uiw μ w₀.1 ν) := by
    have hI : T.J w₀.1 = GLnLocal.iwahori (w₀.1.adicCompletion E) n := T.at_q w₀
    have hco := T.co w₀.1
    rw [hI] at hco
    have hh := UpperTheory.ConvolutionTheory.Tf.hopBasic E n μ w₀.1 (GLnLocal.iwahori _ n) (Cartan.diagPow _ n ν) hco.2 hco.1
    have hne : ∀ w ∉ T.marked, w ≠ w₀.1 := fun w hw h => hw (Or.inl h)
    refine ⟨typed_step μ T _ w₀.1 (fun v => ?_) (T.triv q hq w₀) (fun w hw g => ?_), fun g => ?_, fun w hw g => ?_⟩
    · rw [hI]; exact hh.2.1 v
    · exact (hh.2.2.2.2.1 _ fun g' => rhoL_comm μ hw g g').symm
    · exact (hh.2.2.2.2.1 _ fun g' => arch_comm μ g _ g').symm
    · exact (hh.2.2.2.2.1 _ fun g' => rhoL_comm μ (hne w hw) g g').symm
  have hUjG : Good (Uiw μ w₀.1 ν ^ j) := by
    induction j with
    | zero => simpa using hGone
    | succ k ih => rw [pow_succ]; exact hGmul _ _ ih hUG
  have hCG : Good (Uiw μ w₀.1 ν ^ j * (List.ofFn B).prod) := hGmul _ _ hUjG hBG
  have hal := alg (prj (eigIn V (Oinf μ νE aE ∘L prj (fixF μ (GM.levE L.UE))) (y ^ (m + 1)))) (prj (T.typed μ))
    (prj (eigIn (V ⊓ T.typed μ) (Oinf μ νE aE) (y ^ (m + 1)))) (Oinf μ νE aE ∘L prj (fixF μ (GM.levE L.UE))) (Oinf μ νE aE)
    (Uiw μ w₀.1 ν ^ j) (List.ofFn B).prod θ.U (κ : ℂ) ((y ^ (m + 1) : ℝ) : ℂ) k1 k2 k3
    (by
      have := ((𝔢.Uq_amp 0).pow_left j).eq
      rwa [hUq, hAeq] at this)
    (by
      refine ContinuousLinearMap.ext fun v => ?_
      show Oinf μ νE aE ((List.ofFn B).prod (prj (T.typed μ) v)) =
        Oinf μ νE aE (prj (fixF μ (GM.levE L.UE)) ((List.ofFn B).prod (prj (T.typed μ) v)))
      rw [prj_self (hle (hBG.1 _ (prj_mem (typed_closed μ T) v)))])
    (by
      refine ContinuousLinearMap.ext fun v => ?_
      exact (prj_self (hCG.1 _ (prj_mem (typed_closed μ T) v))).symm)
    hθP.eq.symm
  have hCG' : Good ((Uiw μ w₀.1 ν ^ j) ∘L (List.ofFn B).prod) := hCG
  have hfin := hB _ hCG'.2.1 hCG'.2.2
  have htr : trOn (eigIn V 𝔢.toAmp.A (y ^ (m + 1))) ((𝔢.Uq 0 ^ j) ∘L Rop μ 𝔢.g ∘L θ.U) =
      ((κ : ℂ) * ((y ^ (m + 1) : ℝ) : ℂ)) * trOn (eigIn (V ⊓ T.typed μ) (Oinf μ νE aE) (y ^ (m + 1)))
        (((Uiw μ w₀.1 ν ^ j) ∘L (List.ofFn B).prod) ∘L θ.U) := by
    unfold trOn
    rw [← trace_sm, hUq, hKg, hAeq]
    exact congrArg _ hal
  rw [htr, hfin]
  ring
