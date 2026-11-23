import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RapidDecay
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandsSpan
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ClsBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

noncomputable section

namespace UpperTheory.ConvolutionTheory.BW

private theorem proj_comm {G H : Type*} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : UnitaryRep G H) (X : Submodule ℂ H) [X.HasOrthogonalProjection] (g : G)
    (h1 : ∀ x ∈ X, π g x ∈ X) (h2 : ∀ x ∈ X, π g⁻¹ x ∈ X) (v : H) :
    X.starProjection (π g v) = π g (X.starProjection v) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (h1 _ (X.starProjection_apply_mem v)) fun w hw => ?_
  rw [← map_sub, UnitaryRep.inner_map_left]
  exact Submodule.inner_left_of_mem_orthogonal (h2 w hw) (X.sub_starProjection_mem_orthogonal v)

private theorem exists_proj {G H K : Type*} [Group G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Group K] (R : UnitaryRep G H) (ι : K →* G) {a v : H}
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => R (ι k) a))) (hi : inner ℂ v a ≠ 0) :
    ∃ p ∈ Submodule.span ℂ (Set.range fun k => R (ι k) a), inner ℂ p v ≠ 0 ∧ ∀ x : K →₀ ℂ,
      Finsupp.linearCombination ℂ (fun k => R (ι k) v) x = 0 → Finsupp.linearCombination ℂ (fun k => R (ι k) p) x = 0 := by
  set X : Submodule ℂ H := Submodule.span ℂ (Set.range fun k => R (ι k) a) with hX
  have hinv : ∀ k, ∀ x ∈ X, R (ι k) x ∈ X := fun k x hx => by
    have : X ≤ X.comap (R (ι k)).toLinearMap := Submodule.span_le.2 (by
      rintro _ ⟨l, rfl⟩
      refine Submodule.subset_span ⟨k * l, ?_⟩
      simp only [map_mul, UnitaryRep.map_mul_apply]
      rfl)
    exact this hx
  have hmem : a ∈ X := Submodule.subset_span ⟨1, by simp only [map_one, UnitaryRep.map_one_apply]⟩
  refine ⟨_, X.starProjection_apply_mem v, fun hz => hi ?_, fun x hx => ?_⟩
  · have h1 := Submodule.inner_right_of_mem_orthogonal (X.starProjection_apply_mem v)
      (X.sub_starProjection_mem_orthogonal v)
    rw [inner_sub_right, hz, zero_sub, neg_eq_zero, inner_self_eq_zero] at h1
    have h2 := X.sub_starProjection_mem_orthogonal v
    rw [h1, sub_zero] at h2
    exact Submodule.inner_left_of_mem_orthogonal hmem h2
  · have h2 := congrArg X.starProjection.toLinearMap hx
    rw [map_zero, Finsupp.apply_linearCombination] at h2
    rw [← h2]
    congr 2
    funext k
    exact (proj_comm R X _ (hinv k) (by rw [← map_inv]; exact hinv _) v).symm

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private def k1 : KA E n →* normOneGL E n := Subgroup.inclusion maxCompact_le_normOneGL

private def trK (k : KA E n) (φ : cuspForms E n) : cuspForms E n :=
  ⟨rightTranslate (k : AdelicGLn.AdelicGL E n) φ.1, φ.2.1.rightTranslate_of_mem_maxCompact k.2, φ.2.2.translate _⟩

variable (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]

private theorem cls_trK (k : KA E n) (φ : cuspForms E n) :
    clsL μ (trK k φ) = rightRegularRep (rationalGLOne E n) μ (k1 k) (clsL μ φ) :=
  congrArg Subtype.val (cuspToL2_rightTranslate μ (k1 k) φ (trK k φ) rfl)

private theorem trK_mem {V : Submodule ℂ (LL μ)} (hV : IsSummand μ V) (k : KA E n) {φ : cuspForms E n}
    (h : φ ∈ formsIn μ V) : trK k φ ∈ formsIn μ V := by
  refine ⟨fun s x => ?_, ?_⟩
  · change φ.1 (centralSection E n s * x * k) = φ.1 (x * k)
    rw [mul_assoc]
    exact h.1 s _
  · change clsL μ (trK k φ) ∈ V
    rw [cls_trK]
    exact hV.inv _ _ h.2

private theorem exists_form0 {v : LL μ} (hv : v ∈ cuspidalL2 μ) (h0 : v ≠ 0) :
    ∃ V, IsSummand μ V ∧ ∃ f ∈ formsIn μ V, inner ℂ v (clsL μ f) ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : (⨆ V : {V // IsSummand μ V}, V.1) ≤ (ℂ ∙ v)ᗮ := iSup_le fun V => by
    rw [← (formsIrr E n μ V.1 V.2).2.2.2]
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rintro _ ⟨f, hf, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hc _ V.2 f hf)
  have h2 := Submodule.topologicalClosure_minimal _ h1 (Submodule.isClosed_orthogonal _)
  rw [summandsSpan E n μ] at h2
  exact h0 (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (h2 hv)))

private theorem fin_span (f₀ : cuspForms E n) : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KA E n =>
    rightRegularRep (rationalGLOne E n) μ (k1 k) (clsL μ f₀))) := by
  have := finiteDimensional_span_cuspRep_maxCompact μ f₀
  have e : Submodule.span ℂ (Set.range fun k : KA E n =>
      rightRegularRep (rationalGLOne E n) μ (k1 k) (clsL μ f₀)) = (Submodule.span ℂ (Set.range fun k : KA E n =>
      cuspRep μ ⟨k, maxCompact_le_normOneGL k.2⟩ (cuspToL2 μ f₀))).map (cuspidalL2 μ).subtype := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [e]
  infer_instance

private theorem comb_zero {f : cuspForms E n} (hf : ∀ k : KA E n, trK k f ∈ centralCuspForms E n) (x : KA E n →₀ ℂ)
    (hx : Finsupp.linearCombination ℂ (fun k => rightRegularRep (rationalGLOne E n) μ (k1 k) (clsL μ f)) x = 0)
    (g : AdelicGLn.AdelicGL E n) : (x.sum fun k c => c * f.1 (g * k)) = 0 := by
  have h1 : clsL μ (Finsupp.linearCombination ℂ (fun k => trK k f) x) = 0 := by
    have e : (clsL μ ∘ fun k => trK k f) = fun k => rightRegularRep (rationalGLOne E n) μ (k1 k) (clsL μ f) :=
      funext fun k => cls_trK μ k f
    rw [Finsupp.apply_linearCombination, e, hx]
  have h3 : Finsupp.linearCombination ℂ (fun k => trK k f) x ∈ centralCuspForms E n :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hf k)
  have h4 := congrArg ((LinearMap.proj g : (AdelicGLn.AdelicGL E n → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (cuspForms E n).subtype)
    ((clsBasic E n μ).1 _ h3 h1)
  rw [map_zero, Finsupp.apply_linearCombination] at h4
  exact h4

private theorem exists_form {v : LL μ} (hv : v ∈ cuspidalL2 μ) (h0 : v ≠ 0) :
    ∃ V, IsSummand μ V ∧ ∃ f ∈ formsIn μ V, inner ℂ (clsL μ f) v ≠ 0 ∧ ∀ x : KA E n →₀ ℂ,
      Finsupp.linearCombination ℂ (fun k => rightRegularRep (rationalGLOne E n) μ (k1 k) v) x = 0 →
      ∀ g, (x.sum fun k c => c * f.1 (g * k)) = 0 := by
  obtain ⟨V, hV, f₀, hf₀, hi⟩ := exists_form0 μ hv h0
  obtain ⟨p, hp, h1, h2⟩ := exists_proj _ k1 (fin_span μ f₀) hi
  have hle : Submodule.span ℂ (Set.range fun k : KA E n =>
      rightRegularRep (rationalGLOne E n) μ (k1 k) (clsL μ f₀)) ≤ (formsIn μ V).map (clsL μ) := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, trK_mem μ hV k hf₀, cls_trK μ k f₀⟩)
  obtain ⟨f, hf, rfl⟩ := hle hp
  exact ⟨V, hV, f, hf, h1, fun x hx => comb_zero μ (fun k => (trK_mem μ hV k hf).1) x (h2 x hx)⟩

private theorem ae_comb {ψ : AdelicGLn.AdelicGL E n → ℂ} (hψ : IsLeftInvariant ψ) {v : LL μ}
    (hv : v =ᵐ[quotientMeasure (rationalGLOne E n) μ] cuspQuot hψ) (x : KA E n →₀ ℂ) :
    Finsupp.linearCombination ℂ (fun k => rightRegularRep (rationalGLOne E n) μ (k1 k) v) x
      =ᵐ[quotientMeasure (rationalGLOne E n) μ]
        fun q => Finsupp.linearCombination ℂ (fun k => cuspQuot hψ (rightMul _ (k1 k) q)) x := by
  induction x using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero]
    exact Lp.coeFn_zero _ _ _
  | add x y hx hy =>
    simp only [map_add]
    exact (Lp.coeFn_add _ _).trans (hx.add hy)
  | single k c =>
    simp only [Finsupp.linearCombination_single]
    have h1 := (measurePreserving_rightMul μ (k1 k)).quasiMeasurePreserving.ae_eq hv
    filter_upwards [Lp.coeFn_smul c (rightRegularRep (rationalGLOne E n) μ (k1 k) v),
      coeFn_rightRegularRep (rationalGLOne E n) μ (k1 k) v, h1] with q e1 e2 e3
    rw [e1, Pi.smul_apply, e2]
    exact congrArg _ e3

private theorem exists_form' {ψ : AdelicGLn.AdelicGL E n → ℂ} (hψ : IsLeftInvariant ψ) (hc : Continuous ψ)
    (hb : ∃ C : ℝ, ∀ x : normOneGL E n, ‖ψ x‖ ≤ C) (hcu : Cusp ψ) (h0 : ∃ x : normOneGL E n, ψ x ≠ 0) :
    ∃ V, IsSummand μ V ∧ ∃ f ∈ formsIn μ V,
      ∫ y, ψ (Quotient.out y : normOneGL E n) * starRingEnd ℂ (f.1 (Quotient.out y : normOneGL E n))
        ∂quotientMeasure (rationalGLOne E n) μ ≠ 0 ∧ ∀ x : KA E n →₀ ℂ,
      (∀ g, (x.sum fun k c => c * ψ (g * k)) = 0) → ∀ g, (x.sum fun k c => c * f.1 (g * k)) = 0 := by
  have := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
  obtain ⟨C, hC⟩ := hb
  have hm : MemLp (cuspQuot hψ) 2 (quotientMeasure (rationalGLOne E n) μ) := by
    refine MemLp.of_bound (continuous_cuspQuot _ hc).aestronglyMeasurable C (Filter.Eventually.of_forall fun q => ?_)
    obtain ⟨y, rfl⟩ := mk_surjective _ q
    exact hC y
  have hv : hm.toLp _ ∈ cuspidalL2 μ := by
    intro r hr hrn
    filter_upwards [ae_ctFun_congr μ r (MemLp.coeFn_toLp hm)] with y hy
    rw [constantTermL2, hy]
    exact hcu r hr hrn y
  have hv0 : hm.toLp _ ≠ 0 := fun h => by
    obtain ⟨x, hx⟩ := h0
    have h1 : cuspQuot hψ =ᵐ[quotientMeasure (rationalGLOne E n) μ] 0 := by
      refine (MemLp.coeFn_toLp hm).symm.trans ?_
      rw [h]
      exact Lp.coeFn_zero _ _ _
    have h2 : (fun y : normOneGL E n => ψ y) =ᵐ[μ] 0 := (quasiMeasurePreserving_mk _ μ).ae_eq h1
    exact hx (congrFun ((Continuous.ae_eq_iff_eq μ (hc.comp continuous_subtype_val) continuous_const).1 h2) x)
  obtain ⟨V, hV, f, hf, hi, hk⟩ := exists_form μ hv hv0
  refine ⟨V, hV, f, hf, fun hz => hi ?_, fun x hx => hk x ?_⟩
  · rw [L2.inner_def, ← hz]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hm, (clsBasic E n μ).2.2.2 f hf.1] with q e1 e2
    rw [e1, e2, RCLike.inner_apply]
    congr 1
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  · refine Lp.ext ((ae_comb μ hψ (MemLp.coeFn_toLp hm) x).trans (Filter.EventuallyEq.trans ?_ (Lp.coeFn_zero _ _ _).symm))
    refine Filter.Eventually.of_forall fun q => ?_
    obtain ⟨y, rfl⟩ := mk_surjective _ q
    exact hx y

open GlobalTheory.CuspRep in
private theorem loc_mem (w : Pl E) {k : GL (Fin n) (w.adicCompletion E)} (hk : k ∈ GlobalTheory.LFun.KGL w n) :
    finGL E n (locGL E n w k) ∈ KA E n := by
  rw [← Fb.finEmb_eq]
  refine finEmb_mem_maxCompact ?_
  have h : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (locGL E n w k) ∈ GlobalTheory.LFun.KGL v n := fun v => by
    by_cases h : v = w
    · subst h; rw [pLoc_locGL]; exact hk
    · rw [pLoc_locGL_of_ne h]; exact one_mem _
  refine (AdelicGLn.mem_integralFiniteGL_iff E n).2 ⟨fun i j v => ?_, fun i j v => ?_⟩
  · exact (GlobalTheory.AdelicU.mem_GLint_iff.1 (h v)).1 i j
  · have := (GlobalTheory.AdelicU.mem_GLint_iff.1 (h v)).2 i j
    rw [← map_inv] at this
    exact this

private theorem exists_fin {r : ℕ} (m : Multiset ℂ) (h : m.card = r) :
    ∃ Λ : Fin r → ℂ, ∀ u, (m.map (u + ·)).prod = ∏ i, (u + Λ i) := by
  induction m using Quotient.inductionOn with
  | h l =>
    obtain rfl : l.length = r := h
    refine ⟨l.get, fun u => ?_⟩
    rw [← List.prod_ofFn]
    conv_lhs => rw [← List.ofFn_get l]
    simp [List.map_ofFn, Function.comp_def]

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW GlobalTheory.CuspRep in
theorem UpperTheory.ConvolutionTheory.BW.eigComp :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.EigComp E := by
  intro E _ _ _ S r ρ ψ hr hu hc hk hs h0
  obtain ⟨V, hV, f, hf, hi, hx⟩ := exists_form' (mu1 E r) hu.left ((umgOps E r).2 ψ hu).1
    (by simpa using rapidDecay E r ψ hu hc 0) hc h0
  obtain ⟨π, hπ, -⟩ := exCusp E r (mu1 E r) V hV
  have hfπ : Cm.ofCusp E r f ∈ π.V := Cm.mem_carrier.1 (hπ.carrier_eq ▸ hf)
  have hne : Cm.ofCusp E r f ≠ 0 := fun h => hi (by
    have : f.1 = 0 := congrArg Subtype.val h
    simp [this])
  have hinf : ∀ τ, ∃ Λ : Fin r → ℂ, ∀ u, cap τ u (Cm.ofCusp E r f) = (∏ i, (u + Λ i)) • Cm.ofCusp E r f := fun τ => by
    have hm : π.HasInfChar τ ((CG.mk π).infChar τ) :=
      hasInfChar_infChar_of_commute E r (fun τ u o => GlobalTheory.SpehInfChar.cap_commute_act τ u o) (CG.mk π) τ
    obtain ⟨Λ, hΛ⟩ := exists_fin _ hm.1
    exact ⟨Λ, fun u => by rw [← hΛ]; exact hm.2 u _ hfπ⟩
  have hsat : ∀ w, ∃ B : Multiset ℂˣ, w ∉ S → GlobalTheory.LFun.IsSatVecGL w (rw r w) (Cm.ofCusp E r f) B := fun w => by
    by_cases hw : w ∈ S
    · exact ⟨0, fun h => absurd hw h⟩
    have hfix : (⟨_, hfπ⟩ : π.V) ∈ GlobalTheory.PRep.fixed (π.locRep w) (GlobalTheory.LFun.KGL w r) := by
      refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (Subtype.ext (funext fun g => ?_))
      have key : ∀ φ : GA E r → ℂ, ∀ g, ((Finsupp.single (⟨_, loc_mem w hk⟩ : KA E r) (1 : ℂ) +
          Finsupp.single 1 (-1)).sum fun k c => c * φ (g * k)) = φ (g * finGL E r (locGL E r w k)) - φ g := fun φ g => by
        rw [Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_mul _ _ _)]
        rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
        simp [sub_eq_add_neg]
      have h1 := hx _ (fun g => (key ψ.1 g).trans (sub_eq_zero.2 (congrFun (congrArg Subtype.val (hs w hw k hk)) g))) g
      exact sub_eq_zero.1 ((key f.1 g).symm.trans h1)
    have hne' : (⟨_, hfπ⟩ : π.V) ≠ 0 := fun h => hne (congrArg Subtype.val h)
    obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_locRep π w ((Submodule.ne_bot_iff _).2 ⟨_, hfix, hne'⟩)
    exact ⟨B, fun _ => (hB.2 _ hfix hne').map π.V.subtype (fun _ _ => rfl) hne⟩
  choose Λ hΛ using hinf
  choose B hB using hsat
  exact ⟨⟨hr, Cm.ofCusp E r f, hne, f.2, fun t g => hf.1 _ g, ⟨V, hV, hf.2⟩, Λ, hΛ, B, hB⟩,
    fun x h => hx x (hk x h), hi⟩
