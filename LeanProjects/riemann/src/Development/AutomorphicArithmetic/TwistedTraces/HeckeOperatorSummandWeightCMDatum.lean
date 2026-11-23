import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InnerOps
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.EigenLatticeOffDiagonal

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

private theorem comm_prj {V : Submodule ℂ (LL μ)} (hV : IsClosed (V : Set (LL μ))) (R : LL μ →L[ℂ] LL μ)
    (hR : Commute (prj V) R) (v : LL μ) (hv : v ∈ V) : R v ∈ V := by
  have hself : ∀ x ∈ V, prj V x = x := fun x hx =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hx)
  have h := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) hR.eq
  simp only [ContinuousLinearMap.mul_apply, hself v hv] at h
  rw [← h]
  exact hV.submodule_topologicalClosure_eq.le (Submodule.starProjection_apply_mem V.topologicalClosure (R v))

end Ops

section Ty
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {n : ℕ} {q : Pl F} {w₀ : PlacesOver E q} (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]

private theorem mem_offN (T : Ty σ n q w₀) {v : LL μ} :
    v ∈ offN μ T ↔ ∀ w, w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) → ∀ x ∈ T.J w, rhoL μ w x v = T.χ w x • v := by
  simp only [offN, Submodule.mem_iInf, mem_eigL]

private theorem off_step (T : Ty σ n q w₀) (Bo : LL μ →L[ℂ] LL μ) (w₁ : Pl E)
    (hfix : ∀ v, Bo v ∈ fixL μ w₁ (T.J w₁)) (hχ : T.χ w₁ = 1)
    (hc : ∀ w, w ≠ w₁ → ∀ g, Commute Bo (rhoL μ w g)) (v : LL μ) (hv : v ∈ offN μ T) : Bo v ∈ offN μ T := by
  rw [mem_offN] at hv ⊢
  intro w hw x hx
  by_cases h : w = w₁
  · subst h
    have hch : IsChr (T.J w) 1 := hχ ▸ T.chr w
    have h1 := (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) 1 (T.co w) hch).2.1
    have h2 : Bo v ∈ eigL μ w (T.J w) 1 := by rw [h1]; exact hfix v
    rw [hχ]
    exact (mem_eigL μ).1 h2 x hx
  · have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hc w h x).eq
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [← this, hv w hw x hx, map_smul]

end Ty

end UpperTheory.EigenLatticeOffDiagonal

open UpperTheory.EigenLatticeOffDiagonal in
theorem UpperTheory.heckeOperator_summand_weight_CMDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (q : Pl F) (w₀ : PlacesOver E q),
        GM.Split E q → ∀ (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ (e : Fin n → ℤ) (j r : ℕ) (p : Fin r → Pl F),
        (∀ i, p i ∈ T.sp) → ∀ [∀ u : Pl E, MeasurableSpace (Gw n u)] [∀ u : Pl E, BorelSpace (Gw n u)]
          (mm : ∀ u : Pl E, Measure (Gw n u)), (∀ u, (mm u).IsHaarMeasure ∧ mm u (T.J u) = 1) →
        ∀ (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), (∀ i, Test (ψ (p i)) ∧ ∀ u ∈ T.J (T.mk' (p i)).1, ∀ g, ψ (p i) (u * g) = ψ (p i) g) →
        ∀ B : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (B i)) →
          (∀ g, Commute ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) (rightRegularRep (rationalGLOne E n) μ (archP E n g))) ∧
          (∀ w ∉ T.marked, ∀ g, Commute ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) (rhoL μ w g)) ∧
          (∀ f ∈ offN μ T, ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) f ∈ offN μ T) ∧
          (∀ f ∈ V, ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) f ∈ V) := by
  intro F E _ _ _ _ _ σ n μ _ q w₀ hq T V hV e j r p hp _ _ mm hmm ψ hψ B hBo
  have hVc : IsClosed (V : Set (LL μ)) := IsSummandOf.closed hV
  have hVrho : ∀ (w : Pl E) (g : Gw n w), Commute (prj V) (rhoL μ w g) := fun w g =>
    ((UpperTheory.ConvolutionTheory.Tf.innerOps E n μ).2.2.2.1 _ V hVc (IsSummandOf.inv hV)).symm
  let Good : (LL μ →L[ℂ] LL μ) → Prop := fun O => (∀ v ∈ offN μ T, O v ∈ offN μ T) ∧
    (∀ g, Commute O (rightRegularRep (rationalGLOne E n) μ (archP E n g))) ∧
    (∀ w ∉ T.marked, ∀ g, Commute O (rhoL μ w g)) ∧ (∀ v ∈ V, O v ∈ V)
  have hGone : Good 1 := ⟨fun v hv => hv, fun g => Commute.one_left _, fun w _ g => Commute.one_left _, fun v hv => hv⟩
  have hGmul : ∀ O₁ O₂, Good O₁ → Good O₂ → Good (O₁ * O₂) := fun O₁ O₂ h₁ h₂ =>
    ⟨fun v hv => h₁.1 _ (h₂.1 v hv), fun g => (h₁.2.1 g).mul_left (h₂.2.1 g),
      fun w hw g => (h₁.2.2.1 w hw g).mul_left (h₂.2.2.1 w hw g), fun v hv => h₁.2.2.2 _ (h₂.2.2.2 v hv)⟩
  have hBG : Good (List.ofFn B).prod := by
    refine List.prod_induction _ hGmul hGone fun O hO => ?_
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hO
    haveI := (hmm (T.mk' (p i)).1).1
    have hsp : p i ∈ T.sp := hp i
    have hspl : GM.Split E (p i) := (Finset.mem_filter.1 hsp).2
    have ht := (hψ i).2
    have hne : ∀ w ∉ T.marked, w ≠ (T.mk' (p i)).1 := fun w hw h => hw (Or.inr ⟨p i, hsp, h⟩)
    refine ⟨off_step μ T (B i) _ (oloc_fix μ (hBo i) _ ht) (T.triv _ hspl _) (fun w hw g => ?_),
      fun g => ?_, fun w hw g => ?_, comm_prj μ hVc _ (oloc_comm μ (hBo i) _ fun g' => hVrho _ g')⟩
    · exact (oloc_comm μ (hBo i) _ fun g' => rhoL_comm μ hw g g').symm
    · exact (oloc_comm μ (hBo i) _ fun g' => arch_comm μ g _ g').symm
    · exact (oloc_comm μ (hBo i) _ fun g' => rhoL_comm μ (hne w hw) g g').symm
  have hUG : Good (Uiw μ w₀.1 e) := by
    have hI : T.J w₀.1 = GLnLocal.iwahori (w₀.1.adicCompletion E) n := T.at_q w₀
    have hco := T.co w₀.1
    rw [hI] at hco
    have hh := UpperTheory.ConvolutionTheory.Tf.hopBasic E n μ w₀.1 (GLnLocal.iwahori _ n) (Cartan.diagPow _ n e) hco.2 hco.1
    have hne : ∀ w ∉ T.marked, w ≠ w₀.1 := fun w hw h => hw (Or.inl h)
    refine ⟨off_step μ T _ w₀.1 (fun v => ?_) (T.triv q hq w₀) (fun w hw g => ?_), fun g => ?_, fun w hw g => ?_,
      comm_prj μ hVc _ (hh.2.2.2.2.1 _ fun g' => hVrho _ g')⟩
    · rw [hI]; exact hh.2.1 v
    · exact (hh.2.2.2.2.1 _ fun g' => rhoL_comm μ hw g g').symm
    · exact (hh.2.2.2.2.1 _ fun g' => arch_comm μ g _ g').symm
    · exact (hh.2.2.2.2.1 _ fun g' => rhoL_comm μ (hne w hw) g g').symm
  have hUjG : Good (Uiw μ w₀.1 e ^ j) := by
    induction j with
    | zero => simpa using hGone
    | succ k ih => rw [pow_succ]; exact hGmul _ _ ih hUG
  have hCG : Good ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) := hGmul _ _ hUjG hBG
  exact ⟨hCG.2.1, hCG.2.2.1, hCG.1, hCG.2.2.2⟩
