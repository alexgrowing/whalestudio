import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

section Ops
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

private theorem rhoL_mul (w : Pl K) (g h : Gw n w) : rhoL μ w (g * h) = rhoL μ w g ∘L rhoL μ w h := by
  have := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  simp only [rhoL, map_mul, this]

private theorem rhoL_comm {w w' : Pl K} (h : w ≠ w') (g : Gw n w) (g' : Gw n w') :
    Commute (rhoL μ w g) (rhoL μ w' g') := by
  have h1 := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  have h2 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' h.symm g g'
  show rhoL μ w g ∘L rhoL μ w' g' = rhoL μ w' g' ∘L rhoL μ w g
  simp only [rhoL, ← h1, h2]

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

private theorem oloc_fix {w : Pl K} [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] {m : Measure (Gw n w)}
    [m.IsHaarMeasure] {ψ : Gw n w → ℂ} {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (J : Subgroup (Gw n w))
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

private theorem mem_fixL {w : Pl K} {J : Subgroup (Gw n w)} {v : LL μ} :
    v ∈ fixL μ w J ↔ ∀ x ∈ J, rhoL μ w x v = v := by
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 v).trans ⟨fun h x hx => h _ ⟨x, hx, rfl⟩, ?_⟩
  rintro h _ ⟨x, hx, rfl⟩
  exact h x hx

end Ops

private theorem prod_range {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (X : Set H) (l : List (H →L[ℂ] H))
    (hl : ∀ O ∈ l, ∀ v ∈ X, O v ∈ X) (hO : ∃ O ∈ l, ∀ v, O v ∈ X) (f : H) : l.prod f ∈ X := by
  induction l with
  | nil => obtain ⟨O, hO, -⟩ := hO; simp at hO
  | cons a t ih =>
    rw [List.prod_cons, ContinuousLinearMap.mul_apply]
    obtain ⟨O, hO, hr⟩ := hO
    rcases List.mem_cons.1 hO with rfl | ht
    · exact hr _
    · exact hl a List.mem_cons_self _ (ih (fun O' h' => hl O' (List.mem_cons_of_mem _ h')) ⟨O, ht, hr⟩)

private theorem under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

theorem UpperTheory.prod_localOperators_mem_fixed_and_offN_CMDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (q : Pl F) (w₀ : PlacesOver E q)
        (T : Ty σ n q w₀) (r : ℕ) (p : Fin r → Pl F), Function.Injective p → (∀ i, p i ∈ nsS T) →
        ∀ [∀ u : Pl E, MeasurableSpace (Gw n u)] [∀ u : Pl E, BorelSpace (Gw n u)] (mm : ∀ u : Pl E, Measure (Gw n u)),
          (∀ u, (mm u).IsHaarMeasure) →
        ∀ (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ) (U : ∀ i, Subgroup (Gw n (T.mk' (p i)).1)),
          (∀ i, ∀ u ∈ U i, ∀ g, ψ (p i) (u * g) = ψ (p i) g) →
        ∀ B : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (B i)) →
          (∀ f, (List.ofFn B).prod f ∈ ⨅ i, fixL μ (T.mk' (p i)).1 (U i)) ∧ (∀ f ∈ offN μ T, (List.ofFn B).prod f ∈ offN μ T) := by
  intro F E _ _ _ _ _ σ n μ _ q w₀ T r p hp hns _ _ mm hmm ψ U hU B hB
  have hfix : ∀ i v, B i v ∈ fixL μ (T.mk' (p i)).1 (U i) := fun i v => by
    haveI := hmm (T.mk' (p i)).1
    exact oloc_fix μ (hB i) (U i) (hU i) v
  have hne : ∀ i j, i ≠ j → (T.mk' (p i)).1 ≠ (T.mk' (p j)).1 := fun i j hij h =>
    hij (hp ((under_eq (T.mk' (p i))).symm.trans
      ((congrArg (fun w : Pl E => w.under (𝓞 F)) h).trans (under_eq (T.mk' (p j))))))
  have hcomm : ∀ i (w : Pl E), w ≠ (T.mk' (p i)).1 → ∀ (g : Gw n w) (v : LL μ),
      B i (rhoL μ w g v) = rhoL μ w g (B i v) := fun i w hw g v => by
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v)
      (oloc_comm μ (hB i) (rhoL μ w g) fun g' => rhoL_comm μ hw g g').eq
    simp only [ContinuousLinearMap.mul_apply] at this
    exact this.symm
  refine ⟨fun f => ?_, ?_⟩
  · rw [Submodule.mem_iInf]
    intro i
    refine prod_range (fixL μ (T.mk' (p i)).1 (U i) : Set (LL μ)) (List.ofFn B) (fun O hO v hv => ?_)
      ⟨B i, (List.mem_ofFn' _ _).2 ⟨i, rfl⟩, hfix i⟩ f
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hO
    by_cases h : j = i
    · subst h
      exact hfix j v
    · refine (mem_fixL μ).2 fun x hx => ?_
      rw [← hcomm j _ (hne i j (Ne.symm h)) x v, (mem_fixL μ).1 hv x hx]
  · have hoff : ∀ {v : LL μ}, v ∈ offN μ T ↔
        ∀ w : Pl E, w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) → ∀ x ∈ T.J w, rhoL μ w x v = T.χ w x • v := by
      intro v
      simp only [offN, Submodule.mem_iInf, mem_eigL]
    have key : ∀ O ∈ List.ofFn B, ∀ f ∈ offN μ T, O f ∈ offN μ T := by
      intro O hO f hf
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hO
      refine hoff.2 fun w hw x hx => ?_
      have hwi : w ≠ (T.mk' (p i)).1 := fun h => hw (by
        rw [h, under_eq]
        exact hns i)
      rw [← hcomm i w hwi x f, hoff.1 hf w hw x hx, map_smul]
    exact List.prod_induction (fun O : LL μ →L[ℂ] LL μ => ∀ f ∈ offN μ T, O f ∈ offN μ T)
      (fun a b ha hb f hf => ha _ (hb f hf)) (fun f hf => hf) key
