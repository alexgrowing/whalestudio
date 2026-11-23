import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped RestrictedProduct Topology Classical

namespace UpperTheory.ConvolutionTheory.C

section SlopeTestRemainingChoices

private theorem mem_of_finite_places {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {A : ∀ v, Subgroup (G v)}
    (H : Subgroup (Πʳ v, [G v, A v])) (L C : ∀ v, Subgroup (G v))
    (hL : ∀ v, ∀ x ∈ L v, RestrictedTensor.singleHom A v x ∈ H)
    (base : ∀ h : Πʳ v, [G v, A v], (∀ v, h v ∈ L v) → (∀ v, h v ∈ C v) → h ∈ H)
    (T : Finset ι) : ∀ h : Πʳ v, [G v, A v], (∀ v, h v ∈ L v) → (∀ v ∉ T, h v ∈ C v) → h ∈ H := by
  induction T using Finset.induction_on with
  | empty => exact fun h h1 h2 => base h h1 fun v => h2 v (Finset.notMem_empty v)
  | insert a s has ih =>
    intro h h1 h2
    rw [← RestrictedTensor.single_mul_eraseAt a h]
    refine H.mul_mem (hL a _ (h1 a)) (ih _ (fun v => ?_) (fun v hv => ?_))
    · by_cases hva : v = a
      · subst hva; rw [RestrictedTensor.eraseAt_apply_self]; exact one_mem _
      · rw [RestrictedTensor.eraseAt_apply_of_ne _ hva]; exact h1 v
    · by_cases hva : v = a
      · subst hva; rw [RestrictedTensor.eraseAt_apply_self]; exact one_mem _
      · rw [RestrictedTensor.eraseAt_apply_of_ne _ hva]; exact h2 v (by simp [hva, hv])

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem rhoF_mul (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (a b : AdelicGLn.FiniteAdelicGL K n) (x : LL μ) :
    rhoF μ (a * b) x = rhoF μ a (rhoF μ b x) := by
  simp only [rhoF, _root_.map_mul]
  exact UnitaryRep.map_mul_apply _ _ _ _

private theorem rhoF_one (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (x : LL μ) : rhoF μ 1 x = x := by
  simp only [rhoF, _root_.map_one]
  exact UnitaryRep.map_one_apply _ _

private def stab (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (x : LL μ) : Subgroup (AdelicGLn.FiniteAdelicGL K n) where
  carrier := {g | rhoF μ g x = x}
  one_mem' := rhoF_one μ x
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [rhoF_mul, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← rhoF_mul, inv_mul_cancel, rhoF_one]

private theorem isClosed_stab (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (x : LL μ) :
    IsClosed (stab μ x : Set (AdelicGLn.FiniteAdelicGL K n)) :=
  isClosed_eq (((rightRegularRep (rationalGLOne K n) μ).continuous_orbit x).comp MultiplicityOne.continuous_finProj)
    continuous_const

private theorem mem_fixF (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (W : Subgroup (AdelicGLn.FiniteAdelicGL K n)) (x : LL μ) :
    x ∈ fixF μ W ↔ ∀ u ∈ W, rhoF μ u x = x := by
  simp [fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private theorem mem_fixL (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (Gw n w)) (x : LL μ) :
    x ∈ fixL μ w J ↔ ∀ g ∈ J, rhoF μ (AdelicGLn.localEmbedding w g) x = x := by
  simp [fixL, mem_fixF]

private theorem finAt_finEmb' (h : AdelicGLn.FiniteAdelicGL K n) (v : Pl K) :
    finAt v (finEmb K n h) = AdelicGLn.finiteRestrictedEquiv K n h v := by
  show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n h)).2) v = _
  rw [prodEquiv_finEmb]

private theorem equiv_localEmbedding (w : Pl K) (g : Gw n w) :
    AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.localEmbedding w g) =
      RestrictedTensor.singleHom (fun v : Pl K => GLnLocal.integralGL (v.adicCompletion K) n) w g :=
  ContinuousMulEquiv.apply_symm_apply _ _

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.C

theorem UpperTheory.ConvolutionTheory.C.fixLev :
    UpperTheory.ConvolutionTheory.C.FixLev := by
  intro K _ _ n μ _ P U
  let e := AdelicGLn.finiteRestrictedEquiv K n
  let I : ∀ v : Pl K, Subgroup (Gw n v) := fun v => GLnLocal.integralGL (v.adicCompletion K) n
  let lev : ∀ v : Pl K, Subgroup (Gw n v) := fun v => if v ∈ P then U v else I v
  have hmem : ∀ h, h ∈ levOn P U ↔ ∀ v, e h v ∈ lev v := fun h => by
    show (∀ v, finAt v (finEmb K n h) ∈ _) ↔ _
    simp only [finAt_finEmb']
    rfl
  have hloc : ∀ (v : Pl K) (g : Gw n v), g ∈ lev v → AdelicGLn.localEmbedding v g ∈ levOn P U := fun v g hg => by
    refine (hmem _).2 fun w => ?_
    show e (AdelicGLn.localEmbedding v g) w ∈ lev w
    rw [equiv_localEmbedding]
    by_cases hw : w = v
    · subst hw; rw [RestrictedTensor.singleHom_apply_self]; exact hg
    · rw [RestrictedTensor.singleHom_apply_of_ne _ hw]; exact one_mem _
  apply le_antisymm
  · intro x hx
    rw [mem_fixF] at hx
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · refine Submodule.mem_iInf _ |>.2 fun v => Submodule.mem_iInf _ |>.2 fun hv => ?_
      refine (mem_fixL μ v _ x).2 fun g hg => hx _ (hloc v g ?_)
      simpa [lev, hv, I] using hg
    · refine Submodule.mem_iInf _ |>.2 fun v => Submodule.mem_iInf _ |>.2 fun hv => ?_
      refine (mem_fixL μ v _ x).2 fun g hg => hx _ (hloc v g ?_)
      simpa [lev, hv] using hg
  · intro x hx
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hx
    have hfix : ∀ (v : Pl K) (g : Gw n v), g ∈ lev v → rhoF μ (AdelicGLn.localEmbedding v g) x = x := fun v g hg => by
      by_cases hv : v ∈ P
      · have := (Submodule.mem_iInf _ |>.1 (Submodule.mem_iInf _ |>.1 h2 v) hv)
        exact (mem_fixL μ v _ x).1 this g (by simpa [lev, hv] using hg)
      · have := (Submodule.mem_iInf _ |>.1 (Submodule.mem_iInf _ |>.1 h1 v) hv)
        exact (mem_fixL μ v _ x).1 this g (by simpa [lev, hv, I] using hg)
    let H : Subgroup (Πʳ v : Pl K, [Gw n v, I v]) := (stab μ x).comap e.symm.toMulEquiv.toMonoidHom
    have hHc : IsClosed (H : Set (Πʳ v : Pl K, [Gw n v, I v])) := (isClosed_stab μ x).preimage e.symm.continuous
    have hL : ∀ v, ∀ g ∈ lev v, RestrictedTensor.singleHom I v g ∈ H := fun v g hg => by
      show rhoF μ (e.symm _) x = x
      have : e.symm (RestrictedTensor.singleHom I v g) = AdelicGLn.localEmbedding v g := by
        rw [ContinuousMulEquiv.symm_apply_eq]
        exact (equiv_localEmbedding v g).symm
      rw [this]
      exact hfix v g hg
    have hfin := mem_of_finite_places H lev (fun _ => ⊥) hL (fun h _ hb => by
      have : h = 1 := DFunLike.ext _ _ fun v => Subgroup.mem_bot.1 (hb v)
      rw [this]; exact one_mem _)
    have hint := mem_of_finite_places H lev I hL (fun h ha hb => by
      let x0 : ∀ v : Pl K, (I v : Set (Gw n v)) := fun v => ⟨h v, hb v⟩
      let y : Finset (Pl K) → ∀ v : Pl K, (I v : Set (Gw n v)) := fun S v => if v ∈ S then x0 v else ⟨1, one_mem _⟩
      let f : (∀ v : Pl K, (I v : Set (Gw n v))) → Πʳ v : Pl K, [Gw n v, I v] := RestrictedProduct.structureMap _ _ Filter.cofinite
      have hf : Continuous f := RestrictedProduct.isEmbedding_structureMap.continuous
      have hy : Tendsto y atTop (𝓝 x0) := tendsto_pi_nhds.2 fun v =>
        tendsto_const_nhds.congr' ((eventually_ge_atTop ({v} : Finset (Pl K))).mono fun S hS => by
          have : v ∈ S := hS (Finset.mem_singleton_self v)
          simp [y, this])
      have hlim := (hf.tendsto x0).comp hy
      have hx0 : f x0 = h := DFunLike.ext _ _ fun v => rfl
      rw [hx0] at hlim
      refine hHc.mem_of_tendsto hlim (Eventually.of_forall fun S => ?_)
      refine hfin S _ (fun v => ?_) (fun v hv => ?_)
      · by_cases hv : v ∈ S
        · show ((y S v : _) : Gw n v) ∈ lev v
          simp only [y, hv, if_true]; exact ha v
        · show ((y S v : _) : Gw n v) ∈ lev v
          simp only [y, hv, if_false]; exact one_mem _
      · show ((y S v : _) : Gw n v) ∈ (⊥ : Subgroup (Gw n v))
        simp only [y, hv, if_false]; exact one_mem _) P
    refine (mem_fixF μ _ x).2 fun u hu => ?_
    have := hint (e u) ((hmem u).1 hu) (fun v hv => by
      have := (hmem u).1 hu v
      simpa [lev, hv] using this)
    show u ∈ stab μ x
    have h3 : e.symm (e u) ∈ stab μ x := this
    simpa using h3
