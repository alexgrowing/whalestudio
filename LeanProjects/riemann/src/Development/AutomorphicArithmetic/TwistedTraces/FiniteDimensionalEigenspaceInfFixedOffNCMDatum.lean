import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensOp
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.EigAdm
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

section One
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

private theorem mem_eigL' (w : Pl K) (J : Subgroup (Gw n w)) (χ : Gw n w → ℂ) (v : LL μ) :
    v ∈ eigL μ w J χ ↔ ∀ x ∈ J, rhoL μ w x v = χ x • v := by
  simp only [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
    LinearMap.id_apply]

private theorem mem_fixL' (w : Pl K) (J : Subgroup (Gw n w)) (v : LL μ) :
    v ∈ fixL μ w J ↔ ∀ x ∈ J, rhoL μ w x v = v := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply,
    Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, rhoL]

private theorem rhoL_comm {w w' : Pl K} (hne : w' ≠ w) (g : Gw n w) (x : Gw n w') (v : LL μ) :
    rhoL μ w' x (rhoL μ w g v) = rhoL μ w g (rhoL μ w' x v) := by
  have h := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' hne g x
  simp only [rhoL, rhoF]
  rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, ← map_mul, ← map_mul, h]

end One

private theorem kerChr_co {G : Type} [Group G] [TopologicalSpace G] {J : Subgroup G} {χ : G → ℂ} (hJ : CO J) (h : IsChr J χ) :
    CO (kerChr J χ h) := by
  have e : (kerChr J χ h : Set G) = (J : Set G) ∩ χ ⁻¹' {1} := rfl
  have ho : IsOpen (χ ⁻¹' {(1 : ℂ)}) := h.1.isOpen_fiber 1
  have hc : IsClosed (χ ⁻¹' {(1 : ℂ)}) := isClosed_singleton.preimage h.1.continuous
  rw [CO, e]
  exact ⟨hJ.1.inter_right hc, hJ.2.inter ho⟩

private theorem exists_ext {A ι : Type*} {B : A → Type*} (f : ι → A) (hf : Function.Injective f) (U : ∀ i, B (f i))
    (d : ∀ a, B a) : ∃ U' : ∀ a, B a, (∀ i, U' (f i) = U i) ∧ ∀ a, a ∉ Set.range f → U' a = d a := by
  have key : ∀ (i j : ι) (hj : f j = f i), (hj ▸ U j : B (f i)) = U i := by
    intro i j hj
    obtain rfl := hf hj
    rfl
  refine ⟨fun a => if h : ∃ i, f i = a then h.choose_spec ▸ U h.choose else d a, fun i => ?_, fun a ha => dif_neg ha⟩
  have h : ∃ j, f j = f i := ⟨i, rfl⟩
  simp only [dif_pos h]
  exact key i _ _

section Two
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {n : ℕ} {q : Pl F} {w₀ : PlacesOver E q}
variable (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]

private theorem under_of_over {v : Pl F} (u : PlacesOver E v) : u.1.under (𝓞 F) = v := by
  ext1
  exact (Ideal.over_def u.1.asIdeal v.asIdeal).symm

private theorem finite_over (v : Pl F) : {w : Pl E | w.under (𝓞 F) = v}.Finite := by
  refine (Set.finite_range fun u : PlacesOver E v => u.1).subset fun w hw => ?_
  subst hw
  exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem mem_Zv (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (O : LL μ →L[ℂ] LL μ) (x : ℝ) (v : LL μ) :
    v ∈ eigIn (V ⊓ offN μ T) O x ↔ v ∈ V ∧ (∀ w : Pl E, w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) → v ∈ eigL μ w (T.J w) (T.χ w)) ∧
      O v = (x : ℂ) • v := by
  simp only [eigIn, offN, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe,
    and_assoc]

private theorem Zv_closed (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (hV : IsClosed (V : Set (LL μ))) (O : LL μ →L[ℂ] LL μ) (x : ℝ) :
    IsClosed (eigIn (V ⊓ offN μ T) O x : Set (LL μ)) := by
  have e : (eigIn (V ⊓ offN μ T) O x : Set (LL μ)) = (V : Set (LL μ)) ∩ ((⋂ w, ⋂ (_ : w.under (𝓞 F) ∉ (nsS T : Set (Pl F))),
      (eigL μ w (T.J w) (T.χ w) : Set (LL μ))) ∩ {v | O v = (x : ℂ) • v}) := by
    ext v
    simp only [SetLike.mem_coe, mem_Zv, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [e]
  refine hV.inter (IsClosed.inter ?_ (isClosed_eq O.continuous (continuous_const_smul _)))
  exact isClosed_iInter fun w => isClosed_iInter fun _ =>
    (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) (T.χ w) (T.co w) (T.chr w)).1

end Two

theorem UpperTheory.finiteDimensional_eigenspace_inf_fixed_offN_CMDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
        (ν : Measure (archGroup E n)) [ν.IsHaarMeasure] (a : TI E n) (q : Pl F) (w₀ : PlacesOver E q) (T : Ty σ n q w₀)
        (V : Submodule ℂ (LL μ)), IsSummand μ V → (∀ v ∈ nsS T, ∀ u : PlacesOver E v, u = T.mk' v) → ∀ x : ℝ, x ≠ 0 →
          IsClosed (eigIn (V ⊓ offN μ T) (Oinf μ ν a) x : Set (LL μ)) ∧
          (∀ v ∈ nsS T, ∀ g, ∀ f ∈ eigIn (V ⊓ offN μ T) (Oinf μ ν a) x, rhoL μ (T.mk' v).1 g f ∈ eigIn (V ⊓ offN μ T) (Oinf μ ν a) x) ∧
          ∀ (r : ℕ) (p : Fin r → Pl F), Function.Injective p → (∀ v, v ∈ nsS T ↔ v ∈ Set.range p) →
          ∀ U : ∀ i, Subgroup (Gw n (T.mk' (p i)).1), (∀ i, CO (U i)) →
            FiniteDimensional ℂ ↥(eigIn (V ⊓ offN μ T) (Oinf μ ν a) x ⊓ ⨅ i, fixL μ (T.mk' (p i)).1 (U i)) := by
  intro F E _ _ _ _ _ σ n hn μ _ ν _ a q w₀ T V hV huniq x hx
  refine ⟨Zv_closed μ T V hV.closed _ x, ?_, ?_⟩
  · intro v hv g f hf
    obtain ⟨m, _, -⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx E n hn).2.1 μ ν
    obtain ⟨h1, h2, h3⟩ := (mem_Zv μ T V _ x f).1 hf
    refine (mem_Zv μ T V _ x _).2 ⟨hV.inv _ _ h1, fun w hw => ?_, ?_⟩
    · refine (mem_eigL' μ _ _ _ _).2 fun y hy => ?_
      have hne : w ≠ (T.mk' v).1 := fun h => hw (by rw [h, under_of_over]; exact hv)
      rw [rhoL_comm μ hne, (mem_eigL' μ _ _ _ _).1 (h2 w hw) y hy, map_smul]
    · have hc : Oinf μ ν a (rhoL μ (T.mk' v).1 g f) = rhoL μ (T.mk' v).1 g (Oinf μ ν a f) :=
        DFunLike.congr_fun ((UpperTheory.ConvolutionTheory.Tf.opAlg E n μ ν m).2.2.2.2.2.2.2.2 a (AdelicGLn.localEmbedding (T.mk' v).1 g)).eq f
      rw [hc, h3, map_smul]
  · intro r p hp hpr U hU
    have hfin : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S}.Finite := by
      have : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S} = ⋃ v ∈ insert q T.S, {w : Pl E | w.under (𝓞 F) = v} := by
        ext w
        simp
      rw [this]
      exact (Finset.finite_toSet _).biUnion fun v _ => finite_over v
    set P : Finset (Pl E) := hfin.toFinset with hP
    have hPm : ∀ w, w ∈ P ↔ w.under (𝓞 F) ∈ insert q T.S := fun w => by simp [hP]
    let f : Fin r → Pl E := fun i => (T.mk' (p i)).1
    have hf : Function.Injective f := fun i j hij => hp (by
      have := congrArg (fun w : Pl E => w.under (𝓞 F)) hij
      simpa only [f, under_of_over] using this)
    obtain ⟨U', hU1, hU2⟩ := exists_ext (B := fun w : Pl E => Subgroup (Gw n w)) f hf U
      (fun w => kerChr (T.J w) (T.χ w) (T.chr w))
    have hU' : ∀ w ∈ P, CO (U' w) := fun w _ => by
      by_cases hw : w ∈ Set.range f
      · obtain ⟨i, rfl⟩ := hw
        rw [hU1]
        exact hU i
      · rw [hU2 w hw]
        exact kerChr_co (T.co w) (T.chr w)
    have hoff : ∀ w : Pl E, w ∉ Set.range f → w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) := fun w hw h => by
      have h' : w.under (𝓞 F) ∈ nsS T := h
      have e := huniq _ h' ⟨w, ⟨rfl⟩⟩
      obtain ⟨i, hi⟩ := (hpr _).1 h'
      refine hw ⟨i, ?_⟩
      have e' : w = (T.mk' (w.under (𝓞 F))).1 := congrArg Subtype.val e
      exact (congrArg (fun v => (T.mk' v).1) hi).trans e'.symm
    haveI := UpperTheory.ConvolutionTheory.C.eigAdm E n hn μ ν a x hx P U' hU'
    refine Submodule.finiteDimensional_of_le (fun v hv => ?_)
      (S₂ := eigIn (cuspidalL2 μ) (Oinf μ ν a) x ⊓ sphOff μ P ⊓ ⨅ w ∈ P, fixL μ w (U' w))
    obtain ⟨hZ, hfx⟩ := Submodule.mem_inf.1 hv
    obtain ⟨h1, h2, h3⟩ := (mem_Zv μ T V _ x v).1 hZ
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hV.le h1, ?_⟩, ?_⟩, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, h3]
    · refine (Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).2 fun hw => ?_
      have hu : w.under (𝓞 F) ∉ insert q T.S := fun h => hw ((hPm w).2 h)
      have hS : w.under (𝓞 F) ∉ T.S := fun h => hu (Finset.mem_insert_of_mem h)
      obtain ⟨e1, e2⟩ := T.off w hS (fun h => hu (by rw [h]; exact Finset.mem_insert_self _ _))
      have hns : w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) := fun h => hS (Finset.mem_filter.1 h).1
      refine (mem_fixL' μ _ _ _).2 fun y hy => ?_
      rw [(mem_eigL' μ _ _ _ _).1 (h2 w hns) y (e1 ▸ hy), e2]
      simp
    · refine (Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).2 fun _ => ?_
      by_cases hw : w ∈ Set.range f
      · obtain ⟨i, rfl⟩ := hw
        rw [hU1]
        exact (Submodule.mem_iInf _).1 hfx i
      · rw [hU2 w hw]
        refine (mem_fixL' μ _ _ _).2 fun y hy => ?_
        rw [(mem_eigL' μ _ _ _ _).1 (h2 w (hoff w hw)) y hy.1, hy.2, one_smul]
