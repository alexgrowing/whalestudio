import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatSubst

theorem setLIntegral_comp_addEquiv {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (e : G ≃+ G) (he : Continuous e) (hes : Continuous e.symm)
    (hΓ : ∀ x, e x ∈ Γ ↔ x ∈ Γ) (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G}
    (hF : IsAddFundamentalDomain Γ F μ) (hfin : μ F ≠ ⊤) (φ : G → ENNReal)
    (hφ : ∀ γ ∈ Γ, ∀ x, φ (γ + x) = φ x) : ∫⁻ w in F, φ (e w) ∂μ = ∫⁻ w in F, φ w ∂μ := by
  let m : G ≃ᵐ G :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving m (μ.map e.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving e (μ.map e.symm) μ := hmp
  have hν : (μ.map e.symm).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ e.symm hes (by simpa using he)
  have hF' : IsAddFundamentalDomain Γ (e ⁻¹' F) (μ.map e.symm) := by
    let f : Γ → Γ := fun y => ⟨e.symm y, (hΓ _).1 (by simp)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, (hΓ _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine hF.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.map e.symm = c • μ := ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ⟩
  have hac : μ.map e.symm ≪ μ := hc ▸ Measure.smul_absolutelyContinuous
  have hF'' : IsAddFundamentalDomain Γ F (μ.map e.symm) := hF.mono hac
  have h1 : (μ.map e.symm) (e ⁻¹' F) = μ F := hmp.measure_preimage_equiv F
  have h2 : (μ.map e.symm) F = μ F := (hF''.measure_eq hF').trans h1
  have h0 : μ F ≠ 0 := hF.measure_ne_zero (NeZero.ne μ)
  have hc1 : (c : ENNReal) = 1 := by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    exact (ENNReal.mul_left_inj h0 hfin).1 (by rw [h2, one_mul])
  have hc2 : c = 1 := by exact_mod_cast hc1
  rw [hc2, one_smul] at hc
  have h3 : ∫⁻ w in e ⁻¹' F, φ (e w) ∂(μ.map e.symm) = ∫⁻ w in F, φ w ∂μ :=
    hmp.setLIntegral_comp_preimage_emb m.measurableEmbedding φ F
  rw [hc] at h3 hF'
  rw [← h3]
  refine hF.setLIntegral_eq hF' (fun w => φ (e w)) fun g x => ?_
  show φ (e ((g : G) + x)) = φ (e x)
  rw [map_add, hφ _ ((hΓ _).2 g.2)]

variable {D : D7} {S T : HSp D}

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem mt_mul (V : HSp D) (g g' : GA D V) : Formalism.L2.Theta.mt V (g * g') = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g' := rfl

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem actO_inv_actO (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  unfold actO
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul, Matrix.mul_assoc,
    ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

theorem symplOH_actO (g : GA D S) (h : GA D T) (x y : WO S T) :
    symplOH S T (actO S T g h x) (actO S T g h y) = symplOH S T x y := by
  unfold symplOH
  rw [GlobalTheory.SymplOInv.symplO_actO]

theorem exists_mt_eq (V : HSp D) {γ : GA D V} (h : γ ∈ GQ V) :
    ∃ m : Matrix (Fin V.rank) (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ = m.map (incA D) := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ'.1, (congrArg Units.val e).symm⟩

theorem exists_actO_ratW {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ∃ y, actO S T γ γ' (ratW T S x) = ratW T S y := by
  obtain ⟨m, hm⟩ := exists_mt_eq S ((GQ S).inv_mem hγ)
  obtain ⟨m', hm'⟩ := exists_mt_eq T hγ'
  refine ⟨m' * x * m, ?_⟩
  unfold actO ratW
  rw [hm, hm', Matrix.map_mul, Matrix.map_mul]

theorem actO_mem_ratL {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T) {x : WO S T}
    (hx : x ∈ ratL T S) : actO S T γ γ' x ∈ ratL T S := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, hz⟩ := exists_actO_ratW hγ hγ' y
  exact ⟨z, hz.symm⟩

theorem isThetaFunO_comp {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T) :
    IsThetaFunO ψ S T fun w => f (actO S T γ γ' w) := by
  let A : WO S T →+ WO S T := AddMonoidHom.mk' (actO S T γ γ') (actO_add γ γ')
  have hA : Continuous (actO S T γ γ') := GlobalTheory.LatLevel.continuous_actO S T γ γ'
  refine ⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩
  · obtain ⟨y, e⟩ := exists_actO_ratW hγ hγ' x
    rw [actO_add, ← symplOH_actO γ γ', e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu (GlobalTheory.LatLevel.actO_map_inf S T γ γ' h0)) (actO S T γ γ' w)
    unfold heisO at e ⊢
    rw [← e, ← symplOH_actO γ γ' w u]
    exact congrArg (fun x => _ * f x) (actO_add γ γ' w u)
  · have h3 : ∀ t, (actO S T γ γ' (L t)).map (finPart D) = 0 := fun t => by
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    have := hf.smooth k (A.comp L) (hA.comp h1) h3 (actO S T γ γ' w)
    simp only [actO_add]
    exact this

theorem rational_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (fun w => f (actO S T γ⁻¹ γ'⁻¹ w)) ∧ (∀ w₀, (fun w => heisO ψ S T w₀ f (actO S T γ⁻¹ γ'⁻¹ w)) = heisO ψ S T (actO S T γ γ' w₀) (fun w => f (actO S T γ⁻¹ γ'⁻¹ w))) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∫⁻ w in 𝓕, ‖f (actO S T γ⁻¹ γ'⁻¹ w)‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
  intro D ψ hψ S T γ hγ γ' hγ' f hf
  have hi := (GQ S).inv_mem hγ
  have hi' := (GQ T).inv_mem hγ'
  refine ⟨isThetaFunO_comp hf hi hi', fun w₀ => ?_, fun μ 𝓕 hμ h𝓕 => ?_⟩
  · funext w
    unfold heisO
    beta_reduce
    rw [actO_add, actO_inv_actO, ← symplOH_actO γ⁻¹ γ'⁻¹ w, actO_inv_actO]
  · obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
    have : BorelSpace (WO S T) := ⟨rfl⟩
    have : Countable (ratL T S) := countable_of_discrete_addSubgroup _
    have hinv : ∀ x, actO S T γ γ' (actO S T γ⁻¹ γ'⁻¹ x) = x := fun x => by
      have := actO_inv_actO γ⁻¹ γ'⁻¹ x
      rwa [inv_inv, inv_inv] at this
    let e : WO S T ≃+ WO S T :=
      { toFun := actO S T γ⁻¹ γ'⁻¹
        invFun := actO S T γ γ'
        left_inv := hinv
        right_inv := actO_inv_actO γ γ'
        map_add' := actO_add _ _ }
    refine setLIntegral_comp_addEquiv (G := WO S T) (ratL T S) e (GlobalTheory.LatLevel.continuous_actO S T _ _)
      (GlobalTheory.LatLevel.continuous_actO S T _ _) (fun x => ⟨fun hx => ?_, actO_mem_ratL hi hi'⟩) μ h𝓕
      (measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hcov μ h𝓕).ne
      (fun w => ‖f w‖ₑ ^ 2) ?_
    · rw [← hinv x]
      exact actO_mem_ratL hγ hγ' hx
    · rintro _ ⟨y, rfl⟩ x
      have h6 : f (ratW T S y + x) = _ := hf.quasi y x
      have h7 : ‖f (ratW T S y + x)‖ = ‖f x‖ := by
        rw [h6, norm_mul, hψ.1.2.1, one_mul]
      show ‖f (ratW T S y + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h7]

end GlobalTheory.RatSubst

end
