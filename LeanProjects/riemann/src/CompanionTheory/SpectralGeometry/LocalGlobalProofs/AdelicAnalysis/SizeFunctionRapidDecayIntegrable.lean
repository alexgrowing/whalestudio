import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SizeInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def compReal (hF : IsTotallyReal F) (v : InfinitePlace F) : v.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (hF.isReal v)

theorem continuous_compReal (hF : IsTotallyReal F) (v : InfinitePlace F) :
    Continuous (compReal hF v) :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal v)).continuous

theorem continuous_compReal_symm (hF : IsTotallyReal F) (v : InfinitePlace F) :
    Continuous (compReal hF v).symm :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal v)).symm.continuous

theorem norm_compReal (hF : IsTotallyReal F) (v : InfinitePlace F) (x : v.Completion) :
    ‖compReal hF v x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hF.isReal v)).norm_map_of_map_zero
    (map_zero _) x

theorem secondCountable_Ainf (hF : IsTotallyReal F) : SecondCountableTopology (Ainf F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal v)).toHomeomorph.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))

section Coord

variable {d : ℕ} (hF : IsTotallyReal F) (b : Module.Basis (Fin d) F E)

def ainfEquiv : Ainf F ≃+ (InfinitePlace F → ℝ) where
  toFun x v := compReal hF v (x v)
  invFun w := (fun v => (compReal hF v).symm (w v) : ∀ v : InfinitePlace F, v.Completion)
  left_inv x := by funext v; exact (compReal hF v).symm_apply_apply _
  right_inv w := by funext v; exact (compReal hF v).apply_symm_apply _
  map_add' x y := by funext v; exact map_add (compReal hF v) (x v) (y v)

theorem continuous_ainfEquiv : Continuous (ainfEquiv hF) :=
  continuous_pi fun v => (continuous_compReal hF v).comp (continuous_apply (A := fun v : InfinitePlace F => v.Completion) v)

theorem continuous_ainfEquiv_symm : Continuous (ainfEquiv hF).symm := by
  have h : Continuous fun (w : InfinitePlace F → ℝ) (v : InfinitePlace F) =>
      ((compReal hF v).symm (w v) : v.Completion) :=
    continuous_pi fun v => (continuous_compReal_symm hF v).comp (continuous_apply v)
  exact h

def coordEquiv : Ainf F ⊗[F] E ≃+ (Fin d → InfinitePlace F → ℝ) :=
  (Algebra.TensorProduct.basis (Ainf F) b).equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => ainfEquiv hF)

theorem abs_coordEquiv (y : Ainf F ⊗[F] E) (k : Fin d) (v : InfinitePlace F) :
    ‖coordEquiv hF b y k v‖ = ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y k v‖ :=
  norm_compReal hF v _

def tupEquiv (n M : ℕ) :
    (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin n → Fin M → Fin d → InfinitePlace F → ℝ) :=
  AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ => coordEquiv hF b

theorem tupEquiv_apply (n M : ℕ) (X : Fin n → Fin M → Ainf F ⊗[F] E) (a : Fin n) (i : Fin M) :
    tupEquiv hF b n M X a i = coordEquiv hF b (X a i) := rfl

theorem norm_tupEquiv_le (n M : ℕ) (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    ‖tupEquiv hF b n M X‖ ≤ sizeTup b X := by
  have h0 : ∀ (y : Ainf F ⊗[F] E) (k : Fin d) (v : InfinitePlace F),
      0 ≤ ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y k v‖ := fun _ _ _ => norm_nonneg _
  have hI : ∀ y : Ainf F ⊗[F] E, 0 ≤ sizeInf b y := fun y =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => h0 y k v
  have hT : 0 ≤ sizeTup b X := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => hI _
  refine (pi_norm_le_iff_of_nonneg hT).2 fun a => (pi_norm_le_iff_of_nonneg hT).2 fun i =>
    (pi_norm_le_iff_of_nonneg hT).2 fun k => (pi_norm_le_iff_of_nonneg hT).2 fun v => ?_
  rw [tupEquiv_apply, abs_coordEquiv]
  calc ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v‖
      ≤ ∑ v', ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v'‖ :=
        Finset.single_le_sum (f := fun v' => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v'‖)
          (fun v' _ => norm_nonneg _) (Finset.mem_univ v)
    _ ≤ sizeInf b (X a i) :=
        Finset.single_le_sum (f := fun k' => ∑ v', ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k' v'‖)
          (fun k' _ => Finset.sum_nonneg fun v' _ => norm_nonneg _) (Finset.mem_univ k)
    _ ≤ ∑ i', sizeInf b (X a i') :=
        Finset.single_le_sum (f := fun i' => sizeInf b (X a i')) (fun i' _ => hI _) (Finset.mem_univ i)
    _ ≤ sizeTup b X :=
        Finset.single_le_sum (f := fun a' => ∑ i', sizeInf b (X a' i'))
          (fun a' _ => Finset.sum_nonneg fun i' _ => hI _) (Finset.mem_univ a)

theorem continuous_coordEquiv
    (hc : IsHomeomorph fun (y : Ainf F ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis (Ainf F) b).repr y k) :
    Continuous (coordEquiv hF b) :=
  continuous_pi fun k => (continuous_ainfEquiv hF).comp ((continuous_apply k).comp hc.continuous)

theorem continuous_coordEquiv_symm
    (hc : IsHomeomorph fun (y : Ainf F ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis (Ainf F) b).repr y k) :
    Continuous (coordEquiv hF b).symm := by
  have h1 : Continuous fun w : Fin d → InfinitePlace F → ℝ => fun k => (ainfEquiv hF).symm (w k) :=
    continuous_pi fun k => (continuous_ainfEquiv_symm hF).comp (continuous_apply k)
  have h2 := (hc.homeomorph _).symm.continuous.comp h1
  convert h2 using 1
  funext w
  apply (hc.homeomorph _).injective
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  funext k
  show (Algebra.TensorProduct.basis (Ainf F) b).repr ((coordEquiv hF b).symm w) k = _
  apply (ainfEquiv hF).injective
  rw [AddEquiv.apply_symm_apply]
  have := congrFun ((coordEquiv hF b).apply_symm_apply w) k
  exact this

end Coord

theorem size_neg_pow_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) ∧ (∀ X : Fin n → Fin M → Ainf F ⊗[F] E, 0 ≤ sizeTup b X) ∧ ∃ N : ℕ, ∫⁻ X, ENNReal.ofReal (((1 + sizeTup b X) ^ N)⁻¹) ∂μ < ⊤ := by
  intro F E _ _ _ _ _ σ hCM d b n M μ hμ
  have hF : IsTotallyReal F := hCM.1
  haveI : SecondCountableTopology (Ainf F) := secondCountable_Ainf hF
  haveI : T2Space (Ainf F) := inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))
  obtain ⟨hring, -, -, -, -, -, hhom, hborel, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  haveI := hring
  haveI := hborel n M
  have hc := hhom d b
  have hce := continuous_coordEquiv hF b hc
  have hcs := continuous_coordEquiv_symm hF b hc
  have hnorm : ∀ y : Ainf F ⊗[F] E, sizeInf b y = ∑ k, ∑ v, ‖coordEquiv hF b y k v‖ := fun y => by
    simp only [abs_coordEquiv, sizeInf]
  have hcontI : Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
    have : (sizeInf b : Ainf F ⊗[F] E → ℝ) = fun y => ∑ k, ∑ v, ‖coordEquiv hF b y k v‖ := funext hnorm
    rw [this]
    refine continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun v _ => ?_
    exact ((continuous_apply v).comp ((continuous_apply k).comp hce)).norm
  have hcontT : Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
    unfold sizeTup
    refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun i _ => ?_
    exact hcontI.comp ((continuous_apply i).comp (continuous_apply a))
  have hI0 : ∀ y : Ainf F ⊗[F] E, 0 ≤ sizeInf b y := fun y =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => norm_nonneg _
  have hT0 : ∀ X : Fin n → Fin M → Ainf F ⊗[F] E, 0 ≤ sizeTup b X := fun X =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => hI0 _
  refine ⟨hcontT, hT0, ?_⟩
  let e := tupEquiv hF b n M
  have he : Continuous e :=
    continuous_pi fun a => continuous_pi fun i => hce.comp ((continuous_apply i).comp (continuous_apply a))
  have hes : Continuous e.symm :=
    continuous_pi fun a => continuous_pi fun i => hcs.comp ((continuous_apply i).comp (continuous_apply a))
  let W := Fin n → Fin M → Fin d → InfinitePlace F → ℝ
  haveI b1 : BorelSpace (Fin d → InfinitePlace F → ℝ) := inferInstance
  haveI s1 : SecondCountableTopology (Fin d → InfinitePlace F → ℝ) := inferInstance
  haveI b2 : BorelSpace (Fin M → Fin d → InfinitePlace F → ℝ) := Pi.borelSpace
  haveI s2 : SecondCountableTopology (Fin M → Fin d → InfinitePlace F → ℝ) := inferInstance
  haveI b3 : BorelSpace W := Pi.borelSpace
  haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  obtain ⟨N, hN⟩ := exists_nat_gt (Module.finrank ℝ W : ℝ)
  refine ⟨N, ?_⟩
  have hfin := finite_integral_one_add_norm (μ := Measure.map e μ) (E := W) (r := (N : ℝ)) hN
  have hmeas : Measurable fun y : W => ENNReal.ofReal ((1 + ‖y‖) ^ (-(N : ℝ))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (Continuous.rpow_const (by fun_prop) fun y => Or.inl (by positivity)).measurable
  rw [lintegral_map hmeas he.measurable] at hfin
  refine lt_of_le_of_lt (lintegral_mono fun X => ?_) hfin
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (0 : ℝ) < 1 + ‖e X‖ := by positivity
  rw [Real.rpow_neg h1.le, Real.rpow_natCast]
  have h2 : 1 + ‖e X‖ ≤ 1 + sizeTup b X := by
    have := norm_tupEquiv_le hF b n M X
    linarith
  exact inv_anti₀ (pow_pos h1 N) (pow_le_pow_left₀ h1.le h2 N)

end GlobalTheory.CompanionTheory.SW.SizeInt
