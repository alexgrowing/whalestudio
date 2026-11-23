import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusTensorEqModulusNorm
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.HermMod

section Scale

def Scales {X : Type} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) (f : X → X)
    (m : ℝ≥0) : Prop :=
  ∃ Φ : X ≃ₜ X, ⇑Φ = f ∧ μ = m • μ.map Φ

variable {X Y : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem Scales.id (μ : Measure X) : Scales μ id 1 :=
  ⟨Homeomorph.refl X, rfl, by simp⟩

theorem Scales.comp {μ : Measure X} {f g : X → X} {m n : ℝ≥0} (hf : Scales μ f m)
    (hg : Scales μ g n) : Scales μ (g ∘ f) (m * n) := by
  obtain ⟨Φ, rfl, h1⟩ := hf
  obtain ⟨Ψ, rfl, h2⟩ := hg
  refine ⟨Φ.trans Ψ, rfl, ?_⟩
  have e : μ.map (Φ.trans Ψ) = (μ.map Φ).map Ψ :=
    (Measure.map_map Ψ.continuous.measurable Φ.continuous.measurable).symm
  rw [e, mul_comm, mul_smul, ← Measure.map_smul, ← h1, ← h2]

theorem Scales.prod [SecondCountableTopology X] [SecondCountableTopology Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] {f : X → X} {g : Y → Y} {m n : ℝ≥0}
    (hf : Scales μ f m) (hg : Scales ν g n) : Scales (μ.prod ν) (Prod.map f g) (m * n) := by
  obtain ⟨Φ, rfl, h1⟩ := hf
  obtain ⟨Ψ, rfl, h2⟩ := hg
  refine ⟨Φ.prodCongr Ψ, rfl, ?_⟩
  have e : (μ.prod ν).map (Φ.prodCongr Ψ) = (μ.map Φ).prod (ν.map Ψ) :=
    (Measure.map_prod_map μ ν Φ.continuous.measurable Ψ.continuous.measurable).symm
  rw [e, mul_smul, ← Measure.prod_smul_right, ← Measure.prod_smul_left, ← h1, ← h2]

theorem Scales.shearL [SecondCountableTopology X] [SecondCountableTopology Y]
    [AddCommGroup Y] [IsTopologicalAddGroup Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] [ν.IsAddRightInvariant]
    {g : X → Y} (hg : Continuous g) :
    Scales (μ.prod ν) (fun p => (p.1, p.2 + g p.1)) 1 := by
  refine ⟨{ toFun := fun p => (p.1, p.2 + g p.1), invFun := fun p => (p.1, p.2 - g p.1)
            left_inv := fun p => by simp, right_inv := fun p => by simp
            continuous_toFun := by fun_prop, continuous_invFun := by fun_prop }, rfl, ?_⟩
  rw [one_smul]
  refine (MeasurePreserving.skew_product (MeasurePreserving.id μ) (g := fun a y => y + g a)
    (Continuous.measurable (by unfold Function.uncurry; fun_prop))
    (Filter.Eventually.of_forall fun a => map_add_right_eq_self ν (g a))).map_eq.symm

theorem Scales.shearR [SecondCountableTopology X] [SecondCountableTopology Y]
    [AddCommGroup X] [IsTopologicalAddGroup X]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] [μ.IsAddRightInvariant]
    {g : Y → X} (hg : Continuous g) :
    Scales (μ.prod ν) (fun p => (p.1 + g p.2, p.2)) 1 := by
  refine ⟨{ toFun := fun p => (p.1 + g p.2, p.2), invFun := fun p => (p.1 - g p.2, p.2)
            left_inv := fun p => by simp, right_inv := fun p => by simp
            continuous_toFun := by fun_prop, continuous_invFun := by fun_prop }, rfl, ?_⟩
  rw [one_smul]
  have h1 := MeasurePreserving.skew_product (MeasurePreserving.id ν) (g := fun a y => y + g a)
    (Continuous.measurable (by unfold Function.uncurry; fun_prop))
    (Filter.Eventually.of_forall fun a => map_add_right_eq_self μ (g a))
  exact ((Measure.measurePreserving_swap.comp h1).comp
    Measure.measurePreserving_swap).map_eq.symm

theorem Scales.mul {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    (ν : Measure S) (hν : ν.IsAddHaarMeasure) {u : S} (hu : IsUnit u) :
    Scales ν (fun z => u * z) (modu S u) := by
  have h := ((modu_basic S).1 u hu).2 ν hν
  obtain ⟨u, rfl⟩ := hu
  exact ⟨{ toFun := fun z => u * z, invFun := fun z => (u⁻¹ : Sˣ) * z
           left_inv := fun p => by simp, right_inv := fun p => by simp
           continuous_toFun := by fun_prop, continuous_invFun := by fun_prop }, rfl, h⟩

end Scale

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem conj_conj (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_of_conj_eq (h : IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ f, algebraMap F E f = e := by
  haveI := Subalgebra.isSimpleOrder_of_finrank h.2.2.1
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h0
  · have : e ∈ AlgHom.equalizer σ (AlgHom.id F E) := he
    rw [h0, Algebra.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    haveI := h.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := h0 ▸ Algebra.mem_top
    have hx' : σ x = x := hx
    have := h.2.2.2 τ x
    rw [hx'] at this
    exact this.symm

theorem trace_field (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  have hσ := conj_conj h
  obtain ⟨a, ha⟩ := exists_of_conj_eq h (e + σ e) (by rw [map_add, hσ, add_comm])
  have h1 : Algebra.trace F E (σ e) = Algebra.trace F E e :=
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)) e
  have h3 := congrArg (Algebra.trace F E) ha
  rw [Algebra.trace_algebraMap, h.2.2.1, map_add, h1, two_smul, ← two_mul, ← two_mul] at h3
  rw [← ha, mul_left_cancel₀ two_ne_zero h3]

variable (R : Type) [CommRing R] [Algebra F R]

theorem trace_tensor (h : IsCMExt F E σ) (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]; ring
  | tmul a e =>
    have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) =
        a * algebraMap F R (Algebra.trace F E e) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    have h4 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h3, h4, ← TensorProduct.tmul_add, ← trace_field h, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm, ← Algebra.smul_def,
      TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem sigR_sigR (h : IsCMExt F E σ) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = _
    rw [conj_conj h]

theorem half_trace (h : IsCMExt F E σ) {z : R ⊗[F] E} (hs : sigR R σ z = z) :
    algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) z) = z := by
  have h2 : algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2)) * 2 = 1 := by
    rw [← IsScalarTower.algebraMap_apply, ← map_ofNat (algebraMap F (R ⊗[F] E)) 2, ← map_mul,
      show (1 / 2 * 2 : F) = 1 by norm_num, map_one]
  rw [map_mul, trace_tensor R h, hs, ← two_mul, ← mul_assoc, h2, one_mul]

theorem exists_norm (h : IsCMExt F E σ) (z : R ⊗[F] E) :
    ∃ k : R, algebraMap R (R ⊗[F] E) k = z * sigR R σ z :=
  ⟨_, half_trace R h (by rw [map_mul, sigR_sigR R h, mul_comm])⟩

theorem hR_symm (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (x y : Fin M → R ⊗[F] E) : sigR R σ (hR R σ J x y) = hR R σ J y x := by
  have hJ' : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := by
    intro i j
    show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [hJ.1]
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_sigR R h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ']
  ring

theorem qR_eq (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (x : Fin M → R ⊗[F] E) : algebraMap R (R ⊗[F] E) (qR R σ J x) = hR R σ J x x :=
  half_trace R h (hR_symm R h hJ x x)

theorem algebraMap_inj : Function.Injective (algebraMap R (R ⊗[F] E)) :=
  Algebra.TensorProduct.includeLeft_injective (R := F) (S := R) (A := R) (B := E)
    (algebraMap F E).injective

theorem hR_lrAct {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : Matrix (Fin 2) (Fin 2) (R ⊗[F] E))
    (X : Fin 2 → Fin M → R ⊗[F] E) (a b : Fin 2) :
    hR R σ J (lrAct 1 γ X a) (lrAct 1 γ X b) =
      sigR R σ (γ 0 a) * γ 0 b * hR R σ J (X 0) (X 0) + sigR R σ (γ 0 a) * γ 1 b * hR R σ J (X 0) (X 1) +
      sigR R σ (γ 1 a) * γ 0 b * hR R σ J (X 1) (X 0) + sigR R σ (γ 1 a) * γ 1 b * hR R σ J (X 1) (X 1) := by
  simp only [hR, Formalism.UG.hform, lrAct, Matrix.one_mulVec, Fin.sum_univ_two, Finset.mul_sum,
    ← Finset.sum_add_distrib, map_add, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem lrAct_mul {S : Type} [CommRing S] {M n : ℕ} (γ δ : Matrix (Fin n) (Fin n) S)
    (X : Fin n → Fin M → S) : lrAct 1 (γ * δ) X = lrAct 1 δ (lrAct 1 γ X) := by
  funext a i
  simp only [lrAct, Matrix.one_mulVec, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end Alg

theorem haar_measure_gram_GL2_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (lam : Measure (R ⊗[F] E)) (ν : Measure R) (γ : GL (Fin 2) E), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ Φ : (R × (R ⊗[F] E) × R) ≃ₜ (R × (R ⊗[F] E) × R), (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ X : (Fin 2 → Fin M → R ⊗[F] E), gram3 R σ J (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR R)) X) = Φ (gram3 R σ J X)) ∧ ν.prod (lam.prod ν) = (modu (R ⊗[F] E) (inclR R (γ : Matrix (Fin 2) (Fin 2) E).det) ^ 2) • (ν.prod (lam.prod ν)).map Φ := by
  intro F E _ _ _ _ _ σ h R _ _ _ _ _ _ _ _ _ lam ν γ hlam hν
  have hA : Continuous (algebraMap R (R ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap R (R ⊗[F] E))
  have hT : Continuous (Algebra.trace R (R ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have hun : ∀ e : E, e ≠ 0 → IsUnit (inclR (F := F) R e) := fun e he => (Ne.isUnit he).map _
  obtain ⟨-, hmul, hone, -⟩ := modu_basic (R ⊗[F] E)
  suffices H : ∀ g : Matrix (Fin 2) (Fin 2) E, g.det ≠ 0 →
      ∃ f : (R × (R ⊗[F] E) × R) → (R × (R ⊗[F] E) × R),
        (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
          ∀ X : (Fin 2 → Fin M → R ⊗[F] E),
            gram3 R σ J (lrAct 1 (g.map (inclR R)) X) = f (gram3 R σ J X)) ∧
        Scales (ν.prod (lam.prod ν)) f (modu (R ⊗[F] E) (inclR R g.det) ^ 2) by
    obtain ⟨f, h1, Φ, rfl, h2⟩ := H γ γ.det_ne_zero
    exact ⟨Φ, h1, h2⟩
  intro g hg
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun g : Matrix (Fin 2) (Fin 2) E =>
      ∃ f : (R × (R ⊗[F] E) × R) → (R × (R ⊗[F] E) × R),
        (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
          ∀ X : (Fin 2 → Fin M → R ⊗[F] E),
            gram3 R σ J (lrAct 1 (g.map (inclR R)) X) = f (gram3 R σ J X)) ∧
        Scales (ν.prod (lam.prod ν)) f (modu (R ⊗[F] E) (inclR R g.det) ^ 2)) g hg ?_ ?_ ?_
  · intro D hD
    rw [Matrix.det_diagonal, Fin.prod_univ_two] at hD ⊢
    have u0 := hun _ (left_ne_zero_of_mul hD)
    have u1 := hun _ (right_ne_zero_of_mul hD)
    obtain ⟨n0, hn0⟩ := exists_norm R h (inclR R (D 0))
    obtain ⟨n1, hn1⟩ := exists_norm R h (inclR R (D 1))
    obtain ⟨v0, e0⟩ := modu_eq_modu_norm F E σ h R _ _ u0 hn0
    obtain ⟨v1, e1⟩ := modu_eq_modu_norm F E σ h R _ _ u1 hn1
    obtain ⟨-, e2⟩ := modu_eq_modu_norm F E σ h R _ n0 (u0.map (sigR R σ))
      (by rw [hn0, sigR_sigR R h, mul_comm])
    refine ⟨_, ?_, by
      have := (Scales.mul ν hν v0).prod ((Scales.mul lam hlam ((u0.map (sigR R σ)).mul u1)).prod
        (Scales.mul ν hν v1))
      rw [hmul _ _ (u0.map (sigR R σ)) u1, e2, e1] at this
      rw [map_mul, hmul _ _ u0 u1, e0, e1]
      convert this using 1
      ring⟩
    intro M J hJ X
    refine Prod.ext (algebraMap_inj (F := F) (E := E) R ?_) (Prod.ext ?_ (algebraMap_inj (F := F) (E := E) R ?_))
    all_goals simp [-Algebra.TensorProduct.algebraMap_apply, gram3, qR_eq R h hJ, hR_lrAct, hn0, hn1]
    all_goals ring
  · rintro ⟨i, j, hij, t⟩
    obtain ⟨n, hn⟩ := exists_norm R h (inclR R t)
    rw [Matrix.TransvectionStruct.det, map_one, hone, one_pow]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · refine ⟨_, ?_, by
        have := ((Scales.id ν).prod (Scales.shearL lam ν
          (g := fun c => Algebra.trace R (R ⊗[F] E) (sigR R σ (inclR R t) * c)) (by fun_prop))).comp
          (Scales.shearL ν (lam.prod ν)
            (g := fun a => (inclR R t * algebraMap R (R ⊗[F] E) a, n * a)) (by fun_prop))
        simpa only [mul_one] using this⟩
      intro M J hJ X
      refine Prod.ext (algebraMap_inj (F := F) (E := E) R ?_) (Prod.ext ?_ (algebraMap_inj (F := F) (E := E) R ?_))
      all_goals simp [-Algebra.TensorProduct.algebraMap_apply, gram3, qR_eq R h hJ, hR_lrAct, hn, trace_tensor R h, sigR_sigR R h, hR_symm R h hJ,
        Matrix.TransvectionStruct.toMatrix, Matrix.transvection]
      all_goals ring
    · refine ⟨_, ?_, by
        have := (Scales.shearR ν (lam.prod ν)
            (g := fun p => Algebra.trace R (R ⊗[F] E) (sigR R σ (inclR R t) * sigR R σ p.1) + n * p.2)
            (by have := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ; fun_prop)).comp
          ((Scales.id ν).prod (Scales.shearR lam ν
          (g := fun d => sigR R σ (inclR R t) * algebraMap R (R ⊗[F] E) d) (by fun_prop)))
        simpa only [mul_one] using this⟩
      intro M J hJ X
      refine Prod.ext (algebraMap_inj (F := F) (E := E) R ?_) (Prod.ext ?_ (algebraMap_inj (F := F) (E := E) R ?_))
      all_goals simp [-Algebra.TensorProduct.algebraMap_apply, gram3, qR_eq R h hJ, hR_lrAct, hn, trace_tensor R h, sigR_sigR R h, hR_symm R h hJ,
        Matrix.TransvectionStruct.toMatrix, Matrix.transvection]
      all_goals ring
    · exact absurd rfl hij
  · rintro A B hA hB ⟨f, hf, sf⟩ ⟨k, hk, sk⟩
    refine ⟨k ∘ f, fun M J hJ X => ?_, ?_⟩
    · rw [Matrix.map_mul, lrAct_mul, hk M J hJ, hf M J hJ]; rfl
    · rw [Matrix.det_mul, map_mul, hmul _ _ (hun _ hA) (hun _ hB), mul_pow]
      exact sf.comp sk

end GlobalTheory.GaugeEx.HermMod
