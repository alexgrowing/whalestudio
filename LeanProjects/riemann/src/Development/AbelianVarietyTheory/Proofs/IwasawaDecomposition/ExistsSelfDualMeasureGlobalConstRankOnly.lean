import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyRealStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyRealStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedActionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesComplet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorNiceRingArtinianReducedOpenUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaHaarModulusCmFieldElementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNormalizedLocalHaarSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualHaarMeasureInfiniteAdelesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualCompSelfAdjointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlaceStatement

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.GaugeSdMain

def mulHomeo {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (u : Rˣ) : R ≃ₜ R where
  toFun z := (u : R) * z
  invFun z := ((u⁻¹ : Rˣ) : R) * z
  left_inv z := by simp [← mul_assoc]
  right_inv z := by simp [← mul_assoc]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem sdR_change (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (ψ0 ψ : R → ℂ) (a : R) (ha : IsUnit a) (h : ∀ x, ψ x = ψ0 (a * x)) (ν : Measure R)
    (hν : SdR R ψ0 ν) : SdR R ψ (NNReal.sqrt (modu R a) • ν) := by
  obtain ⟨hpos, hm⟩ := (GlobalTheory.GaugeEx.modu_basic R).1 a ha
  have h1 := GlobalTheory.T.selfDual_sqrt_smul_comp_of_invariant R ν (fun s t => ψ0 (s * t)) (mulHomeo ha.unit) (modu R a) hpos.ne'
    (hm ν hν.1) (fun x y => by
      show ψ0 (x * (a * y)) = ψ0 ((a * x) * y)
      congr 1; ring) hν
  have h2 : (fun s t : R => ψ (s * t)) = fun x y => ψ0 (x * mulHomeo ha.unit y) := by
    funext x y
    show ψ (x * y) = ψ0 (x * (a * y))
    rw [h]; congr 1; ring
  unfold SdR
  rw [h2]
  exact h1

theorem lrAct_one {S : Type} [CommRing S] {n M : ℕ} (g : Matrix (Fin M) (Fin M) S)
    (X : Fin n → Fin M → S) : lrAct g (1 : Matrix (Fin n) (Fin n) S) X = fun a => g.mulVec (X a) := by
  funext a
  simp [lrAct, Matrix.one_apply]

def actHomeo {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] {n M : ℕ}
    (g : Matrix (Fin M) (Fin M) S) (hg : IsUnit g.det) :
    (Fin n → Fin M → S) ≃ₜ (Fin n → Fin M → S) where
  toFun X := fun a => g.mulVec (X a)
  invFun X := fun a => g⁻¹.mulVec (X a)
  left_inv X := by
    funext a
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hg, Matrix.one_mulVec]
  right_inv X := by
    funext a
    simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hg, Matrix.one_mulVec]
  continuous_toFun := continuous_pi fun a => continuous_const.matrix_mulVec (continuous_apply a)
  continuous_invFun := continuous_pi fun a => continuous_const.matrix_mulVec (continuous_apply a)

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ}

theorem hR_one (x y : Fin M → R ⊗[F] E) :
    hR R σ (1 : Matrix (Fin M) (Fin M) E) x y = ∑ i, sigR R σ (x i) * y i := by
  unfold hR JR Formalism.UG.hform
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  simp [Matrix.one_apply]

theorem sigR_inclR (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem hR_one_mulVec (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → R ⊗[F] E) :
    hR R σ (1 : Matrix (Fin M) (Fin M) E) x ((JR R J).mulVec y) = hR R σ J x y := by
  rw [hR_one]
  simp only [hR, Formalism.UG.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem hR_one_mulVec' (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (x y : Fin M → R ⊗[F] E) :
    hR R σ (1 : Matrix (Fin M) (Fin M) E) ((JR R J).mulVec x) y = hR R σ J x y := by
  rw [hR_one]
  simp only [hR, Formalism.UG.hform, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, JR,
    Matrix.map_apply, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem BR_smul {n : ℕ} (a : F) (J : Matrix (Fin M) (Fin M) E) (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ (a • J) X Y = algebraMap F R a * BR R σ J X Y := by
  unfold BR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  have e : ∀ e : E, inclR R (a • e) = (algebraMap F R a) • (inclR R e : R ⊗[F] E) := by
    intro e
    simp only [inclR, algebraMap_smul]
    exact map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) a e
  simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply, Matrix.smul_apply, e, Finset.smul_sum,
    mul_smul_comm, smul_mul_assoc]

end Alg

theorem herm_smul {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (a : F) (ha : a ≠ 0) :
    IsHermND σ (a • J) := by
  refine ⟨fun i j => by simp [hJ.1], ?_⟩
  have : a • J = (algebraMap F E a) • J := by rw [algebraMap_smul]
  rw [this, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (by simpa using ha)) hJ.2

theorem herm_one {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) :
    IsHermND σ (1 : Matrix (Fin M) (Fin M) E) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem tup_haar {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    (lam : Measure S) (h : lam.IsAddHaarMeasure) (n M : ℕ) : (tupMeas lam n M).IsAddHaarMeasure := by
  unfold tupMeas
  haveI h1 : (Measure.pi fun _ : Fin M => lam).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem sdW_change (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (hR : Nice R) (ψ0 ψ : R → ℂ) (a : F) (ha : a ≠ 0) (h : ∀ x, ψ x = ψ0 (algebraMap F R a * x))
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (lam : Measure (R ⊗[F] E)) (hl : lam.IsAddHaarMeasure) (r : ℝ≥0)
    (hμ : SdW F E σ M 1 R ψ0 1 (r • tupMeas lam 1 M)) :
    SdW F E σ M J R ψ 1
      (NNReal.sqrt (modu (R ⊗[F] E) (inclR R (a • J).det)) • r • tupMeas lam 1 M) := by
  have hJ' := herm_smul σ J hJ a ha
  obtain ⟨h1, h2, -⟩ := GlobalTheory.GaugeEx.nice_tensor F E R hR
  have hdet : (JR (F := F) R (a • J)).det = inclR R (a • J).det := by
    rw [RingHom.map_det]; rfl
  have hu : IsUnit (JR (F := F) R (a • J)).det := by
    rw [hdet]; exact (Ne.isUnit hJ'.2).map _
  have hm := GlobalTheory.T.vectorTupleProductMeasure_two_sided_action (R ⊗[F] E) h1 h2 lam hl 1 M (JR R (a • J)) 1 hu (by simp)
  obtain ⟨hb, -, hone, -⟩ := GlobalTheory.GaugeEx.modu_basic (R ⊗[F] E)
  have hT : lrAct (JR (F := F) R (a • J)) (1 : Matrix (Fin 1) (Fin 1) _) = actHomeo (n := 1) _ hu := by
    funext X; rw [lrAct_one]; rfl
  rw [Matrix.det_one, hone, one_pow, pow_one, mul_one, hT, hdet] at hm
  have hpos := (hb _ hu).1
  rw [hdet] at hpos
  have h3 := GlobalTheory.T.selfDual_sqrt_smul_comp_of_invariant _ (r • tupMeas lam 1 M) (fun X Y => ψ0 (BR R σ 1 X Y)) (actHomeo (n := 1) _ hu)
    _ hpos.ne' (by rw [Measure.map_smul, smul_comm, ← hm]) (fun X Y => by
      show ψ0 (BR R σ 1 X fun c => (JR R (a • J)).mulVec (Y c)) =
        ψ0 (BR R σ 1 (fun c => (JR R (a • J)).mulVec (X c)) Y)
      simp only [BR, hR_one_mulVec, hR_one_mulVec' R σ _ hJ'.1]) hμ
  have h4 : (fun X Y : Fin 1 → Fin M → R ⊗[F] E => ψ (BR R σ J X Y)) =
      fun X Y => ψ0 (BR R σ 1 X (actHomeo (n := 1) _ hu Y)) := by
    funext X Y
    show _ = ψ0 (BR R σ 1 X fun c => (JR R (a • J)).mulVec (Y c))
    rw [h, ← BR_smul]
    simp only [BR, hR_one_mulVec]
  unfold SdW
  rw [h4]
  exact h3

theorem psiInf_mul (F : Type) [Field F] [NumberField F] (ψ0 ψ : AddChar (AF F) ℂ) (a : F)
    (h : ∀ x, ψ x = ψ0 (algebraMap F (AF F) a * x)) (x : Ainf F) :
    psiInf F ψ x = psiInf F ψ0 (algebraMap F (Ainf F) a * x) := by
  unfold psiInf
  rw [h]
  congr 1
  exact Prod.ext rfl (mul_zero (algebraMap F (Af F) a))

theorem psiV_mul (F : Type) [Field F] [NumberField F] (ψ0 ψ : AddChar (AF F) ℂ) (a : F)
    (h : ∀ x, ψ x = ψ0 (algebraMap F (AF F) a * x)) (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) :
    psiV F ψ v x = psiV F ψ0 v (algebraMap F (Fv F v) a * x) := by
  classical
  unfold psiV
  rw [h]
  congr 1
  refine Prod.ext (mul_zero (algebraMap F (Ainf F) a)) ?_
  show algebraMap F (Af F) a * singleV F v x = singleV F v (algebraMap F (Fv F v) a * x)
  apply Subtype.ext
  funext w
  show algebraMap F (Fv F w) a * Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => Fv F w) v x w =
    Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => Fv F w) v (algebraMap F (Fv F v) a * x) w
  by_cases hw : w = v
  · subst hw; simp
  · simp [Pi.single_eq_of_ne hw]

theorem exists_smul_haar {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (μ ν : Measure V) (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ μ = c • ν ∧ (μ = ν → c = 1) := by
  refine ⟨Measure.addHaarScalarFactor μ ν, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne',
    Measure.isAddLeftInvariant_eq_smul μ ν, fun h => ?_⟩
  subst h
  exact Measure.addHaarScalarFactor_self μ

theorem sqrt_prod {ι : Type} (A : ι → ℝ≥0) (a : ℝ≥0) (hA : (Function.mulSupport A).Finite)
    (h : a * ∏ᶠ v, A v = 1) :
    (Function.mulSupport fun v => NNReal.sqrt (A v)).Finite ∧
      NNReal.sqrt a * ∏ᶠ v, NNReal.sqrt (A v) = 1 := by
  refine ⟨hA.subset fun v hv h1 => hv (by simp [h1]), ?_⟩
  have := MonoidHom.map_finprod (NNReal.sqrtHom : ℝ≥0 →*₀ ℝ≥0).toMonoidHom hA
  have h2 : NNReal.sqrt (∏ᶠ v, A v) = ∏ᶠ v, NNReal.sqrt (A v) := this
  rw [← h2, ← NNReal.sqrt_mul, h, NNReal.sqrt_one]

theorem final_prod {ι : Type} (A B r t : ι → ℝ≥0) (a b ri ti : ℝ≥0)
    (hA : (Function.mulSupport A).Finite) (hB : (Function.mulSupport B).Finite)
    (hrt : (Function.mulSupport fun v => r v / t v).Finite)
    (h1 : a * ∏ᶠ v, A v = 1) (h2 : b * ∏ᶠ v, B v = 1) :
    (Function.mulSupport fun v => (A v * r v) / (B v * t v)).Finite ∧
      (a * ri) / (b * ti) * ∏ᶠ v, (A v * r v) / (B v * t v) = ri / ti * ∏ᶠ v, r v / t v := by
  have e : (fun v => (A v * r v) / (B v * t v)) = fun v => (A v / B v) * (r v / t v) := by
    funext v; rw [mul_div_mul_comm]
  have hAB : (Function.mulSupport fun v => A v / B v).Finite :=
    (hA.union hB).subset (Function.mulSupport_div A B)
  rw [e]
  refine ⟨(hAB.union hrt).subset (Function.mulSupport_mul _ _), ?_⟩
  rw [finprod_mul_distrib hAB hrt, finprod_div_distrib hA hB, mul_div_mul_comm, mul_mul_mul_comm,
    ← mul_div_mul_comm, h1, h2, div_one, one_mul]

theorem selfDual_const : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ), ∃ κ : ℝ≥0, κ ≠ 0 ∧ ∀ (ψ : AddChar (AF F) ℂ) (J : Matrix (Fin M) (Fin M) E), IsCharAF F ψ → IsHermND σ J → ∀ (μi : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (νi : Measure (Ainf F)) (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), SdW F E σ M J (Ainf F) (psiInf F ψ) 1 μi → SdR (Ainf F) (psiInf F ψ) νi → (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (μv v)) → (∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)) → ∃ (ri ti : ℝ≥0) (r t : HeightOneSpectrum (𝓞 F) → ℝ≥0), μi = ri • tupMeas s.lamI 1 M ∧ νi = ti • s.nuI ∧ (∀ v, μv v = r v • tupMeas (s.lamV v) 1 M) ∧ (∀ v, νv v = t v • s.nuV v) ∧ ri ≠ 0 ∧ ti ≠ 0 ∧ (∀ v, r v ≠ 0) ∧ (∀ v, t v ≠ 0) ∧ (Function.mulSupport fun v => r v / t v).Finite ∧ ri / ti * ∏ᶠ v, r v / t v = κ := by
  intro F E _ _ _ _ _ σ hCM d b s M
  haveI : IsTotallyReal F := hCM.1
  obtain ⟨ψ0, hψ0⟩ := GlobalTheory.T.exists_nontrivial_adeleChar_trivial_on_totallyReal F
  have h1 := herm_one σ M
  obtain ⟨⟨ν0i, hν0i, -⟩, hWi⟩ := GlobalTheory.T.existsUnique_selfDual_haar_measure_infinite_adeles F E σ hCM ψ0 hψ0
  obtain ⟨μ0i, hμ0i, -⟩ := hWi M 1 h1
  obtain ⟨ri, hri, eri, -⟩ := exists_smul_haar μ0i _ hμ0i.1 (tup_haar s.lamI s.haar_lamI 1 M)
  obtain ⟨ti, hti, eti, -⟩ := exists_smul_haar ν0i _ hν0i.1 s.haar_nuI
  have hr : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : ℝ≥0, c ≠ 0 ∧
      SdW F E σ M 1 (Fv F v) (psiV F ψ0 v) 1 (c • tupMeas (s.lamV v) 1 M) ∧
      (SdW F E σ M 1 (Fv F v) (psiV F ψ0 v) 1 (tupMeas (s.lamV v) 1 M) → c = 1) := by
    intro v
    obtain ⟨μ, hμ, hu⟩ := (GlobalTheory.T.existsUnique_selfDual_measures_finitePlace F E σ hCM ψ0 hψ0 v).2 M 1 h1
    obtain ⟨c, hc, ec, h⟩ := exists_smul_haar μ _ hμ.1 (tup_haar (s.lamV v) (s.haar_lamV v) 1 M)
    exact ⟨c, hc, ec ▸ hμ, fun h' => h (hu _ h').symm⟩
  have ht : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : ℝ≥0, c ≠ 0 ∧
      SdR (Fv F v) (psiV F ψ0 v) (c • s.nuV v) ∧ (SdR (Fv F v) (psiV F ψ0 v) (s.nuV v) → c = 1) := by
    intro v
    obtain ⟨μ, hμ, hu⟩ := (GlobalTheory.T.existsUnique_selfDual_measures_finitePlace F E σ hCM ψ0 hψ0 v).1
    obtain ⟨c, hc, ec, h⟩ := exists_smul_haar μ _ hμ.1 (s.haar_nuV v)
    exact ⟨c, hc, ec ▸ hμ, fun h' => h (hu _ h').symm⟩
  choose r hr0 hrs hr1 using hr
  choose t ht0 hts ht1 using ht
  rw [eri] at hμ0i
  rw [eti] at hν0i
  have hfin : (Function.mulSupport fun v => r v / t v).Finite := by
    have := Filter.eventually_cofinite.1 (GlobalTheory.T.eventually_normalizedLocalHaar_selfDual F E σ hCM d b s ψ0 hψ0 M 1 h1)
    refine this.subset fun v hv h => hv ?_
    show r v / t v = 1
    rw [hr1 v h.2, ht1 v h.1, div_one]
  refine ⟨ri / ti * ∏ᶠ v, r v / t v, mul_ne_zero (div_ne_zero hri hti) ?_, ?_⟩
  · exact finprod_induction (fun x : ℝ≥0 => x ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero)
      fun v => div_ne_zero (hr0 v) (ht0 v)
  intro ψ J hψ hJ μi νi μv νv hμi hνi hμv hνv
  obtain ⟨a, ha, hψa⟩ := GlobalTheory.T.exists_ne_zero_adele_char_eq_comp_mul_totally_real F ψ0 ψ hψ0 hψ
  have hJ' := herm_smul σ J hJ a ha
  obtain ⟨hNi, hNv⟩ := GlobalTheory.GaugeEx.nice_ainf_fv F
  obtain ⟨hB, hB1⟩ := GlobalTheory.GaugeProdFormula.prod_modu_eq_one F a ha
  obtain ⟨hA, hA1⟩ := GlobalTheory.T.product_formula_haarModulus_cmField_element F E σ hCM _ hJ'.2
  obtain ⟨hB', hB1'⟩ := sqrt_prod _ _ hB hB1
  obtain ⟨hA', hA1'⟩ := sqrt_prod _ _ hA hA1
  obtain ⟨hf, he⟩ := final_prod _ _ r t _ _ ri ti hA' hB' hfin hA1' hB1'
  refine ⟨_, _, _, _, ?_, ?_, fun v => ?_, fun v => ?_, ?_, ?_, fun v => ?_, fun v => ?_, hf, he⟩
  · rw [mul_smul]
    exact ((GlobalTheory.T.existsUnique_selfDual_haar_measure_infinite_adeles F E σ hCM ψ hψ).2 M J hJ).unique hμi
      (sdW_change F E σ _ hNi _ _ a ha (psiInf_mul F ψ0 ψ a hψa) M J hJ _ s.haar_lamI ri hμ0i)
  · rw [mul_smul]
    exact (GlobalTheory.T.existsUnique_selfDual_haar_measure_infinite_adeles F E σ hCM ψ hψ).1.unique hνi
      (sdR_change _ _ _ _ ((Ne.isUnit ha).map _) (psiInf_mul F ψ0 ψ a hψa) _ hν0i)
  · rw [mul_smul]
    exact ((GlobalTheory.T.existsUnique_selfDual_measures_finitePlace F E σ hCM ψ hψ v).2 M J hJ).unique (hμv v)
      (sdW_change F E σ _ (hNv v) _ _ a ha (psiV_mul F ψ0 ψ a hψa v) M J hJ _ (s.haar_lamV v) _ (hrs v))
  · rw [mul_smul]
    exact (GlobalTheory.T.existsUnique_selfDual_measures_finitePlace F E σ hCM ψ hψ v).1.unique (hνv v)
      (sdR_change _ _ _ _ ((Ne.isUnit ha).map _) (psiV_mul F ψ0 ψ a hψa v) _ (hts v))
  · exact mul_ne_zero (left_ne_zero_of_mul_eq_one hA1') hri
  · exact mul_ne_zero (left_ne_zero_of_mul_eq_one hB1') hti
  · refine mul_ne_zero ?_ (hr0 v)
    rw [Ne, NNReal.sqrt_eq_zero]
    exact (((GlobalTheory.GaugeEx.modu_basic _).1 _ ((Ne.isUnit hJ'.2).map _)).1).ne'
  · refine mul_ne_zero ?_ (ht0 v)
    rw [Ne, NNReal.sqrt_eq_zero]
    exact (((GlobalTheory.GaugeEx.modu_basic _).1 _ ((Ne.isUnit ha).map _)).1).ne'

end GlobalTheory.GaugeSdMain
