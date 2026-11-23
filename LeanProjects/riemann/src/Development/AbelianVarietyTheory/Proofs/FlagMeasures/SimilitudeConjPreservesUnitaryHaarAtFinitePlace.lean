import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnitaryGroupStabilizersUnimodularFinitePlac
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFlagDualBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarFrameStabiliserCompatibleFibreStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureUnitriangularInvariantStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.ConjStabiliserHaar

section Abstract

variable {G X : Type} [Group G] [MulAction G X]

def conjInv (x0 : X) (s : G) (h1 : ∀ h ∈ MulAction.stabilizer G x0, s⁻¹ * h * s ∈ MulAction.stabilizer G x0)
    (h2 : ∀ h ∈ MulAction.stabilizer G x0, s * h * s⁻¹ ∈ MulAction.stabilizer G x0) :
    MulAction.stabilizer G x0 ≃* MulAction.stabilizer G x0 where
  toFun h := ⟨s⁻¹ * h * s, h1 h h.2⟩
  invFun h := ⟨s * h * s⁻¹, h2 h h.2⟩
  left_inv h := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv h := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace X]

theorem conj_map_eq (x0 : X) (hcl : IsClosed (MulAction.stabilizer G x0 : Set G))
    (μG : Measure G) [μG.IsHaarMeasure] [μG.IsMulRightInvariant] (ρ : Measure X)
    (μ1 : Measure (MulAction.stabilizer G x0)) [μ1.IsHaarMeasure]
    (hw : ∀ f : G → ℝ≥0∞, Measurable f → ∀ sec : X → G,
      (∀ y, (∃ g : G, g • x0 = y) → sec y • x0 = y) →
      ∫⁻ g, f g ∂μG = ∫⁻ y, ∫⁻ h', f (sec y * (h' : G)) ∂μ1 ∂ρ)
    (R : X ≃ᵐ X) (hR : ∀ (g : G) (x : X), R (g • x) = g • R x) (hρ : ρ.map R = ρ)
    (s : G) (hs : s • x0 = R x0)
    (h1 : ∀ h ∈ MulAction.stabilizer G x0, s⁻¹ * h * s ∈ MulAction.stabilizer G x0)
    (h2 : ∀ h ∈ MulAction.stabilizer G x0, s * h * s⁻¹ ∈ MulAction.stabilizer G x0) :
    μ1.map (conjInv x0 s h1 h2) = μ1 := by
  haveI : LocallyCompactSpace (MulAction.stabilizer G x0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (MulAction.stabilizer G x0) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  set e := conjInv x0 s h1 h2 with he
  have hec : Continuous e := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hes : Continuous e.symm := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  haveI : (μ1.map e).IsHaarMeasure := e.isHaarMeasure_map μ1 hec hes
  have hc : μ1.map e = Measure.haarScalarFactor (μ1.map e) μ1 • μ1 :=
    Measure.isMulLeftInvariant_eq_smul _ _
  set c : NNReal := Measure.haarScalarFactor (μ1.map e) μ1 with hcdef

  classical
  let sec : X → G := fun y => if h : ∃ g : G, g • x0 = y then h.choose else 1
  have hsec : ∀ y, (∃ g : G, g • x0 = y) → sec y • x0 = y := by
    intro y h
    simp only [sec, dif_pos h]
    exact h.choose_spec
  have horb : ∀ y, (∃ g : G, g • x0 = y) → ∃ g : G, g • x0 = R.symm y := by
    rintro y ⟨g, rfl⟩
    refine ⟨g * s⁻¹, ?_⟩
    apply R.injective
    rw [MeasurableEquiv.apply_symm_apply, hR, mul_smul, ← hs, inv_smul_smul]
  let sec' : X → G := fun y => sec (R.symm y) * s
  have hsec' : ∀ y, (∃ g : G, g • x0 = y) → sec' y • x0 = y := by
    intro y hy
    simp only [sec', mul_smul]
    rw [hs, ← hR, hsec _ (horb y hy), MeasurableEquiv.apply_symm_apply]
  have key : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = c * ∫⁻ g, f g ∂μG := by
    intro f hf
    have hfs : Measurable (fun g => f (g * s)) := hf.comp (measurable_mul_const s)
    have hA : ∫⁻ g, f (g * s) ∂μG = ∫⁻ g, f g ∂μG := lintegral_mul_right_eq_self f s
    have hB := hw _ hfs sec hsec
    have hC := hw f hf sec' hsec'
    have hinner : ∀ y, ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * (h' : G) * s) ∂μ1 =
        c * ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * s * (h' : G)) ∂μ1 := by
      intro y
      have hm : Measurable (fun h' : MulAction.stabilizer G x0 => f (sec y * s * (h' : G))) :=
        hf.comp ((measurable_const_mul _).comp measurable_subtype_coe)
      have h3 : ∫⁻ h', f (sec y * s * (h' : G)) ∂(μ1.map e) =
          ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * (h' : G) * s) ∂μ1 := by
        rw [lintegral_map hm hec.measurable]
        refine lintegral_congr fun h => ?_
        congr 1
        show sec y * s * (s⁻¹ * (h : G) * s) = _
        group
      rw [← h3, hc, lintegral_smul_measure]
      rfl
    have hD : ∫⁻ y, ∫⁻ h' : MulAction.stabilizer G x0, f (sec' y * (h' : G)) ∂μ1 ∂ρ =
        ∫⁻ y, ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * s * (h' : G)) ∂μ1 ∂ρ := by
      conv_lhs => rw [← hρ]
      rw [lintegral_map_equiv]
      simp only [sec', MeasurableEquiv.symm_apply_apply]
    calc ∫⁻ g, f g ∂μG = ∫⁻ g, f (g * s) ∂μG := hA.symm
      _ = ∫⁻ y, ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * (h' : G) * s) ∂μ1 ∂ρ := hB
      _ = ∫⁻ y, c * ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * s * (h' : G)) ∂μ1 ∂ρ := by
          simp only [hinner]
      _ = c * ∫⁻ y, ∫⁻ h' : MulAction.stabilizer G x0, f (sec y * s * (h' : G)) ∂μ1 ∂ρ :=
          lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = c * ∫⁻ g, f g ∂μG := by rw [hC, hD]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have h4 := key (K.indicator 1) (measurable_one.indicator hKm)
  rw [lintegral_indicator_one hKm] at h4
  have hpos : μG K ≠ 0 := (Measure.measure_pos_of_mem_nhds μG hK1).ne'
  have hfin : μG K ≠ ∞ := hK.measure_lt_top.ne
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have h5 : (1 : ℝ≥0∞) * μG K = c * μG K := by rw [one_mul]; exact h4
    exact ((ENNReal.mul_left_inj hpos hfin).1 h5).symm
  have hc2 : c = 1 := by exact_mod_cast hc1
  rw [hc, hc2, one_smul]

theorem conj_lintegral_eq (x0 : X) (hcl : IsClosed (MulAction.stabilizer G x0 : Set G))
    (μG : Measure G) [μG.IsHaarMeasure] [μG.IsMulRightInvariant] (ρ : Measure X)
    (μ1 : Measure (MulAction.stabilizer G x0)) (hμ1 : μ1.IsHaarMeasure)
    (hw : ∀ f : G → ℝ≥0∞, Measurable f → ∀ sec : X → G,
      (∀ y, (∃ g : G, g • x0 = y) → sec y • x0 = y) →
      ∫⁻ g, f g ∂μG = ∫⁻ y, ∫⁻ h', f (sec y * (h' : G)) ∂μ1 ∂ρ)
    (R : X ≃ᵐ X) (hR : ∀ (g : G) (x : X), R (g • x) = g • R x) (hρ : ρ.map R = ρ)
    (s : G) (hs : s • x0 = R x0)
    (μ0 : Measure (MulAction.stabilizer G x0)) (hμ0 : μ0.IsHaarMeasure)
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ h : MulAction.stabilizer G x0, f (s * (h : G) * s⁻¹) ∂μ0 =
      ∫⁻ h : MulAction.stabilizer G x0, f (h : G) ∂μ0 := by
  haveI := hμ1
  haveI := hμ0
  haveI : LocallyCompactSpace (MulAction.stabilizer G x0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (MulAction.stabilizer G x0) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have h1 : ∀ h ∈ MulAction.stabilizer G x0, s⁻¹ * h * s ∈ MulAction.stabilizer G x0 := by
    intro h hh
    rw [MulAction.mem_stabilizer_iff] at hh ⊢
    rw [mul_smul, mul_smul, hs, ← hR, hh, ← hs, inv_smul_smul]
  have h2 : ∀ h ∈ MulAction.stabilizer G x0, s * h * s⁻¹ ∈ MulAction.stabilizer G x0 := by
    intro h hh
    rw [MulAction.mem_stabilizer_iff] at hh ⊢
    apply R.injective
    rw [hR, ← hs, mul_smul, mul_smul, inv_smul_smul, hh]
  have hmap := conj_map_eq x0 hcl μG ρ μ1 hw R hR hρ s hs h1 h2
  have hc : μ0 = Measure.haarScalarFactor μ0 μ1 • μ1 := Measure.isMulLeftInvariant_eq_smul _ _
  have hm : Measurable (fun h : MulAction.stabilizer G x0 => f (s * (h : G) * s⁻¹)) :=
    hf.comp (((measurable_const_mul s).comp measurable_subtype_coe).mul_const _)
  have hec : Continuous (conjInv x0 s h1 h2) := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  have h3 : ∫⁻ h : MulAction.stabilizer G x0, f (s * (h : G) * s⁻¹) ∂μ1 =
      ∫⁻ h : MulAction.stabilizer G x0, f (h : G) ∂μ1 := by
    conv_lhs => rw [← hmap]
    rw [lintegral_map hm hec.measurable]
    refine lintegral_congr fun h => ?_
    congr 1
    show s * (s⁻¹ * (h : G) * s) * s⁻¹ = _
    group
  rw [hc, lintegral_smul_measure, lintegral_smul_measure, h3]

end Abstract

section Tuples

variable {A : Type} [CommRing A] {n a : ℕ}

def mv (u : Matrix (Fin a) (Fin a) A) (X : Fin a → Fin n → A) : Fin a → Fin n → A :=
  fun b => ∑ c, u c b • X c

theorem mv_mv (u w : Matrix (Fin a) (Fin a) A) (X : Fin a → Fin n → A) :
    mv w (mv u X) = mv (u * w) X := by
  funext b
  simp only [mv, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by rw [mul_comm]

theorem mv_one (X : Fin a → Fin n → A) : mv 1 X = X := by
  funext b
  simp [mv, Matrix.one_apply]

theorem continuous_mv [TopologicalSpace A] [IsTopologicalRing A] (u : Matrix (Fin a) (Fin a) A) :
    Continuous (mv (n := n) u) :=
  continuous_pi fun b => continuous_finset_sum _ fun c _ => (continuous_apply c).const_smul (u c b)

theorem det_unitriangular (u : Matrix (Fin a) (Fin a) A) (h1 : ∀ i, u i i = 1)
    (h2 : ∀ i j, j < i → u i j = 0) : u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h2 i j hij)]
  simp [h1]

noncomputable def mvHomeo [TopologicalSpace A] [IsTopologicalRing A] (u : Matrix (Fin a) (Fin a) A)
    (hu : IsUnit u.det) : (Fin a → Fin n → A) ≃ₜ (Fin a → Fin n → A) where
  toFun := mv u
  invFun := mv u⁻¹
  left_inv X := by rw [mv_mv, Matrix.mul_nonsing_inv u hu, mv_one]
  right_inv X := by rw [mv_mv, Matrix.nonsing_inv_mul u hu, mv_one]
  continuous_toFun := continuous_mv u
  continuous_invFun := continuous_mv _

end Tuples

section Gram

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem smul_mv [TopologicalSpace R] (g : HA R σ J) (u : Matrix (Fin a) (Fin a) (R ⊗[F] E))
    (X : Fin a → Fin n → R ⊗[F] E) : g • mv u X = mv u (g • X) := by
  funext b
  show lin R σ J g (∑ c, u c b • X c) = ∑ c, u c b • lin R σ J g (X c)
  rw [map_sum]
  simp only [map_smul]

theorem hR_sum_left {ι : Type} (t : Finset ι) (x : ι → Fin n → R ⊗[F] E) (y : Fin n → R ⊗[F] E) :
    hR R σ J (∑ i ∈ t, x i) y = ∑ i ∈ t, hR R σ J (x i) y := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [hR_zero_left]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hR_add_left, ih]

theorem hR_sum_right {ι : Type} (t : Finset ι) (x : Fin n → R ⊗[F] E) (y : ι → Fin n → R ⊗[F] E) :
    hR R σ J x (∑ i ∈ t, y i) = ∑ i ∈ t, hR R σ J x (y i) :=
  map_sum (GlobalTheory.UnitriangularCoeff.hRight R σ J x) y t

theorem gramR_mv (u : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (X : Fin a → Fin n → R ⊗[F] E) :
    gramR R σ J (mv u X) = (u.map (sigR R σ)).transpose * gramR R σ J X * u := by
  ext i j
  simp only [gramR, mv, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hR_sum_left]
  simp only [hR_smul_left, hR_sum_right, GlobalTheory.UnitriangularCoeff.hR_smul_right, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem gramR_ratTup (X : Fin a → Fin n → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR R) := by
  ext i j
  simp [gramR, gramE, hE, hR, Formalism.UG.hform, ratTup, JR, sigR, inclR, Matrix.map_apply, mul_assoc]

theorem gramR_smul [TopologicalSpace R] (g : HA R σ J) (X : Fin a → Fin n → R ⊗[F] E) :
    gramR R σ J (g • X) = gramR R σ J X := by
  ext i j
  exact hR_lin g (X i) (X j)

end Gram

theorem conj_preserves_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ (hT : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j), ∀ (μ : Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (r + 1))), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure → ∀ s ∈ Ssub (Fv F v) σ J P, ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∫⁻ h, f (s * (h : HA (Fv F v) σ J) * s⁻¹) ∂μ0 = ∫⁻ h, f (h : HA (Fv F v) σ J) ∂μ0 := by
  intro F E _ _ _ _ _ σ hCM n J hJ v r P T hP hT μ ν hμ hν fib hfib μ0 hμ0 s hs f hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI := h5
  haveI := h6
  haveI := h7
  haveI := h8
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (HA (Fv F v) σ J) := ⟨rfl⟩
  obtain ⟨⟨-, -, -, -, -, ⟨μG, hμG⟩, hright⟩, -⟩ :=
    GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion F E σ hCM n J hJ v
  haveI := hμG
  haveI := hright μG hμG
  obtain ⟨μ1, hμ1, -, hw⟩ := GlobalTheory.T.exists_haar_frameStabiliser_compatible_fibre F E σ hCM n J hJ v r P T hP hT μ ν hμ hν fib hfib μG hμG
  set x0 := ratTup (F := F) (Fv F v) (F0 P) with hx0def
  set S := hermOf (Fv F v) σ (gramE σ J (F0 P)) hT with hS
  have hgram : gramR (Fv F v) σ J x0 = (S : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :=
    gramR_ratTup (Fv F v) σ J (F0 P)
  obtain ⟨co, -, hco⟩ := GlobalTheory.UnitriangularCoeff.exists_coeff F E σ hCM n J hJ v r P T hP
  let u : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E) := fun a b =>
    if a = b then 1 else if h : a < b then co ⟨s, hs⟩ ⟨(a, b), h⟩ else 0
  have hu1 : ∀ i, u i i = 1 := fun i => by simp [u]
  have hu2 : ∀ i j, j < i → u i j = 0 := by
    intro i j hij
    simp [u, hij.ne', not_lt.2 hij.le]
  have hsu : s • x0 = mv u x0 := by
    funext b
    exact (hco ⟨s, hs⟩ (co ⟨s, hs⟩)).1 rfl b
  have hg : (u.map (sigR (Fv F v) σ)).transpose *
      (S : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) * u =
      (S : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) := by
    rw [← hgram, ← gramR_mv, ← hsu, gramR_smul]
  have hfu := GlobalTheory.T.gramMap_fibreMeasure_unitriangular_invariant F E σ hCM n J hJ v (r + 1) μ ν hμ hν fib hfib S u hu1 hu2 hg
  have hdet : IsUnit u.det := by
    rw [det_unitriangular u hu1 hu2]
    exact isUnit_one
  let Rm := (mvHomeo (n := n) u hdet).toMeasurableEquiv
  have hcl : IsClosed (MulAction.stabilizer (HA (Fv F v) σ J) x0 : Set (HA (Fv F v) σ J)) := by
    have hc : Continuous (fun g : HA (Fv F v) σ J => g • x0) :=
      (h9 (r + 1)).2.comp (Continuous.prodMk continuous_id continuous_const)
    exact isClosed_singleton.preimage hc
  exact conj_lintegral_eq x0 hcl μG (fib S) μ1 hμ1 hw Rm (fun g x => (smul_mv (Fv F v) σ J g u x).symm)
    hfu s hsu μ0 hμ0 f hf

end GlobalTheory.ConjStabiliserHaar
