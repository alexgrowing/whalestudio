import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponentsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorPropertiesStatement

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.GaugeEx.ProdTransport

theorem tprod_tail_split {ι : Type*} [DecidableEq ι] (f : ι → ℝ) (hf : Summable fun v => |f v - 1|)
    (S S' : Finset ι) (h : S ⊆ S') :
    ∏' v : {v // v ∉ S}, f v.1 = (∏ v ∈ S' \ S, f v) * ∏' v : {v // v ∉ S'}, f v.1 := by
  have hm : Multipliable fun v : {v // v ∉ S'} => f v.1 := by
    have h1 : Summable fun v : {v // v ∉ S'} => ‖f v.1 - 1‖ := hf.subtype _
    simpa using multipliable_one_add_of_summable h1
  have e1 : ∀ T : Finset ι, ∀ a, HasProd (fun v : {v // v ∉ T} => f v.1) a ↔
      HasProd (Set.mulIndicator {v | v ∉ T} f) a := fun T a =>
    hasProd_subtype_iff_mulIndicator (s := {v | v ∉ T})
  have h2 := (e1 S' _).1 hm.hasProd
  have h3 : HasProd (Set.mulIndicator (↑(S' \ S) : Set ι) f) (∏ v ∈ S' \ S, f v) :=
    hasProd_subtype_iff_mulIndicator.1 ((S' \ S).hasProd f)
  have h4 := h3.mul h2
  refine ((e1 S _).2 ?_).tprod_eq
  convert h4 using 1
  funext v
  by_cases h5 : v ∈ S
  · simp [Set.mulIndicator, h5, h h5]
  · by_cases h6 : v ∈ S' <;> simp [Set.mulIndicator, h5, h6]

theorem abstract_transport {ι X Xi : Type*} {Xv : ι → Type*} [MeasurableSpace X] [MeasurableSpace Xi]
    [∀ v, MeasurableSpace (Xv v)] (pI : X → Xi) (pv : ∀ v, X → Xv v) (hpv : ∀ v, Measurable (pv v))
    (L : ∀ v, Set (Xv v)) (hL : ∀ v, MeasurableSet (L v))
    (T : X ≃ᵐ X) (Ti : Xi → Xi) (Tv : ∀ v, Xv v → Xv v) (hTi : Measurable Ti)
    (hTv : ∀ v, Measurable (Tv v)) (hci : ∀ x, pI (T x) = Ti (pI x))
    (hcv : ∀ v x, pv v (T x) = Tv v (pv v x)) (S₀ : Finset ι) (hS₀ : ∀ v ∉ S₀, Tv v ⁻¹' L v = L v)
    (ν : Measure X) (mi : Measure Xi) (mv : ∀ v, Measure (Xv v))
    (hfin : ∀ v, mv v (Tv v ⁻¹' L v) ≠ ∞)
    (hsum : Summable fun v => |((mv v).map (Tv v) (L v)).toReal - 1|)
    (H : ∀ (S : Finset ι) (fi : Xi → ℝ≥0∞) (fv : ∀ v, Xv v → ℝ≥0∞),
      Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ x in {x | ∀ v ∉ S, pv v x ∈ L v}, fi (pI x) * ∏ v ∈ S, fv v (pv v x) ∂ν =
        (∫⁻ y, fi y ∂mi) * (∏ v ∈ S, ∫⁻ y, fv v y ∂(mv v)) *
          ENNReal.ofReal (∏' v : {v // v ∉ S}, (mv v.1 (L v.1)).toReal))
    (S : Finset ι) (fi : Xi → ℝ≥0∞) (fv : ∀ v, Xv v → ℝ≥0∞)
    (hfi : Measurable fi) (hfv : ∀ v, Measurable (fv v)) :
    ∫⁻ x in {x | ∀ v ∉ S, pv v x ∈ L v}, fi (pI x) * ∏ v ∈ S, fv v (pv v x) ∂(ν.map T) =
      (∫⁻ y, fi y ∂(mi.map Ti)) * (∏ v ∈ S, ∫⁻ y, fv v y ∂((mv v).map (Tv v))) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, ((mv v.1).map (Tv v.1) (L v.1)).toReal) := by
  classical
  have hsub : S ⊆ S ∪ S₀ := Finset.subset_union_left
  have hTL : ∀ v, MeasurableSet (Tv v ⁻¹' L v) := fun v => hTv v (hL v)
  let gv : ∀ v, Xv v → ℝ≥0∞ := fun v =>
    if v ∈ S then fv v ∘ Tv v else (Tv v ⁻¹' L v).indicator 1
  have hgv : ∀ v, Measurable (gv v) := by
    intro v
    by_cases h : v ∈ S
    · simpa [gv, h] using (hfv v).comp (hTv v)
    · simpa [gv, h] using (measurable_one.indicator (hTL v))
  have key := H (S ∪ S₀) (fi ∘ Ti) gv (hfi.comp hTi) hgv
  let B : Set X := {x | ∀ v ∈ (S ∪ S₀) \ S, pv v x ∈ Tv v ⁻¹' L v}
  have hB : MeasurableSet B := by
    have : B = ⋂ v ∈ (S ∪ S₀) \ S, pv v ⁻¹' (Tv v ⁻¹' L v) := by
      ext x; simp only [B, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [this]
    exact Finset.measurableSet_biInter _ fun v _ => hpv v (hTL v)
  have hset : T ⁻¹' {x | ∀ v ∉ S, pv v x ∈ L v} = B ∩ {x | ∀ v ∉ S ∪ S₀, pv v x ∈ L v} := by
    ext x
    simp only [B, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff, hcv]
    constructor
    · intro h
      refine ⟨fun v hv => h v (Finset.mem_sdiff.1 hv).2, fun v hv => ?_⟩
      rw [← hS₀ v fun h' => hv (Finset.mem_union_right _ h')]
      exact h v fun h' => hv (hsub h')
    · rintro ⟨h1, h2⟩ v hv
      by_cases h : v ∈ S ∪ S₀
      · exact h1 v (Finset.mem_sdiff.2 ⟨h, hv⟩)
      · have := h2 v h
        rwa [← hS₀ v fun h' => h (Finset.mem_union_right _ h')] at this
  have hl : ∫⁻ x in {x | ∀ v ∉ S, pv v x ∈ L v}, fi (pI x) * ∏ v ∈ S, fv v (pv v x) ∂(ν.map T) =
      ∫⁻ x in {x | ∀ v ∉ S ∪ S₀, pv v x ∈ L v},
        (fi ∘ Ti) (pI x) * ∏ v ∈ S ∪ S₀, gv v (pv v x) ∂ν := by
    rw [T.restrict_map, lintegral_map_equiv, hset, ← Measure.restrict_restrict hB,
      ← lintegral_indicator hB]
    refine lintegral_congr fun x => ?_
    rw [← Finset.prod_sdiff hsub]
    have e1 : ∏ v ∈ S, gv v (pv v x) = ∏ v ∈ S, fv v (pv v (T x)) :=
      Finset.prod_congr rfl fun v hv => by simp [gv, hv, hcv]
    rw [e1]
    by_cases hx : x ∈ B
    · have e2 : ∏ v ∈ (S ∪ S₀) \ S, gv v (pv v x) = 1 :=
        Finset.prod_eq_one fun v hv => by
          simp only [gv, if_neg (Finset.mem_sdiff.1 hv).2]
          exact Set.indicator_of_mem (hx v hv) _
      rw [Set.indicator_of_mem hx, e2, one_mul, hci]; rfl
    · rw [Set.indicator_of_notMem hx]
      simp only [B, Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨v, hv, hv'⟩ := hx
      have e2 : ∏ v ∈ (S ∪ S₀) \ S, gv v (pv v x) = 0 :=
        Finset.prod_eq_zero hv (by
          simp only [gv, if_neg (Finset.mem_sdiff.1 hv).2]
          exact Set.indicator_of_notMem hv' _)
      rw [e2, zero_mul, mul_zero]
  rw [hl, key, tprod_tail_split _ hsum S (S ∪ S₀) hsub, ← Finset.prod_sdiff hsub,
    ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => ENNReal.toReal_nonneg), lintegral_map hfi hTi]
  have e1 : ∏ v ∈ S, ∫⁻ y, gv v y ∂(mv v) = ∏ v ∈ S, ∫⁻ y, fv v y ∂((mv v).map (Tv v)) :=
    Finset.prod_congr rfl fun v hv => by
      rw [lintegral_map (hfv v) (hTv v)]; simp [gv, hv]
  have e2 : ∏ v ∈ (S ∪ S₀) \ S, ∫⁻ y, gv v y ∂(mv v) =
      ∏ v ∈ (S ∪ S₀) \ S, ENNReal.ofReal ((mv v).map (Tv v) (L v)).toReal :=
    Finset.prod_congr rfl fun v hv => by
      simp only [gv, if_neg (Finset.mem_sdiff.1 hv).2]
      rw [lintegral_indicator_one (hTL v), Measure.map_apply (hTv v) (hL v),
        ENNReal.ofReal_toReal (hfin v)]
  have e3 : ∏' v : {v // v ∉ S ∪ S₀}, (mv v.1 (L v.1)).toReal =
      ∏' v : {v // v ∉ S ∪ S₀}, ((mv v.1).map (Tv v.1) (L v.1)).toReal :=
    tprod_congr fun v => by
      rw [Measure.map_apply (hTv v) (hL v), hS₀ v.1 fun h' => v.2 (Finset.mem_union_right _ h')]
  rw [e1, e2, e3]
  simp only [Function.comp]
  ring

section Lr
variable {S : Type} [CommRing S] {n M : ℕ}

theorem lrAct_eq (g : Matrix (Fin M) (Fin M) S) (γ : Matrix (Fin n) (Fin n) S)
    (X : Fin n → Fin M → S) :
    lrAct g γ X = fun a i => (g * (Matrix.of X).transpose * γ) i a := by
  funext a i
  rw [Matrix.mul_assoc]
  simp [lrAct, Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem lrAct_lrAct (g g' : Matrix (Fin M) (Fin M) S) (γ γ' : Matrix (Fin n) (Fin n) S)
    (hg : g' * g = 1) (hγ : γ * γ' = 1) (X : Fin n → Fin M → S) :
    lrAct g' γ' (lrAct g γ X) = X := by
  rw [lrAct_eq, lrAct_eq]
  have : (Matrix.of fun a i => (g * (Matrix.of X).transpose * γ) i a).transpose =
      g * (Matrix.of X).transpose * γ := by ext; rfl
  rw [this]
  have : g' * (g * (Matrix.of X).transpose * γ) * γ' = (Matrix.of X).transpose := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg, Matrix.one_mul, Matrix.mul_assoc, hγ,
      Matrix.mul_one]
  rw [this]; rfl

theorem map_lrAct {S' : Type} [CommRing S'] (φ : S →+* S') (g : Matrix (Fin M) (Fin M) S)
    (γ : Matrix (Fin n) (Fin n) S) (X : Fin n → Fin M → S) :
    (fun a i => φ (lrAct g γ X a i)) = lrAct (g.map φ) (γ.map φ) fun a i => φ (X a i) := by
  funext a i
  simp [lrAct, Matrix.mulVec, dotProduct]

theorem continuous_lrAct [TopologicalSpace S] [IsTopologicalRing S] (g : Matrix (Fin M) (Fin M) S)
    (γ : Matrix (Fin n) (Fin n) S) : Continuous (lrAct g γ) := by
  unfold lrAct Matrix.mulVec dotProduct
  fun_prop

def lrHomeo [TopologicalSpace S] [IsTopologicalRing S] (g : GL (Fin M) S) (γ : GL (Fin n) S) :
    (Fin n → Fin M → S) ≃ₜ (Fin n → Fin M → S) where
  toFun := lrAct g.val γ.val
  invFun := lrAct g⁻¹.val γ⁻¹.val
  left_inv := lrAct_lrAct _ _ _ _ g.inv_mul γ.mul_inv
  right_inv := lrAct_lrAct _ _ _ _ g.mul_inv γ.inv_mul
  continuous_toFun := continuous_lrAct _ _
  continuous_invFun := continuous_lrAct _ _

theorem lrAct_mem (A : AddSubmonoid S) (hA : ∀ y ∈ A, ∀ z ∈ A, y * z ∈ A)
    (g : Matrix (Fin M) (Fin M) S) (γ : Matrix (Fin n) (Fin n) S) (hg : ∀ i j, g i j ∈ A)
    (hγ : ∀ i j, γ i j ∈ A) (X : Fin n → Fin M → S) (hX : ∀ a i, X a i ∈ A) (a : Fin n) (i : Fin M) :
    lrAct g γ X a i ∈ A := by
  change ∑ j, g i j * ∑ c, X c j * γ c a ∈ A
  exact A.sum_mem fun _ _ => hA _ (hg _ _) _ (A.sum_mem fun _ _ => hA _ (hX _ _) _ (hγ _ _))

theorem finiteOnCompacts_map {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : Y ≃ₜ Y) (m : Measure Y) (hm : IsFiniteMeasureOnCompacts m) :
    IsFiniteMeasureOnCompacts (m.map e) where
  lt_top_of_isCompact K hK := by
    have := e.toMeasurableEquiv.map_apply (μ := m) K
    rw [show m.map e K = m (e ⁻¹' K) from this]
    exact (e.isCompact_preimage.2 hK).measure_lt_top

end Lr

def intVAdd {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : AddSubmonoid (Fv F v ⊗[F] E) where
  carrier := intV b v
  zero_mem' := fun k => by simp
  add_mem' := fun {x y} hx hy k => by
    rw [map_add, Finsupp.add_apply]
    exact add_mem (hx k) (hy k)

theorem isProd_map_lrAct : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : GL (Fin M) (AF F ⊗[F] E)) (γ : GL (Fin n) (AF F ⊗[F] E)), IsProd b ν mi mv → IsProd b (ν.map (lrAct g.val γ.val)) (mi.map (lrAct (g.val.map prInf) (γ.val.map prInf))) (fun v => (mv v).map (lrAct (g.val.map (prV v)) (γ.val.map (prV v)))) := by
  intro F E _ _ _ _ _ d b n M ν mi mv g γ ⟨⟨hmi, hmv, hsum⟩, H⟩
  classical
  obtain ⟨-, -, -, hcv⟩ := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M
  obtain ⟨hco, hsr, hz, -⟩ := GlobalTheory.T.integralPointsFinitePlaceTensor_properties F E (AlgHom.id F E) d b
  let eI := lrHomeo (Matrix.GeneralLinearGroup.map (prInf (F := F) (E := E)) g)
    (Matrix.GeneralLinearGroup.map (prInf (F := F) (E := E)) γ)
  let eV := fun v : HeightOneSpectrum (𝓞 F) =>
    lrHomeo (Matrix.GeneralLinearGroup.map (prV (F := F) (E := E) v) g)
      (Matrix.GeneralLinearGroup.map (prV (F := F) (E := E) v) γ)
  have hlat : ∀ v : HeightOneSpectrum (𝓞 F), (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
      Set.univ.pi fun _ => Set.univ.pi fun _ => intV b v := fun v => by
    ext Y; simp only [mem_latV_iff, Set.mem_univ_pi]
  have hlc : ∀ v : HeightOneSpectrum (𝓞 F),
      IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := fun v => by
    rw [hlat]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => (hco v).1
  have hL : ∀ v : HeightOneSpectrum (𝓞 F),
      MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := fun v =>
    (hlc v).isClosed.measurableSet
  have hmat : ∀ {k : ℕ} (A : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)),
      ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, prV v (A i j) ∈ intV b v := fun A =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hz _
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, eV v ⁻¹' latV b v = latV b v := by
    filter_upwards [hsr, hmat g.val, hmat γ.val, hmat g⁻¹.val, hmat γ⁻¹.val] with v h0 h1 h2 h3 h4
    ext Y
    constructor
    · intro hY
      have := lrAct_mem (intVAdd b v) h0.2.1 (g⁻¹.val.map (prV v)) (γ⁻¹.val.map (prV v)) h3 h4 _ hY
      have e : lrAct (g⁻¹.val.map (prV v)) (γ⁻¹.val.map (prV v)) (eV v Y) = Y := by
        refine lrAct_lrAct (g.val.map (prV v)) _ (γ.val.map (prV v)) _ ?_ ?_ Y
        · rw [← Matrix.map_mul, g.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        · rw [← Matrix.map_mul, γ.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [e] at this
      exact this
    · intro hY
      exact lrAct_mem (intVAdd b v) h0.2.1 (g.val.map (prV v)) (γ.val.map (prV v)) h1 h2 _ hY
  have hfinS := Filter.eventually_cofinite.1 hev
  have hS₀ : ∀ v ∉ hfinS.toFinset, eV v ⁻¹' latV b v = latV b v := fun v hv => by
    simpa using hv
  have hsum' : Summable fun v => |((mv v).map (eV v) (latV b v)).toReal - 1| := by
    refine (summable_congr_cofinite ?_).1 hsum
    filter_upwards [hev] with v hv
    rw [Measure.map_apply (eV v).continuous.measurable (hL v), hv]
  refine ⟨⟨finiteOnCompacts_map eI mi hmi, fun v => finiteOnCompacts_map (eV v) (mv v) (hmv v), hsum'⟩,
    fun S fi fv hfi hfv => ?_⟩
  exact abstract_transport projInf (fun v X => projV v (projFin X)) (fun v => (hcv v).measurable)
    (fun v => latV b v) hL (lrHomeo g γ).toMeasurableEquiv eI (fun v => eV v) eI.continuous.measurable
    (fun v => (eV v).continuous.measurable) (fun X => map_lrAct prInf g.val γ.val X)
    (fun v X => map_lrAct (prV v) g.val γ.val X) hfinS.toFinset hS₀ ν mi mv
    (fun v => by
      have := hmv v
      exact ((eV v).isCompact_preimage.2 (hlc v)).measure_lt_top.ne) hsum' H S fi fv hfi hfv

end GlobalTheory.GaugeEx.ProdTransport
