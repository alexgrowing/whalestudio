import Development.AutomorphicArithmetic.AdelicQuotients.MatrixCoefficientBoundedByValueAtOne
import Development.AutomorphicArithmetic.AdelicQuotients.UnitaryAdelicMemOfLocalGroupsNearOne
import Development.AutomorphicArithmetic.AdelicQuotients.UnitaryLocalGroupLeOffPlacesEmpty
import Development.AutomorphicArithmetic.AdelicQuotients.HaarMeasureTripleProductDecomposition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFinitePlacesIntegralMemNhdsOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFiniteUnramifiedOutsideOfIsHecke

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TP
private theorem nv_sf_pk {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : SFinite μ := inferInstance
end UpperTheory.TP
open UpperTheory.TP
set_option maxHeartbeats 2000000 in
theorem _root_.UpperTheory.TP.nonVan_k :
    _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.Rallis_k → _root_.UpperTheory.TP.Decomp_k → _root_.UpperTheory.TP.BumpAny_k → _root_.UpperTheory.TP.Datum_k → _root_.UpperTheory.TP.Tail_k → UpperTheory.TP.AbsNe → _root_.UpperTheory.TP.SchurStep_k → _root_.UpperTheory.TP.NonVan_k := by
  intro T hR hD hBu hDa hTl hAb hSc E _ _ _ B n d X W M χX χW om hP hn e e' he he' hd K a ε hK ha hε t₀ ht hlt U hU f₀ hf₀ hf0 φ hφ0 hS
  classical
  obtain ⟨a1, a2, a3⟩ := Euler.lcsc_UA (cj E) X.J
  have hC : Cpt (cj E) X.J := T.cpt _ E (cj E) B n X n 0 hP.base (Or.inl hP.herm) (by simp)
  have hS' := hS
  have hA : GlobalTheory.UnitaryBC.IsAutFormU φ := by
    obtain ⟨V, _, _, _, ρ, i, jj, x₀, -, -, hjx, hjU, -, -⟩ := hS'
    exact hU.aut φ (hjx ▸ hjU x₀)
  set φ' : UA (cj E) X.J → ℂ := φ ∘ e.symm with hφ'
  have hfn : IsFn φ' := ⟨hA.cont.comp e.symm.continuous, fun γ hγ g => by
    have h1 : e.symm γ ∈ GlobalTheory.UnitaryBC.ratU E n := (he.rat _).1 (by simpa using hγ)
    simpa [hφ'] using hA.left _ h1 (e.symm g)⟩
  have hφ'0 : φ' ≠ 0 := fun h => hφ0 (funext fun g => by simpa [hφ'] using congrFun h (e g))
  obtain ⟨r, r0, r1, r2⟩ := UpperTheory.matrix_coefficient_bounded_by_value_at_one (M := M) hC hP.good.haar hP.good.dom hfn hφ'0
  obtain ⟨O, oO, eO⟩ := isOpen_induced_iff.1 hA.level
  have one_O : (1 : GlobalTheory.UnitaryBC.UA E n) ∈ O := by
    have : (1 : GlobalTheory.UnitaryBC.finU E n) ∈ Subtype.val ⁻¹' O := by
      rw [eO]; show GlobalTheory.UnitaryBC.RU E n 1 φ = φ; rw [map_one]; rfl
    exact this
  set N : Set (UA (cj E) X.J) := e.symm ⁻¹' O with hN
  have oN : IsOpen N := oO.preimage e.symm.continuous
  have one_N : (1 : UA (cj E) X.J) ∈ N := by simpa [hN] using one_O
  have hfix : ∀ g ∈ gOff (cj E) X ∅, g ∈ N → ∀ y, φ' (y * g) = φ' y := fun g hg hgN y => by
    have k1 : e.symm g ∈ GlobalTheory.UnitaryBC.finU E n := (he.fin _).1 (by simpa using hg)
    have k2 : (⟨e.symm g, k1⟩ : GlobalTheory.UnitaryBC.finU E n) ∈ {k : GlobalTheory.UnitaryBC.finU E n | GlobalTheory.UnitaryBC.RU E n k φ = φ} := by
      rw [← eO]; exact hgN
    have : φ (e.symm y * e.symm g) = φ (e.symm y) := congrFun k2 (e.symm y)
    simpa [hφ'] using this
  obtain ⟨⟨j0, hj0⟩, -, -, -, cK0, -, -, -, -⟩ := hD _ E (cj E) B n X hP.base hP.herm ∅
  have clOff : ∀ S, IsClosed (gOff (cj E) X S : Set (UA (cj E) X.J)) := fun S =>
    (hD _ E (cj E) B n X hP.base hP.herm S).2.2.2.1
  obtain ⟨S₀, hS₀⟩ := _root_.UpperTheory.exists_finite_places_integral_mem_nhds_one hP.base hP.herm cK0 clOff (oN.mem_nhds one_N)
  obtain ⟨R, hRam⟩ := _root_.UpperTheory.exists_finite_unramified_outside_of_isHecke hP.base hP.hW
  have hint := ht _ hlt.le
  obtain ⟨S, hSS, hTail⟩ := hTl _ E (cj E) B n X hP.base hP.herm K a ε hK ha hε M.μ ((d : ℝ) / 2) hP.good.haar hint (S₀ ∪ R)
  have hOffS : gOff (cj E) X S ≤ gOff (cj E) X S₀ := Subgroup.closure_mono fun g hg =>
    ⟨hg.1, fun v hv => hg.2 v (hSS (Finset.mem_union_left _ hv))⟩
  have hOff0 : gOff (cj E) X S ≤ gOff (cj E) X ∅ := Subgroup.closure_mono fun g hg =>
    ⟨hg.1, fun v hv => absurd hv (by simp)⟩
  have hunr : UnrOff χW (S : Set (Pl (maximalRealSubfield E))) := fun w hw => hRam w fun h => hw (by
    simp only [above, Set.mem_setOf_eq] at h ⊢
    exact hSS (Finset.mem_union_right _ h))
  have hbump := fun v => hBu _ E (cj E) B n d X W M χX χW om hP hn hd v N (oN.mem_nhds one_N)
  choose H b hb hHN using hbump
  set φf : ∀ v : Pl (maximalRealSubfield E), (Fin n × Fin d → Fv (maximalRealSubfield E) v) → ℂ :=
    fun v => if v ∈ S then b v else M.vac v with hφf
  have hfin : IsFin M φf := by
    refine ⟨fun v => ?_, ?_⟩
    · by_cases hv : v ∈ S
      · simpa [hφf, hv] using (hb v).1
      · simpa [hφf, hv] using (hP.good.vac v).1
    · filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hv
      simp [hφf, hv]
  letI : MeasurableSpace (Fin n × Fin d → AF (maximalRealSubfield E)) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF (maximalRealSubfield E)) := ⟨rfl⟩
  let ν : Measure (Fin n × Fin d → AF (maximalRealSubfield E)) := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := inferInstance
  obtain ⟨hc1, hco⟩ := hDa _ E (cj E) B n d X W M χX χW om hP hn K a ε hK ha hε ν hν S hunr H φf hfin
    (fun v hv => by simpa [hφf, hv] using hb v) (fun v hv => by simp [hφf, hv]) f₀ hf₀ hf0
  obtain ⟨⟨j, hj⟩, cInf, clAt, clOff', cK, oK, -, hcomp, -⟩ := hD _ E (cj E) B n X hP.base hP.herm S
  let Tst : Subgroup (UA (cj E) X.J) :=
    { carrier := {g | ∀ y, φ' (y * g) = φ' y}
      one_mem' := fun y => by rw [mul_one]
      mul_mem' := fun {g h} hg hh y => by rw [← mul_assoc, hh, hg]
      inv_mem' := fun {g} hg y => by rw [← hg (y * g⁻¹), inv_mul_cancel_right] }
  have hHfix : (⨆ v ∈ S, H v) ≤ Tst := iSup₂_le fun v _ g hg =>
    hfix g (UpperTheory.unitaryLocalGroup_le_offPlaces_empty v ((hb v).2.2.1 hg)) (hHN v hg)
  have hcomm : ∀ (b : gAt (cj E) X S) (c : gOff (cj E) X S), b.1 * c.1 = c.1 * b.1 := fun b c => by
    have h1 : j ((1, (b, 1)) * (1, (1, c))) = j ((1, (1, c)) * (1, (b, 1))) := by
      congr 1
      simp
    rw [map_mul, map_mul, hj, hj] at h1
    simpa using h1
  have hmc : ∀ (x : UA (cj E) X.J) (b : gAt (cj E) X S) (c : gOff (cj E) X S), b.1 ∈ (⨆ v ∈ S, H v) →
      mc M φ' (x * b.1 * c.1) = mc M φ' (x * c.1) := fun x b c hbH => by
    have : (fun y => φ' (y * (x * b.1 * c.1))) = fun y => φ' (y * (x * c.1)) := funext fun y => by
      rw [mul_assoc x, hcomm, ← mul_assoc x, ← mul_assoc y]
      exact hHfix hbH _
    simp only [mc, this]
  haveI : LocallyCompactSpace (gInf (cj E) X) := cInf.isClosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (gAt (cj E) X S) := clAt.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (gOff (cj E) X S) := clOff'.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μA : Measure (gInf (cj E) X) := Measure.haar
  let μB : Measure (gAt (cj E) X S) := Measure.haar
  let μC : Measure (gOff (cj E) X S) := Measure.haar
  haveI : SFinite μA := nv_sf_pk μA
  haveI : SFinite μB := nv_sf_pk μB
  haveI : SFinite μC := nv_sf_pk μC
  obtain ⟨κ, hκ, hκe⟩ := hSc E B n d X W M χX χW om hP hn e e' he he' U hU f₀ hf0 φ hφ0 hS ν hν φf hfin μA inferInstance
  have hPol : pure f₀ φf ∈ PolData B M := Submodule.subset_span ⟨f₀, hf₀, φf, hfin.1, hfin.2, rfl⟩
  obtain ⟨hI, hZ⟩ := hR _ E (cj E) B n d X W M χX χW om hP hn (by omega) K a ε hK ha hε t₀ ht hlt ν hν _ hPol φ' hfn
  refine ⟨φf, hfin, fun h0 => ?_⟩
  obtain ⟨hIP, c, hc⟩ := UpperTheory.haarMeasure_triple_product_decomposition _ _ _ cInf.isClosed clAt clOff' j M.μ hP.good.haar μA μB μC inferInstance inferInstance
    inferInstance _ hI
  rw [hZ h0, mul_zero] at hc
  choose s s1 s2 s3 using fun c : gOff (cj E) X S => (hco 1 (one_mem _) 1 (one_mem _) c.1 c.2).2
  have oH := UpperTheory.unitaryAdelic_mem_of_localGroups_near_one S H (fun v _ => (hb v).2.2.2.2.1) hcomp
  have hIG : ∀ g ∈ (⨆ v ∈ S, H v), IntAll g := fun g hg =>
    Subgroup.mem_iInf.1 ((iSup₂_le fun v _ g hg => Subgroup.mem_iInf.2 fun w =>
      Bad.int_all ((hb v).2.2.1 hg) ((hb v).2.2.2.1 g hg) w : (⨆ v ∈ S, H v) ≤ ⨅ w, Euler.intGrp (cj E) X w) hg)
  have cB : IsCompact {b : gAt (cj E) X S | IntAll b.1} := clAt.isClosedEmbedding_subtypeVal.isCompact_preimage cK
  have cC : IsCompact {c : gOff (cj E) X S | IntAll c.1} := clOff'.isClosedEmbedding_subtypeVal.isCompact_preimage cK
  refine hAb _ _ _ μA μB μC {b | b.1 ∈ ⨆ v ∈ S, H v} {c | IntAll c.1} oH.measurableSet
    (oK.preimage continuous_subtype_val).measurableSet (oH.measure_ne_zero μB ⟨1, one_mem (⨆ v ∈ S, H v)⟩)
    (ne_top_of_le_ne_top cB.measure_lt_top.ne (measure_mono fun b hb' => hIG _ hb')) cC.measure_lt_top.ne
    _ (fun x c => coef om ν (pure f₀ φf) x.1 * star (mc M φ' (x.1 * c.1))) s (fun c => star (mc M φ' c.1))
    (κ * coef om ν (pure f₀ φf) 1) r (fun c => ENNReal.ofReal (a (ε (c.1, 1)) ^ ((d : ℝ) / 2)))
    (mul_ne_zero hκ hc1) r0 hIP ?_ ?_ ?_ ?_ ?_ (hTail μC inferInstance) hc
  · intro x b c hb'
    rw [hj]
    rw [(hco x.1 x.2 b.1 b.2 c.1 c.2).1 hb', zero_mul]
  · intro x c b hb'
    rw [hj]
    simp only
    rw [s3 c x.1 x.2 b.1 hb', hmc _ _ _ hb', mul_assoc]
  · intro c
    exact hκe c.1 (hOff0 c.2)
  · intro c hc'
    refine ⟨s2 c hc', ?_⟩
    have : (fun y => φ' (y * c.1)) = fun y => φ' (y * 1) := funext fun y => by
      rw [mul_one]; exact hfix _ (hOff0 c.2) (hS₀ _ (hOffS c.2) hc') y
    have e1 : mc M φ' c.1 = r := by rw [← r1]; simp only [mc, this]
    simp [e1]
  · intro c
    refine ⟨by simpa using r2 c.1, ?_⟩
    rw [← s1 c, ofReal_norm_eq_enorm]
end
end
