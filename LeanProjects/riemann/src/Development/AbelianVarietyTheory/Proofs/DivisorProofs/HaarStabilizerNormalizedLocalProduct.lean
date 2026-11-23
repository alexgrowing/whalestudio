import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompFinMemIntLocAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitIdelesOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesCompactOfLocalBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompMemOfIsStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitAtUnitArch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtUnitArchOfMemIdelesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIOneSubEInf
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

noncomputable section

namespace GlobalTheory.ThK.EulerMeas

open MeasureTheory.Measure

theorem cylProd_of_restrProd {G ι κ : Type} {H : ι → Type} {P : κ → Type} {Ya : ι → Type} {Yf : κ → Type}
    [Fintype ι] [Group G] [∀ i, Group (H i)] [∀ k, Group (P k)] [TopologicalSpace G] [∀ i, TopologicalSpace (H i)]
    [∀ k, TopologicalSpace (P k)] [MeasurableSpace G] [∀ i, MeasurableSpace (H i)] [∀ k, MeasurableSpace (P k)]
    [∀ i, MeasurableSpace (Ya i)] [∀ k, MeasurableSpace (Yf k)]
    {p : ∀ i, G →* H i} {q : ∀ k, G →* P k} {K : ∀ k, Subgroup (P k)} {μi : ∀ i, Measure (H i)}
    {μf : ∀ k, Measure (P k)} {μ : Measure G}
    (h : GlobalTheory.AdelicU.IsRestrProd p q K μi μf μ) (ja : ∀ i, H i → Ya i) (jf : ∀ k, P k → Yf k)
    (hja : ∀ i, Measurable (ja i)) (hjf : ∀ k, Measurable (jf k)) (Kb : ∀ k, Set (Yf k))
    (hKbm : ∀ k, MeasurableSet (Kb k)) (hKb : ∀ k, jf k ⁻¹' Kb k = K k) :
    GlobalTheory.RestrMeas.IsCylProd (fun i g => ja i (p i g)) (fun k g => jf k (q k g)) Kb
      (fun i => (μi i).map (ja i)) (fun k => (μf k).map (jf k)) μ := by
  have hK1 : ∀ k, (μf k).map (jf k) (Kb k) = μf k (K k) := fun k => by
    rw [Measure.map_apply (hjf k) (hKbm k), hKb k]
  refine ⟨h.vol_one.mono fun k hk => (hK1 k).trans hk, fun S hS A B hA hB => ?_⟩
  have e : GlobalTheory.RestrMeas.cyl (fun i g => ja i (p i g)) (fun k g => jf k (q k g)) Kb S A B =
      GlobalTheory.AdelicU.cyl p q K S (fun i => ja i ⁻¹' A i) (fun k => jf k ⁻¹' B k) := by
    ext g
    simp only [GlobalTheory.RestrMeas.mem_cyl, GlobalTheory.AdelicU.mem_cyl, Set.mem_preimage]
    refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun k _ => ?_
    show q k g ∈ jf k ⁻¹' Kb k ↔ _
    rw [hKb k]
    rfl
  rw [e, h.measure_cyl S (fun k hk => (hK1 k).symm.trans (hS k hk)) _ _ (fun i => hja i (hA i))
    (fun k hk => hjf k (hB k hk))]
  simp only [Measure.map_apply (hja _) (hA _)]
  congr 1
  exact Finset.prod_congr rfl fun k hk => (Measure.map_apply (hjf k) (hB k hk)).symm

end GlobalTheory.ThK.EulerMeas

namespace GlobalTheory.ThK.EulerMeas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem topFacts (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsTopologicalRing (AE F E) ∧ T2Space (AE F E) ∧ LocallyCompactSpace (AE F E)ˣ ∧
    SecondCountableTopology (AE F E)ˣ ∧ T2Space (AE F E)ˣ ∧ BorelSpace (AE F E)ˣ ∧
    SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) ∧ BorelSpace (UA σ J) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : T2Space (Matrix (Fin n) (Fin n) (AE F E)) := inferInstanceAs (T2Space (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.secondCountableTopology
  refine ⟨inferInstance, inferInstance, Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology, inferInstance, ⟨rfl⟩, inferInstance, inferInstance, ⟨rfl⟩⟩

end GlobalTheory.ThK.EulerMeas

namespace GlobalTheory.ThK.EulerMeas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} {K : Subgroup (UA σ X.J)}

def kArch (hK : ∀ k ∈ K, compArch σ X.J k ∈ K) : K →* KAt K (evI F) :=
  ((compArch σ X.J).comp K.subtype).codRestrict (KAt K (evI F)) fun k => ⟨hK k.1 k.2, compArch_mem k.1⟩

def kAt (hK : ∀ k ∈ K, ∀ v, compAt σ X.J v k ∈ K) (v : Pl F) : K →* KAt K (evFin F v) :=
  ((compAt σ X.J v).comp K.subtype).codRestrict (KAt K (evFin F v)) fun k => ⟨hK k.1 k.2 v, compAt_mem v k.1⟩

variable (F E) in

def lArch : (AE F E)ˣ →* idelesAt E (evI F) := (unitArch F E).codRestrict _ unitArch_mem

variable (E) in

def lAt (v : Pl F) : (AE F E)ˣ →* idelesAt E (evFin F v) := (unitAt E v).codRestrict _ (unitAt_mem v)

@[simp] theorem kArch_val (hK : ∀ k ∈ K, compArch σ X.J k ∈ K) (k : K) : (kArch hK k).1 = compArch σ X.J k.1 := rfl
@[simp] theorem kAt_val (hK : ∀ k ∈ K, ∀ v, compAt σ X.J v k ∈ K) (v : Pl F) (k : K) :
    (kAt hK v k).1 = compAt σ X.J v k.1 := rfl
@[simp] theorem lArch_val (l : (AE F E)ˣ) : (lArch F E l).1 = unitArch F E l := rfl
@[simp] theorem lAt_val (v : Pl F) (l : (AE F E)ˣ) : (lAt E v l).1 = unitAt E v l := rfl

def pG (hK : ∀ k ∈ K, compArch σ X.J k ∈ K) (_ : Unit) : K × (AE F E)ˣ →* KAt K (evI F) × idelesAt E (evI F) :=
  (kArch hK).prodMap (lArch F E)

def qG (hK : ∀ k ∈ K, ∀ v, compAt σ X.J v k ∈ K) (v : Pl F) :
    K × (AE F E)ˣ →* KAt K (evFin F v) × idelesAt E (evFin F v) :=
  (kAt hK v).prodMap (lAt E v)

variable (K) in

def kSub (v : Pl F) : Subgroup (KAt K (evFin F v) × idelesAt E (evFin F v)) :=
  (⊤ : Subgroup (KAt K (evFin F v))).prod ((unitsAt E v).subgroupOf (idelesAt E (evFin F v)))

theorem mem_kSub {v : Pl F} {x : KAt K (evFin F v) × idelesAt E (evFin F v)} : x ∈ kSub K v ↔ x.2.1 ∈ unitsAt E v := by
  simp [kSub, Subgroup.mem_prod, Subgroup.mem_subgroupOf]

theorem continuous_kArch (hK : ∀ k ∈ K, compArch σ X.J k ∈ K) : Continuous (kArch hK) :=
  continuous_induced_rng.2 (((GlobalTheory.ThK.ConeEuler.continuous_components F E σ n X.J).2).comp continuous_subtype_val)

theorem continuous_kAt (hK : ∀ k ∈ K, ∀ v, compAt σ X.J v k ∈ K) (v : Pl F) : Continuous (kAt hK v) :=
  continuous_induced_rng.2 (((GlobalTheory.ThK.ConeEuler.continuous_components F E σ n X.J).1 v).comp continuous_subtype_val)

theorem continuous_lArch : Continuous (lArch F E) := continuous_induced_rng.2 (GlobalTheory.ThK.ConeEuler.continuous_unitAt_unitArch F E).2

theorem continuous_lAt (v : Pl F) : Continuous (lAt E v) := continuous_induced_rng.2 ((GlobalTheory.ThK.ConeEuler.continuous_unitAt_unitArch F E).1 v)

end GlobalTheory.ThK.EulerMeas

namespace GlobalTheory.ThK.EulerMeas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n}

theorem exists_glueK (K : Subgroup (UA σ X.J)) (a : UA σ X.J) (ha : a ∈ UAt σ X (evI F)) (haK : a ∈ K)
    (y : Pl F → UA σ X.J) : ∀ S : Finset (Pl F), (∀ v ∈ S, y v ∈ UAt σ X (evFin F v)) → (∀ v ∈ S, y v ∈ K) →
    ∃ k ∈ K, compArch σ X.J k = a ∧ (∀ v ∈ S, compAt σ X.J v k = y v) ∧ ∀ v ∉ S, compAt σ X.J v k = 1 := by
  classical
  have sK := GlobalTheory.ThK.ConeEuler.SuppOne.comp_of_supp F E σ n X
  intro S
  induction S using Finset.induction_on with
  | empty => exact fun _ _ => ⟨a, haK, ((sK a).2 ha).1, by simp, fun v _ => ((sK a).2 ha).2 v⟩
  | insert w S hw ih =>
    intro hy hyK
    obtain ⟨k, hk, h1, h2, h3⟩ := ih (fun v hv => hy v (Finset.mem_insert_of_mem hv))
      (fun v hv => hyK v (Finset.mem_insert_of_mem hv))
    have hyw := hy w (Finset.mem_insert_self w S)
    refine ⟨k * y w, K.mul_mem hk (hyK w (Finset.mem_insert_self w S)), ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [map_mul, h1, ((sK _).1 w hyw).2.1, mul_one]
    · rw [map_mul]
      rcases Finset.mem_insert.1 hv with rfl | hv'
      · rw [h3 v hw, ((sK _).1 v hyw).1, one_mul]
      · rw [h2 v hv', ((sK _).1 w hyw).2.2 v (fun e => hw (e ▸ hv')), mul_one]
    · rw [map_mul, h3 v (fun h => hv (Finset.mem_insert_of_mem h)),
        ((sK _).1 w hyw).2.2 v (fun e => hv (e ▸ Finset.mem_insert_self _ _)), one_mul]

end GlobalTheory.ThK.EulerMeas

namespace GlobalTheory.ThK.EulerMeas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} {K : Subgroup (UA σ X.J)}

theorem isRestrGroup (hcpt : IsCompact (K : Set (UA σ X.J))) (hA : ∀ k ∈ K, compArch σ X.J k ∈ K)
    (hF : ∀ k ∈ K, ∀ v, compAt σ X.J v k ∈ K) :
    GlobalTheory.AdelicU.IsRestrGroup (H := fun _ : Unit => KAt K (evI F) × idelesAt E (evI F)) (pG hA) (qG hF) (kSub K) := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := topFacts (F := F) (E := E) σ X.J
  have cp : ∀ i, Continuous (pG (σ := σ) (X := X) hA i) := fun _ =>
    (continuous_kArch hA).prodMap continuous_lArch
  have cq : ∀ v, Continuous (qG (σ := σ) (X := X) hF v) := fun v =>
    (continuous_kAt hF v).prodMap (continuous_lAt v)
  have oK : ∀ v, IsOpen (kSub K v : Set (KAt K (evFin F v) × idelesAt E (evFin F v))) := fun v => by
    convert isOpen_univ.prod (isCompact_isOpen_unitsAt (E := E) v).2 using 1
    ext x
    simp [mem_kSub]
  refine ⟨cp, cq, oK, ?_, fun S A B hAc hBc => ?_, fun S x y => ?_⟩
  · convert (GlobalTheory.T.unit_ideles_open F E).preimage continuous_snd using 1
    ext g
    simp [mem_kSub, qG]
  · haveI : CompactSpace K := isCompact_iff_compactSpace.1 hcpt
    have hC := GlobalTheory.T.ideles_compact_of_local_bounds F E S (Subtype.val '' (Prod.snd '' A ())) (fun v => Subtype.val '' (Prod.snd '' B v))
      (((hAc ()).image continuous_snd).image continuous_subtype_val)
      fun v hv => ((hBc v hv).image continuous_snd).image continuous_subtype_val
    refine (isCompact_univ.prod hC).of_isClosed_subset ?_ ?_
    · have e : GlobalTheory.AdelicU.cyl (pG hA) (qG hF) (kSub K) S A B = (⋂ i, pG hA i ⁻¹' A i) ∩
          ((⋂ k ∈ S, qG hF k ⁻¹' B k) ∩ ⋂ k ∈ (↑S : Set (Pl F))ᶜ, qG hF k ⁻¹' (kSub K k : Set _)) := by
        ext g
        simp [GlobalTheory.AdelicU.mem_cyl]
      rw [e]
      exact (isClosed_iInter fun i => (hAc i).isClosed.preimage (cp i)).inter
        ((isClosed_biInter fun k hk => (hBc k hk).isClosed.preimage (cq k)).inter
          (isClosed_biInter fun k _ => (Subgroup.isClosed_of_isOpen _ (oK k)).preimage (cq k)))
    · rintro g ⟨h1, h2, h3⟩
      refine ⟨Set.mem_univ _, ⟨_, ⟨_, h1 (), rfl⟩, rfl⟩, fun v hv => ⟨_, ⟨_, h2 v hv, rfl⟩, rfl⟩, fun v hv => ?_⟩
      exact mem_kSub.1 (h3 v hv)
  · classical
    have sU := GlobalTheory.ThK.ConeEuler.unitAt_unitArch_of_mem_idelesAt F E
    have hx2 : (x ()).2.1 ∈ idelesAt E (evI F) := (x ()).2.2
    have hy2 : ∀ v : S, (y v).2.1 ∈ idelesAt E (evFin F v.1) := fun v => (y v).2.2
    let y' : Pl F → UA σ X.J := fun v => if h : v ∈ S then (y ⟨v, h⟩).1.1 else 1
    have ey : ∀ v : S, y' v.1 = (y v).1.1 := fun v => by simp [y', v.2]
    obtain ⟨k, hk, h1, h2, h3⟩ := exists_glueK K (x ()).1.1 (x ()).1.2.2 (x ()).1.2.1 y' S
      (fun v hv => by rw [show y' v = (y ⟨v, hv⟩).1.1 from dif_pos hv]; exact (y ⟨v, hv⟩).1.2.2)
      (fun v hv => by rw [show y' v = (y ⟨v, hv⟩).1.1 from dif_pos hv]; exact (y ⟨v, hv⟩).1.2.1)
    refine ⟨(⟨k, hk⟩, (x ()).2.1 * ∏ v : S, (y v).2.1), fun _ => ?_, fun v => ?_, fun v hv => ?_⟩
    · refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change compArch σ X.J k = _
        exact h1
      change unitArch F E ((x ()).2.1 * ∏ v : S, (y v).2.1) = _
      rw [map_mul, map_prod, (sU (x ()).2.1).2 hx2 |>.1, Finset.prod_eq_one fun v _ => ((sU (y v).2.1).1 v.1 (hy2 v)).2.1, mul_one]
    · refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change compAt σ X.J v.1 k = _
        exact (h2 v.1 v.2).trans (ey v)
      change unitAt E v.1 ((x ()).2.1 * ∏ v : S, (y v).2.1) = _
      rw [map_mul, map_prod, ((sU (x ()).2.1).2 hx2).2 v.1, one_mul, Finset.prod_eq_single v
        (fun u _ hu => ((sU (y u).2.1).1 u.1 (hy2 u)).2.2 v.1 fun h => hu (Subtype.ext h.symm)) (by simp),
        ((sU (y v).2.1).1 v.1 (hy2 v)).1]
    · refine mem_kSub.2 ?_
      change unitAt E v ((x ()).2.1 * ∏ v : S, (y v).2.1) ∈ unitsAt E v
      rw [map_mul, map_prod, ((sU (x ()).2.1).2 hx2).2 v, one_mul, Finset.prod_eq_one fun u _ =>
        ((sU (y u).2.1).1 u.1 (hy2 u)).2.2 v fun h => hv (h ▸ u.2)]
      exact one_mem _

end GlobalTheory.ThK.EulerMeas

namespace GlobalTheory.ThK.EulerMeas

theorem subgroup_facts {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] {K : Subgroup G} (hK : IsCompact (K : Set G)) :
    IsTopologicalGroup K ∧ LocallyCompactSpace K ∧ SecondCountableTopology K ∧ T2Space K ∧ BorelSpace K := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  exact ⟨inferInstance, inferInstance, TopologicalSpace.Subtype.secondCountableTopology _, inferInstance, inferInstance⟩

theorem prod_facts {G H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [Group H] [TopologicalSpace H]
    [MeasurableSpace H]
    (hG : IsTopologicalGroup G ∧ LocallyCompactSpace G ∧ SecondCountableTopology G ∧ T2Space G ∧ BorelSpace G)
    (hH : IsTopologicalGroup H ∧ LocallyCompactSpace H ∧ SecondCountableTopology H ∧ T2Space H ∧ BorelSpace H)
    (μ : Measure G) (ν : Measure H) (hμ : μ.IsHaarMeasure) (hν : ν.IsHaarMeasure) :
    (IsTopologicalGroup (G × H) ∧ LocallyCompactSpace (G × H) ∧ SecondCountableTopology (G × H) ∧ T2Space (G × H) ∧
      BorelSpace (G × H)) ∧ (μ.prod ν).IsHaarMeasure ∧ (SigmaFinite μ ∧ SFinite μ) ∧ SigmaFinite ν ∧ SFinite ν := by
  obtain ⟨_, _, _, _, _⟩ := hG
  obtain ⟨_, _, _, _, _⟩ := hH
  exact ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance,
    ⟨inferInstance, inferInstance⟩, inferInstance, inferInstance⟩

theorem haar_isCylProd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ → ∀ (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (K : Subgroup (UA σ X.J)), IsStab B K → ∀ (μK : Measure K) (μ : Measure (AE F E)ˣ), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))), (∀ v, IsNormK K (evFin F v) (μKv v)) →
    ∀ (μEv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))), (∀ v, IsNormE E v (μEv v)) →
    ∀ (μKi : Measure (KAt K (evI F))), IsNormK K (evI F) μKi → ∀ (μEi : Measure (idelesAt E (evI F))), μEi.IsHaarMeasure →
    SigmaFinite μK ∧ SigmaFinite μ ∧ SigmaFinite (μKi.map Subtype.val) ∧ SigmaFinite (μEi.map Subtype.val) ∧
    (∀ v, SigmaFinite ((μKv v).map Subtype.val) ∧ SigmaFinite ((μEv v).map Subtype.val)) ∧
    (∀ v, Measurable fun p : K × (AE F E)ˣ => (compAt σ X.J v p.1.1, unitAt E v p.2)) ∧
    Measurable (fun p : K × (AE F E)ˣ => (compArch σ X.J p.1.1, unitArch F E p.2)) ∧
    (∀ v, MeasurableSet {q : UA σ X.J × (AE F E)ˣ | q.1 ∈ KAt K (evFin F v) ∧ q.2 ∈ unitsAt E v}) ∧
    (∀ v, ((μKv v).map Subtype.val).prod ((μEv v).map Subtype.val)
      {q : UA σ X.J × (AE F E)ˣ | q.1 ∈ KAt K (evFin F v) ∧ q.2 ∈ unitsAt E v} = 1) ∧
    (∀ p : K × (AE F E)ˣ, ∀ᶠ v in cofinite, compAt σ X.J v p.1.1 ∈ KAt K (evFin F v) ∧ unitAt E v p.2 ∈ unitsAt E v) ∧
    ∃ κ : ℝ≥0, κ ≠ 0 ∧ GlobalTheory.RestrMeas.IsCylProd (W := Unit) (V := Pl F)
      (fun _ (p : K × (AE F E)ˣ) => (compArch σ X.J p.1.1, unitArch F E p.2))
      (fun v p => (compAt σ X.J v p.1.1, unitAt E v p.2))
      (fun v => {q : UA σ X.J × (AE F E)ˣ | q.1 ∈ KAt K (evFin F v) ∧ q.2 ∈ unitsAt E v})
      (fun _ => (μKi.map Subtype.val).prod (μEi.map Subtype.val))
      (fun v => ((μKv v).map Subtype.val).prod ((μEv v).map Subtype.val))
      (κ • μK.prod μ) := by
  intro F E _ _ _ _ _ σ hP B n X r s hB hX K hK μK μ hμK hμ μKv hKv μEv hEv μKi hKi μEi hEi
  have hcpt : IsCompact (K : Set (UA σ X.J)) := by
    obtain ⟨K', -, -, hK', hc, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B n X r s hB hX
    have e : K = K' := Subgroup.ext fun g => (hK g).trans (hK' g).symm
    exact e ▸ hc
  have hS := GlobalTheory.ThK.ConeEuler.StabComp.comp_mem_of_isStab F E σ B n X K hK
  have hA : ∀ k ∈ K, compArch σ X.J k ∈ K := fun k hk => (hS k hk).2
  have hF : ∀ k ∈ K, ∀ v, compAt σ X.J v k ∈ K := fun k hk => (hS k hk).1
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := topFacts (F := F) (E := E) σ X.J
  haveI gU : IsTopologicalGroup (UA σ X.J) := inferInstance
  haveI gE : IsTopologicalGroup (AE F E)ˣ := inferInstance
  obtain ⟨⟨_, _, _, _, _⟩, _, ⟨sK, _⟩, sE, _⟩ := prod_facts (subgroup_facts hcpt) ⟨gE, ‹_›, ‹_›, ‹_›, ‹_›⟩ μK μ hμK hμ
  obtain ⟨⟨_, _, _, _, _⟩, hi, ⟨sKi, _⟩, sEi, _⟩ := prod_facts (subgroup_facts (isCompact_KAt hcpt (evI F)))
    (idelesAt_facts E (evI F)) μKi μEi hKi.1 hEi
  have pv := fun v : Pl F => prod_facts (subgroup_facts (isCompact_KAt hcpt (evFin F v)))
    (idelesAt_facts E (evFin F v)) (μKv v) (μEv v) (hKv v).1 (hEv v).1
  haveI := fun v => (pv v).1.1
  haveI := fun v => (pv v).1.2.1
  haveI := fun v => (pv v).1.2.2.1
  haveI := fun v => (pv v).1.2.2.2.1
  haveI := fun v => (pv v).1.2.2.2.2
  haveI := fun v => (pv v).2.2.1.1
  haveI := fun v => (pv v).2.2.1.2
  haveI := fun v => (pv v).2.2.2.1
  haveI := fun v => (pv v).2.2.2.2
  have eKi : MeasurableEmbedding (Subtype.val : KAt K (evI F) → UA σ X.J) :=
    MeasurableEmbedding.subtype_coe (isCompact_KAt hcpt _).measurableSet
  have eKv : ∀ v, MeasurableEmbedding (Subtype.val : KAt K (evFin F v) → UA σ X.J) := fun v =>
    MeasurableEmbedding.subtype_coe (isCompact_KAt hcpt _).measurableSet
  have eEi : MeasurableEmbedding (Subtype.val : idelesAt E (evI F) → (AE F E)ˣ) :=
    MeasurableEmbedding.subtype_coe (isClosed_idelesAt _).measurableSet
  have eEv : ∀ v, MeasurableEmbedding (Subtype.val : idelesAt E (evFin F v) → (AE F E)ˣ) := fun v =>
    MeasurableEmbedding.subtype_coe (isClosed_idelesAt _).measurableSet
  have hU : ∀ v : Pl F, MeasurableSet {l : (AE F E)ˣ | l ∈ unitsAt E v} := fun v => by
    have := ((isCompact_isOpen_unitsAt (E := E) v).1.image continuous_subtype_val).measurableSet
    convert this using 1
    ext l
    exact ⟨fun h => ⟨⟨l, h.1⟩, h, rfl⟩, fun ⟨m, h, e⟩ => e ▸ h⟩
  have hM : ∀ v, MeasurableSet {q : UA σ X.J × (AE F E)ˣ | q.1 ∈ KAt K (evFin F v) ∧ q.2 ∈ unitsAt E v} := fun v =>
    (isCompact_KAt hcpt _).measurableSet.prod (hU v)
  have hpre : ∀ v, Prod.map Subtype.val Subtype.val ⁻¹'
      {q : UA σ X.J × (AE F E)ˣ | q.1 ∈ KAt K (evFin F v) ∧ q.2 ∈ unitsAt E v} =
      (kSub K v : Set (KAt K (evFin F v) × idelesAt E (evFin F v))) := fun v => by
    ext x
    rw [SetLike.mem_coe, mem_kSub]
    exact ⟨fun h => h.2, fun h => ⟨x.1.2, h⟩⟩
  have h1 : ∀ v, (μKv v).prod (μEv v) (kSub K v) = 1 := fun v => by
    have e : (kSub K v : Set (KAt K (evFin F v) × idelesAt E (evFin F v))) = Set.univ ×ˢ {l | l.1 ∈ unitsAt E v} := by
      ext x
      simp [mem_kSub]
    rw [e, Measure.prod_prod, (hKv v).2, (hEv v).2, one_mul]
  have mi := Measure.map_prod_map μKi μEi eKi.measurable eEi.measurable
  have mv := fun v => Measure.map_prod_map (μKv v) (μEv v) (eKv v).measurable (eEv v).measurable
  have cK := GlobalTheory.ThK.ConeEuler.continuous_components F E σ n X.J
  have cU := GlobalTheory.ThK.ConeEuler.continuous_unitAt_unitArch F E
  refine ⟨sK, sE, eKi.sigmaFinite_map, eEi.sigmaFinite_map,
    fun v => ⟨(eKv v).sigmaFinite_map, (eEv v).sigmaFinite_map⟩, fun v => ?_, ?_, hM, fun v => ?_, fun p => ?_, ?_⟩
  · exact (((cK.1 v).measurable.comp measurable_subtype_coe).comp measurable_fst).prodMk
      ((cU.1 v).measurable.comp measurable_snd)
  · exact ((cK.2.measurable.comp measurable_subtype_coe).comp measurable_fst).prodMk
      (cU.2.measurable.comp measurable_snd)
  · rw [mv, Measure.map_apply ((eKv v).measurable.prodMap (eEv v).measurable) (hM v), hpre, h1]
  · exact (GlobalTheory.ThK.ConeEuler.eventually_unitAt_mem_unitsAt F E p.2).mono fun v hv =>
      ⟨⟨hF _ p.1.2 v, compAt_mem v _⟩, hv⟩
  · obtain ⟨c, hc, h⟩ := (isRestrGroup hcpt hA hF).exists_smul (μi := fun _ => μKi.prod μEi)
      (μf := fun v => (μKv v).prod (μEv v)) (fun _ => hi) (fun v => (pv v).2.1)
      (Eventually.of_forall h1) (μK.prod μ)
    refine ⟨c, hc, ?_⟩
    have := cylProd_of_restrProd (Ya := fun _ => UA σ X.J × (AE F E)ˣ) (Yf := fun _ => UA σ X.J × (AE F E)ˣ) h
      (fun _ => Prod.map Subtype.val Subtype.val) (fun _ => Prod.map Subtype.val Subtype.val)
      (fun _ => eKi.measurable.prodMap eEi.measurable) (fun v => (eKv v).measurable.prodMap (eEv v).measurable) _ hM hpre
    simp only [mi, mv]
    exact this

end GlobalTheory.ThK.EulerMeas

end
