import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsRhoOfAtInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

noncomputable section

namespace GlobalTheory.ThK

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Parts

variable {M : Type} [AddCommGroup M] [Module (AF F) M]

def partFin (v : Pl F) (z : M) : M := GlobalTheory.LatVac.liftV v 1 • z

variable (F) in

def partInf (z : M) : M := realAd F 1 • z

theorem at_partFin (v : Pl F) (z : M) : At (evFin F v) (partFin v z) := fun u hu => by
  rw [partFin, smul_smul, ← smul_eq_mul, GlobalTheory.LatVac.at_liftV v 1 u hu, zero_smul]

theorem partFin_of_at {v : Pl F} {z : M} (hz : At (evFin F v) z) : partFin v z = z := by
  have h := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

theorem evI_realAd_one : evI F (realAd F 1) = 1 :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _).trans (map_one _)

theorem at_partInf (z : M) : At (evI F) (partInf F z) := fun u hu => by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  have h : u * realAd F 1 = 0 := Prod.ext (show u.1 * _ = 0 by rw [h1, zero_mul]) (show u.2 * 0 = 0 from mul_zero _)
  rw [partInf, smul_smul, h, zero_smul]

theorem partInf_of_at {z : M} (hz : At (evI F) z) : partInf F z = z := by
  have h := hz (1 - realAd F 1) (by
    rw [GlobalTheory.ArchUniq.evI_eq_evIHom, map_sub, map_one, ← GlobalTheory.ArchUniq.evI_eq_evIHom, evI_realAd_one, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

end Parts

section Groups

variable {R : Type} [Zero R] {n : ℕ}

variable (σ) in

def UAtSub (X : Spc F E n) (ev : AF F → R) : Subgroup (UA σ X.J) where
  carrier := UAt σ X ev
  one_mem' := fun u _ => by rw [GlobalTheory.StabHaar.mat_one, sub_self, smul_zero]
  mul_mem' := by
    intro g h hg hh u hu
    have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
      rw [GlobalTheory.StabHaar.mat_mul, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]
  inv_mem' := by
    intro g hg u hu
    have e : mat g⁻¹ - 1 = -((mat g - 1) * mat g⁻¹) := by
      rw [Matrix.sub_mul, Matrix.one_mul, GlobalTheory.StabHaar.mat_mul_inv]; abel
    rw [e, smul_neg, ← Matrix.smul_mul, hg u hu, Matrix.zero_mul, neg_zero]

def KAt {X : Spc F E n} (K : Subgroup (UA σ X.J)) (ev : AF F → R) : Subgroup (UA σ X.J) := K ⊓ UAtSub σ X ev

variable (E) in

def idelesAt (ev : AF F → R) : Subgroup (AE F E)ˣ where
  carrier := {l | At ev ((l : AE F E) - 1)}
  one_mem' := fun u _ => by rw [Units.val_one, sub_self, smul_zero]
  mul_mem' := by
    intro g h hg hh u hu
    have e : ((g * h : (AE F E)ˣ) : AE F E) - 1 = ((g : AE F E) - 1) * h + (h - 1) := by
      rw [Units.val_mul]; ring
    rw [e, smul_add, ← smul_mul_assoc, hg u hu, hh u hu, zero_mul, add_zero]
  inv_mem' := by
    intro g hg u hu
    have e : ((g⁻¹ : (AE F E)ˣ) : AE F E) - 1 = -(((g : AE F E) - 1) * (g⁻¹ : (AE F E)ˣ)) := by
      rw [sub_mul, Units.mul_inv]; ring
    rw [e, smul_neg, ← smul_mul_assoc, hg u hu, zero_mul, neg_zero]

variable (E) in

def unitsAt (v : Pl F) : Subgroup (AE F E)ˣ :=
  idelesAt E (evFin F v) ⊓ (intLoc F E v).toSubmonoid.units.comap (unitFin F E v)

theorem mem_UAtSub {X : Spc F E n} {ev : AF F → R} {g : UA σ X.J} : g ∈ UAtSub σ X ev ↔ g ∈ UAt σ X ev := Iff.rfl

theorem mem_KAt {X : Spc F E n} {K : Subgroup (UA σ X.J)} {ev : AF F → R} {g : UA σ X.J} :
    g ∈ KAt K ev ↔ g ∈ K ∧ g ∈ UAt σ X ev := Iff.rfl

theorem mem_idelesAt {ev : AF F → R} {l : (AE F E)ˣ} : l ∈ idelesAt E ev ↔ At ev ((l : AE F E) - 1) := Iff.rfl

theorem mem_unitsAt {v : Pl F} {l : (AE F E)ˣ} : l ∈ unitsAt E v ↔ l ∈ idelesAt E (evFin F v) ∧
    compFin F E v l ∈ intLoc F E v ∧ compFin F E v (l⁻¹ : (AE F E)ˣ) ∈ intLoc F E v := Iff.rfl

theorem unitsAt_le (v : Pl F) : unitsAt E v ≤ idelesAt E (evFin F v) := inf_le_left

theorem isClosed_UAtSub (X : Spc F E n) (ev : AF F → R) : IsClosed (UAtSub σ X ev : Set (UA σ X.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hm : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  change IsClosed {g : UA σ X.J | ∀ u, ev u = 0 → u • (mat g - 1) = 0}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun u => isClosed_iInter fun _ =>
    isClosed_eq ((hm.sub continuous_const).const_smul u) continuous_const

theorem isCompact_KAt {X : Spc F E n} {K : Subgroup (UA σ X.J)} (hK : IsCompact (K : Set (UA σ X.J))) (ev : AF F → R) :
    IsCompact (KAt K ev : Set (UA σ X.J)) := hK.inter_right (isClosed_UAtSub X ev)

theorem isClosed_idelesAt (ev : AF F → R) : IsClosed (idelesAt E ev : Set (AE F E)ˣ) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  change IsClosed {l : (AE F E)ˣ | ∀ u, ev u = 0 → u • ((l : AE F E) - 1) = 0}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun u => isClosed_iInter fun _ =>
    isClosed_eq ((Units.continuous_val.sub continuous_const).const_smul u) continuous_const

omit [NumberField E] in

theorem compFin_smul (v : Pl F) (a : AF F) (z : AE F E) : compFin F E v (a • z) = evFin F v a • compFin F E v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evFin F v) a b)
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

omit [NumberField E] in

theorem compInf_smul (w : InfinitePlace F) (a : AF F) (z : AE F E) :
    compInf F E w (a • z) = evInf F w a • compInf F E w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evInf F w) a b)
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem at_evFin_iff {v : Pl F} {z : AE F E} : At (evFin F v) z ↔
    (∀ w, compInf F E w z = 0) ∧ ∀ w, w ≠ v → compFin F E w z = 0 := by
  constructor
  · intro hz
    rw [← partFin_of_at hz, partFin]
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · rw [compInf_smul, show evInf F w (GlobalTheory.LatVac.liftV v 1) = 0 from rfl, zero_smul]
    · rw [compFin_smul, show evFin F w (GlobalTheory.LatVac.liftV v 1) = 0 from evalV_singleFin_ne hw 1, zero_smul]
  · rintro ⟨h1, h2⟩ u hu
    refine GlobalTheory.Doubling.adele_ext (fun w => ?_) fun w => ?_
    · rw [compInf_smul, h1, smul_zero, map_zero]
    · rw [compFin_smul, map_zero]
      by_cases hw : w = v
      · subst hw; rw [hu, zero_smul]
      · rw [h2 w hw, smul_zero]

theorem at_evI_iff {z : AE F E} : At (evI F) z ↔ ∀ w, compFin F E w z = 0 := by
  constructor
  · intro hz w
    rw [← partInf_of_at hz, partInf, compFin_smul, show evFin F w (realAd F 1) = 0 from map_zero (evalV F w), zero_smul]
  · intro h u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    refine GlobalTheory.Doubling.adele_ext (fun w => ?_) fun w => ?_
    · rw [compInf_smul, map_zero, show evInf F w u = 0 from congrFun h1 w, zero_smul]
    · rw [compFin_smul, h, smul_zero, map_zero]

theorem ideleAt_mem (v : Pl F) (x : (Fv F v ⊗[F] E)ˣ) : ideleAt F E v x ∈ idelesAt E (evFin F v) := by
  refine at_evFin_iff.2 ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [map_sub, map_one, sub_eq_zero]
    exact congrArg Units.val (GlobalTheory.Doubling.unitInf_ideleAt w v x)
  · rw [map_sub, map_one, sub_eq_zero]
    exact congrArg Units.val (GlobalTheory.Doubling.unitFin_ideleAt_ne hw x)

theorem ideleAt_unitFin {v : Pl F} {l : (AE F E)ˣ} (hl : l ∈ idelesAt E (evFin F v)) :
    ideleAt F E v (unitFin F E v l) = l := by
  obtain ⟨h1, h2⟩ := at_evFin_iff.1 hl
  refine GlobalTheory.Doubling.idele_ext (fun w => ?_) fun w => ?_
  · rw [GlobalTheory.Doubling.unitInf_ideleAt]
    have := h1 w
    rw [map_sub, map_one, sub_eq_zero] at this
    exact Units.ext this.symm
  · by_cases hw : w = v
    · subst hw; rw [GlobalTheory.Doubling.unitFin_ideleAt_self]
    · rw [GlobalTheory.Doubling.unitFin_ideleAt_ne hw]
      have := h2 w hw
      rw [map_sub, map_one, sub_eq_zero] at this
      exact Units.ext this.symm

variable (E) in

def idelesAtEquiv (v : Pl F) : idelesAt E (evFin F v) ≃ₜ* (Fv F v ⊗[F] E)ˣ where
  toFun l := unitFin F E v l.1
  invFun x := ⟨ideleAt F E v x, ideleAt_mem v x⟩
  left_inv l := Subtype.ext (ideleAt_unitFin l.2)
  right_inv x := GlobalTheory.Doubling.unitFin_ideleAt_self v x
  map_mul' a b := map_mul (unitFin F E v) a.1 b.1
  continuous_toFun := (GlobalTheory.Doubling.continuous_unitFin v).comp continuous_subtype_val
  continuous_invFun := (GlobalTheory.Doubling.continuous_ideleAt v).subtype_mk _

theorem absE_of_mem {v : Pl F} {l : (AE F E)ˣ} (hl : l ∈ idelesAt E (evFin F v)) :
    absE F E l = absEv F E v (unitFin F E v l) := by
  conv_lhs => rw [← ideleAt_unitFin hl, GlobalTheory.Doubling.absE_ideleAt]

theorem isCompact_isOpen_intLoc (v : Pl F) :
    IsCompact (intLoc F E v : Set (Fv F v ⊗[F] E)) ∧ IsOpen (intLoc F E v : Set (Fv F v ⊗[F] E)) := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  let b := integralBasis E
  let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v) →ₗ[Fv F v] Fv F v ⊗[F] E :=
    Fintype.linearCombination (Fv F v) fun i => (1 : Fv F v) ⊗ₜ[F] b i
  have hφ : ∀ a, φ a = ∑ i, a i ⊗ₜ[F] b i := fun a => by
    simp only [φ, Fintype.linearCombination_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hq : ∀ (c : ℚ) (a : Fv F v) (x : E), a ⊗ₜ[F] (c • x) = ((c : Fv F v) * a) ⊗ₜ[F] x := fun c a x => by
    rw [show c • x = (c : F) • x by rw [Rat.cast_smul_eq_qsmul], ← TensorProduct.smul_tmul, Algebra.smul_def, map_ratCast]
  have hsurj : Function.Surjective φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a x =>
      refine ⟨fun i => (b.repr x i : Fv F v) * a, ?_⟩
      rw [hφ]
      conv_rhs => rw [← b.sum_repr x, TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun i _ => (hq _ _ _).symm
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hy
      exact ⟨a + c, map_add _ _ _⟩
  have himg : (intLoc F E v : Set (Fv F v ⊗[F] E)) =
      φ '' Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext z
    constructor
    · refine intLoc_induction (p := fun z => z ∈ φ '' Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))
        (fun a ha x => ?_) ⟨0, fun _ _ => zero_mem _, map_zero _⟩ ?_ ?_
      · refine ⟨fun i => (RingOfIntegers.basis E).repr x i • a, fun i _ => zsmul_mem ha _, ?_⟩
        rw [hφ]
        conv_rhs => rw [← b.sum_repr (x : E), TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hq, show b.repr (x : E) i = algebraMap ℤ ℚ ((RingOfIntegers.basis E).repr x i) from
          integralBasis_repr_apply E x i]
        simp
      · rintro _ _ ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
        exact ⟨a + c, fun i hi => add_mem (ha i hi) (hc i hi), map_add _ _ _⟩
      · rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun i hi => neg_mem (ha i hi), map_neg _ _⟩
    · rintro ⟨a, ha, rfl⟩
      rw [hφ]
      refine sum_mem fun i _ => ?_
      rw [show b i = ((RingOfIntegers.basis E i : 𝓞 E) : E) from integralBasis_apply E i]
      exact tmul_mem_intLoc (ha i (Set.mem_univ i)) _
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hC : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  rw [himg]
  exact ⟨(isCompact_univ_pi fun _ => hC).image (IsModuleTopology.continuous_of_linearMap φ),
    (IsModuleTopology.isOpenQuotientMap_of_surjective hsurj).isOpenMap _ (isOpen_set_pi Set.finite_univ fun _ _ => hO)⟩

theorem isCompact_isOpen_unitsAt (v : Pl F) :
    IsCompact {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v} ∧ IsOpen {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v} := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (Fv F v ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have e : {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v} =
      (idelesAtEquiv E v).toHomeomorph ⁻¹' ((intLoc F E v).toSubmonoid.units : Set _) := by
    ext l
    exact ⟨fun h => h.2, fun h => ⟨l.2, h⟩⟩
  rw [e]
  exact ⟨(Homeomorph.isCompact_preimage _).2 (Submonoid.units_isCompact (isCompact_isOpen_intLoc v).1),
    (Submonoid.isOpen_units (isCompact_isOpen_intLoc v).2).preimage (Homeomorph.continuous _)⟩

end Groups

section Haar

variable {R : Type} [Zero R] {n : ℕ} {X : Spc F E n}

def IsNormK (K : Subgroup (UA σ X.J)) (ev : AF F → R) (μ : Measure (KAt K ev)) : Prop :=
  μ.IsHaarMeasure ∧ μ Set.univ = 1

variable (E) in

def IsNormE (v : Pl F) (μ : Measure (idelesAt E (evFin F v))) : Prop :=
  μ.IsHaarMeasure ∧ μ {l | l.1 ∈ unitsAt E v} = 1

theorem existsUnique_isNormK {K : Subgroup (UA σ X.J)} (hK : IsCompact (K : Set (UA σ X.J))) (ev : AF F → R) :
    ∃! μ, IsNormK K ev μ := by
  haveI : CompactSpace (KAt K ev) := isCompact_iff_compactSpace.1 (isCompact_KAt hK ev)
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have h0 : IsNormK K ev (Measure.haarMeasure ⊤) :=
    ⟨Measure.isHaarMeasure_haarMeasure _, Measure.haarMeasure_self⟩
  refine ⟨_, h0, fun μ hμ => ?_⟩
  haveI := hμ.1
  haveI := h0.1
  haveI : IsProbabilityMeasure μ := ⟨hμ.2⟩
  haveI : IsProbabilityMeasure (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (KAt K ev))) := ⟨h0.2⟩
  haveI : LocallyCompactSpace (KAt K ev) :=
    IsCompact.locallyCompactSpace_of_mem_nhds_of_group isCompact_univ (x := 1) univ_mem
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

variable (E) in

theorem idelesAt_facts (ev : AF F → R) : IsTopologicalGroup (idelesAt E ev) ∧ LocallyCompactSpace (idelesAt E ev) ∧
    SecondCountableTopology (idelesAt E ev) ∧ T2Space (idelesAt E ev) ∧ BorelSpace (idelesAt E ev) := by
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
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  exact ⟨inferInstance, (isClosed_idelesAt ev).locallyCompactSpace, inferInstance, inferInstance, inferInstance⟩

variable (E) in

theorem exists_haar_idelesAt (ev : AF F → R) : ∃ μ : Measure (idelesAt E ev), μ.IsHaarMeasure := by
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E ev
  exact ⟨Measure.haar, inferInstance⟩

theorem haar_idelesAt_eq_smul {ev : AF F → R} (μ' μ : Measure (idelesAt E ev)) [μ'.IsHaarMeasure] [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ μ' = c • μ := by
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E ev
  exact ⟨_, (Measure.haarScalarFactor_pos_of_isHaarMeasure μ' μ).ne', Measure.isMulLeftInvariant_eq_smul μ' μ⟩

variable (E) in

theorem existsUnique_isNormE (v : Pl F) : ∃! μ, IsNormE E v μ := by
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  obtain ⟨hc, ho⟩ := isCompact_isOpen_unitsAt (E := E) v
  let U : TopologicalSpace.PositiveCompacts (idelesAt E (evFin F v)) :=
    ⟨⟨_, hc⟩, ⟨1, mem_interior_iff_mem_nhds.2 (ho.mem_nhds (one_mem (unitsAt E v)))⟩⟩
  have h0 : IsNormE E v (Measure.haarMeasure U) := ⟨Measure.isHaarMeasure_haarMeasure _, Measure.haarMeasure_self⟩
  refine ⟨_, h0, fun μ hμ => ?_⟩
  haveI := hμ.1
  haveI := h0.1
  obtain ⟨c, -, hc⟩ := haar_idelesAt_eq_smul μ (Measure.haarMeasure U)
  have h1 := hμ.2
  rw [hc, Measure.smul_apply, h0.2, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_eq_one] at h1
  rw [hc, h1, one_smul]

theorem absE_of_mem_unitsAt {v : Pl F} {l : (AE F E)ˣ} (hl : l ∈ unitsAt E v) : absE F E l = 1 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hb : IsCompact (absE F E '' (Subtype.val '' {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v})) :=
    ((isCompact_isOpen_unitsAt v).1.image continuous_subtype_val).image GlobalTheory.Doubling.continuous_absE
  obtain ⟨C, hC⟩ := hb.bddAbove
  have key : ∀ m ∈ unitsAt E v, absE F E m ≤ 1 := fun m hm => by
    by_contra h
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.1 h)
    have hk' : m ^ k ∈ unitsAt E v := pow_mem hm k
    exact not_le.2 hk (by rw [← map_pow]; exact hC ⟨_, ⟨⟨_, hk'.1⟩, hk', rfl⟩, rfl⟩)
  refine le_antisymm (key l hl) ?_
  have h1 := key _ (inv_mem hl)
  calc (1 : ℝ≥0) = absE F E l * absE F E l⁻¹ := by rw [← map_mul, mul_inv_cancel, map_one]
    _ ≤ absE F E l * 1 := by gcongr
    _ = _ := mul_one _

end Haar

section Ops

variable {κ : Type} [Fintype κ]

open Classical in

def locOp (v : Pl F) (T : ((κ → AF F) → ℂ) → ((κ → AF F) → ℂ)) (φ : (κ → Fv F v) → ℂ) : (κ → Fv F v) → ℂ :=
  if h : ∃ φ₁, φ₁ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) T φ φ₁ then h.choose else 0

open Classical in

def locOpInf (T : ((κ → AF F) → ℂ) → ((κ → AF F) → ℂ)) (f : SInf F κ) : SInf F κ :=
  if h : ∃ f₁ : SInf F κ, Acts (evI F) T f f₁ then h.choose else 0

theorem locOp_mem (v : Pl F) (T : ((κ → AF F) → ℂ) → ((κ → AF F) → ℂ)) (φ : (κ → Fv F v) → ℂ) : locOp v T φ ∈ SB (κ → Fv F v) := by
  unfold locOp
  split_ifs with h
  exacts [h.choose_spec.1, zero_mem _]

theorem acts_locOp {v : Pl F} {T : ((κ → AF F) → ℂ) → ((κ → AF F) → ℂ)} {φ : (κ → Fv F v) → ℂ}
    (h : ∃ φ₁, φ₁ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) T φ φ₁) : Acts (evFin F v) T φ (locOp v T φ) := by
  rw [locOp, dif_pos h]
  exact h.choose_spec.2

theorem locOp_eq {v : Pl F} {T : ((κ → AF F) → ℂ) → ((κ → AF F) → ℂ)} {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v))
    (hφ₁ : φ₁ ∈ SB (κ → Fv F v)) (h : Acts (evFin F v) T φ φ₁) : locOp v T φ = φ₁ :=
  GlobalTheory.TensUniq.eq_of_tens_eq v φ _ _ hφ fun r hr => (acts_locOp ⟨φ₁, hφ₁, h⟩ r hr).symm.trans (h r hr)

theorem acts_locOpInf {T : ((κ → AF F) → ℂ) → ((κ → AF F) → ℂ)} {f : SInf F κ} (h : ∃ f₁ : SInf F κ, Acts (evI F) T f f₁) :
    Acts (evI F) T f (locOpInf T f) := by
  rw [locOpInf, dif_pos h]
  exact h.choose_spec

variable (F κ) in

theorem exists_rest_inf : ∃ r : ((κ → AF F) → ℂ), r 0 ≠ 0 ∧ ∀ f : SInf F κ, Rest (evI F) f r := by
  let φ : ∀ w : Pl F, (κ → Fv F w) → ℂ := fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  refine ⟨fun x => ∏ᶠ w, φ w fun i => evFin F w (x i), ?_, fun f => ⟨fun x z hz => ?_, ?_⟩⟩
  · beta_reduce
    rw [finprod_eq_one_of_forall_eq_one fun w => ?_]
    · exact one_ne_zero
    · simp only [φ, Pi.zero_apply, map_zero]
      rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
      rfl
  · have h : ∀ w i, evFin F w (z i) = 0 := fun w i => by
      rw [← partInf_of_at hz, partInf, Pi.smul_apply, smul_eq_mul, map_mul,
        show evFin F w (realAd F 1) = 0 from map_zero (evalV F w), zero_mul]
    simp only [Pi.add_apply, map_add, h, add_zero]
  · exact GlobalTheory.TensUniq.pure_mem_schA f φ (fun w => GlobalTheory.StdVacuum.indicator_mem_SB w) (Eventually.of_forall fun _ => rfl)

theorem eq_of_tens_inf {r : ((κ → AF F) → ℂ)} (h0 : r 0 ≠ 0) (hr : ∀ x z, At (evI F) z → r (x + z) = r x)
    {f g : (κ → mixedEmbedding.mixedSpace F) → ℂ} (h : tens (evI F) f r = tens (evI F) g r) : f = g := by
  funext y
  let z : κ → AF F := fun i => GlobalTheory.HeisSchA.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) 0
  have hz : At (evI F) z := fun u hu => funext fun i => GlobalTheory.HeisSchA.at_mk _ u hu
  have hy : (fun i => evI F (z i)) = y := funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
  have e := congrFun h z
  have hrz : r z = r 0 := by simpa using hr 0 z hz
  simp only [tens, hy, hrz] at e
  exact mul_right_cancel₀ h0 e

theorem locOpInf_eq {T : ((κ → AF F) → ℂ) → ((κ → AF F) → ℂ)} {f f₁ : SInf F κ} (h : Acts (evI F) T f f₁) : locOpInf T f = f₁ := by
  obtain ⟨r, h0, hr⟩ := exists_rest_inf F κ
  exact DFunLike.coe_injective
    (eq_of_tens_inf h0 (hr f).1 ((acts_locOpInf ⟨f₁, h⟩ r (hr f)).symm.trans (h r (hr f))))

theorem tens_lin {R : Type} (ev : AF F → R) (a b : ℂ) (φ φ' : (κ → R) → ℂ) (r : ((κ → AF F) → ℂ)) :
    tens ev (a • φ + b • φ') r = a • tens ev φ r + b • tens ev φ' r := by
  funext x
  simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem locOp_lin {v : Pl F} {T : ((κ → AF F) → ℂ) → ((κ → AF F) → ℂ)} (hT : IsLinearMap ℂ T)
    (hex : ∀ φ ∈ SB (κ → Fv F v), ∃ φ₁, φ₁ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) T φ φ₁) (a b : ℂ)
    {φ φ' : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) (hφ' : φ' ∈ SB (κ → Fv F v)) :
    locOp v T (a • φ + b • φ') = a • locOp v T φ + b • locOp v T φ' := by
  have hs : a • φ + b • φ' ∈ SB (κ → Fv F v) := add_mem ((SB _).smul_mem a hφ) ((SB _).smul_mem b hφ')
  obtain ⟨r, h0, hr⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have key : tens (evFin F v) (locOp v T (a • φ + b • φ')) r = tens (evFin F v) (a • locOp v T φ + b • locOp v T φ') r := by
    rw [← acts_locOp (hex _ hs) r (hr _ hs), tens_lin, tens_lin, hT.map_add, hT.map_smul, hT.map_smul,
      acts_locOp (hex _ hφ) r (hr _ hφ), acts_locOp (hex _ hφ') r (hr _ hφ')]
  funext t
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hrz : r (fun i => GlobalTheory.LatVac.liftV v (t i)) = r 0 := by simpa using (hr φ hφ).1 0 _ hz
  have e := congrFun key fun i => GlobalTheory.LatVac.liftV v (t i)
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hrz] at e
  exact mul_right_cancel₀ h0 e

theorem locOpInf_lin {T : ((κ → AF F) → ℂ) → ((κ → AF F) → ℂ)} (hT : IsLinearMap ℂ T)
    (hex : ∀ f : SInf F κ, ∃ f₁ : SInf F κ, Acts (evI F) T f f₁) (a b : ℂ) (f f' : SInf F κ) :
    locOpInf T (a • f + b • f') = a • locOpInf T f + b • locOpInf T f' := by
  obtain ⟨r, h0, hr⟩ := exists_rest_inf F κ
  refine DFunLike.coe_injective (eq_of_tens_inf h0 (hr f).1 ?_)
  rw [← acts_locOpInf (hex _) r (hr _)]
  change T (tens (evI F) (a • ⇑f + b • ⇑f') r) = tens (evI F) (a • ⇑(locOpInf T f) + b • ⇑(locOpInf T f')) r
  rw [tens_lin, tens_lin, hT.map_add, hT.map_smul, hT.map_smul, acts_locOpInf (hex _) r (hr _),
    acts_locOpInf (hex _) r (hr _)]

theorem locOp_of_fix {v : Pl F} {T : ((κ → AF F) → ℂ) → ((κ → AF F) → ℂ)} (hT : ∀ Φ ∈ schA F κ, T Φ = Φ) {φ : (κ → Fv F v) → ℂ}
    (hφ : φ ∈ SB (κ → Fv F v)) : locOp v T φ = φ := locOp_eq hφ hφ fun _ hr => hT _ hr.2

variable {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F}

open scoped GlobalTheory.VacAny in

theorem locOp_rho (co : Darboux Bf κ) {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) (v : Pl F) (u : V)
    {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) :
    Acts (evFin F v) (co.rho ψ (partFin v u)) φ (locOp v (co.rho ψ (partFin v u)) φ) ∧
      locOp v (co.rho ψ (partFin v u)) φ = schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v u) φ := by
  have e : GlobalTheory.LatVac.locCo co v (partFin v u) = GlobalTheory.LatVac.locCo co v u := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp [GlobalTheory.LatVac.locCo, partFin, GlobalTheory.LatVac.evFin_liftV]
  have h := GlobalTheory.VacBridge.rho_acts_locCo co ψ v _ (at_partFin v u) φ
  rw [e] at h
  have hm := GlobalTheory.SchrSB.schr_mem_SB ψ hψ v (GlobalTheory.LatVac.locCo co v u) φ hφ
  exact ⟨acts_locOp ⟨_, hm, h⟩, locOp_eq hφ hm h⟩

open GlobalTheory.ArchUniq Classical in

theorem locOpInf_rho (co : Darboux Bf κ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (u : V) (f : SInf F κ) :
    Acts (evI F) (co.rho ψ (partInf F u)) f (locOpInf (co.rho ψ (partInf F u)) f) ∧
      ⇑(locOpInf (co.rho ψ (partInf F u)) f) = schrF (trP F κ) (locV (co.e u).1, locV (co.e u).2) f := by
  have e : ∀ x : κ → AF F, locV (realAd F 1 • x) = locV x := fun x => funext fun i => by
    simp only [locV, Pi.smul_apply, smul_eq_mul, evI_eq_evIHom, map_mul]
    rw [← evI_eq_evIHom, evI_realAd_one, one_mul]
  have hg : ⇑(GlobalTheory.HeisSchA.archS f (locV (co.e u).2) (locV (co.e u).1)
      (trP F κ (locV (co.e u).1) (locV (co.e u).2) / 2)) = schrF (trP F κ) (locV (co.e u).1, locV (co.e u).2) f := by
    funext y
    rw [GlobalTheory.HeisSchA.archS_apply, GlobalTheory.Published.Metaplectic.eChar_apply, schrF, ContinuousLinearMap.neg_apply,
      GlobalTheory.HeisSchA.trL_apply]
    congr 2
    simp only [trP, dotProduct]
    push_cast
    ring
  have h := acts_rho_of_at_inf ψ hψ co _ (at_partInf u) f _ (by
    rw [hg, partInf, map_smul, Prod.smul_fst, Prod.smul_snd, e, e])
  exact ⟨acts_locOpInf ⟨_, h⟩, by rw [locOpInf_eq h, hg]⟩

end Ops

section Cone

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem smul_shiftA (H : Plane E n n₁) (H' : Plane E d d₁) (a : AF F) (l : (AE F E)ˣ) :
    a • shiftA H H' l = (a • l.1) • Matrix.vecMulVec (incV F H.x) (incV F H'.y) := (smul_assoc _ _ _).symm

theorem smul_shiftB (H : Plane E n n₁) (H' : Plane E d d₁) (a : AF F) (l : (AE F E)ˣ) :
    a • shiftB σ H H' l = cA σ (a • l.1) • Matrix.vecMulVec (incV F H.y) (incV F H'.x) := by
  rw [map_smul]
  exact (smul_assoc _ _ _).symm

theorem acts_locOp_om (hA : ActsEx) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
    (hP : IsPair B M χX χW om r s r' s') {v : Pl F} {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) {h : UA σ W.J}
    (hh : h ∈ UAt σ W (evFin F v)) {φ : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) :
    Acts (evFin F v) (om (g, h)) φ (locOp v (om (g, h)) φ) :=
  acts_locOp ((hA F E σ B n d X W M χX χW om r s r' s' hP v).1 g hg h hh φ hφ).exists

variable (B : Base F E) (M : Model σ X W) (om : Rep σ X W)

section Fin

variable (v : Pl F) (ev : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ)
  (K : Subgroup (UA σ X.J)) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v)))
  (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ)

def coneFinInt (φ : (Fin n × Fin d → Fv F v) → ℂ) (k : UA σ X.J) (l : (AE F E)ˣ) (y : Fin n₁ × Fin d₁ → Fv F v) : ℂ :=
  ev (locOp v (M.co.rho B.ψ (partFin v (u l))) (locOp v (om (k, 1)) φ)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z

def coneFin (φ : (Fin n × Fin d → Fv F v) → ℂ) : (Fin n₁ × Fin d₁ → Fv F v) → ℂ :=
  fun y => ∫ k, ∫ l, coneFinInt B M om v ev u ν z φ k.1 l.1 y ∂μ ∂μK

variable {B M om v ev K μK μ u ν z}

open scoped GlobalTheory.VacAny in

theorem coneFinInt_eq (hψ : Continuous B.ψ) (φ : (Fin n × Fin d → Fv F v) → ℂ) (k : UA σ X.J) {l : (AE F E)ˣ}
    (hl : l ∈ idelesAt E (evFin F v)) (y : Fin n₁ × Fin d₁ → Fv F v) :
    coneFinInt B M om v ev u ν z φ k l y =
      ev (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (u l)) (locOp v (om (k, 1)) φ)) y * (ν l : ℂ) *
        ((absEv F E v (unitFin F E v l) : ℝ) : ℂ) ^ z := by
  rw [coneFinInt, (locOp_rho M.co hψ v (u l) (locOp_mem v _ φ)).2, absE_of_mem hl]

open scoped GlobalTheory.VacAny in

theorem coneFinInt_lin (hψ : Continuous B.ψ) {k : UA σ X.J}
    (hk : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (om (k, 1)) φ φ₁)
    (a b : ℂ) {φ φ' : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hφ' : φ' ∈ SB (Fin n × Fin d → Fv F v)) (l : (AE F E)ˣ) (y : Fin n₁ × Fin d₁ → Fv F v) :
    coneFinInt B M om v ev u ν z (a • φ + b • φ') k l y =
      a * coneFinInt B M om v ev u ν z φ k l y + b * coneFinInt B M om v ev u ν z φ' k l y := by
  have hT : IsLinearMap ℂ (M.co.rho B.ψ (partFin v (u l))) :=
    ⟨fun f g => funext fun x => mul_add _ _ _, fun c f => funext fun x => mul_left_comm _ _ _⟩
  simp only [coneFinInt]
  rw [locOp_lin (om (k, 1)).isLinear hk a b hφ hφ', locOp_lin hT
    (fun f hf => ⟨_, locOp_mem v _ f, (locOp_rho M.co hψ v (u l) hf).1⟩) a b (locOp_mem _ _ _) (locOp_mem _ _ _),
    map_add, map_smul, map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem coneFin_lin (hψ : Continuous B.ψ)
    (hk : ∀ k ∈ KAt K (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃ φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (om (k, 1)) φ φ₁)
    (a b : ℂ) {φ φ' : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hφ' : φ' ∈ SB (Fin n × Fin d → Fv F v)) (y : Fin n₁ × Fin d₁ → Fv F v)
    (h1 : ∀ k : KAt K (evFin F v), Integrable (fun l : idelesAt E (evFin F v) => coneFinInt B M om v ev u ν z φ k.1 l.1 y) μ)
    (h1' : ∀ k : KAt K (evFin F v), Integrable (fun l : idelesAt E (evFin F v) => coneFinInt B M om v ev u ν z φ' k.1 l.1 y) μ)
    (h2 : Integrable (fun k : KAt K (evFin F v) => ∫ l, coneFinInt B M om v ev u ν z φ k.1 l.1 y ∂μ) μK)
    (h2' : Integrable (fun k : KAt K (evFin F v) => ∫ l, coneFinInt B M om v ev u ν z φ' k.1 l.1 y ∂μ) μK) :
    coneFin B M om v ev K μK μ u ν z (a • φ + b • φ') y =
      a * coneFin B M om v ev K μK μ u ν z φ y + b * coneFin B M om v ev K μK μ u ν z φ' y := by
  simp only [coneFin]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h2.const_mul a) (h2'.const_mul b)]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  beta_reduce
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((h1 k).const_mul a) ((h1' k).const_mul b)]
  exact integral_congr_ae (Eventually.of_forall fun l => coneFinInt_lin hψ (hk k.1 k.2) a b hφ hφ' l.1 y)

theorem coneFin_of_fixed (hK : IsNormK K (evFin F v) μK) {φ : (Fin n × Fin d → Fv F v) → ℂ}
    (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) (hfix : ∀ k ∈ KAt K (evFin F v), Acts (evFin F v) (om (k, 1)) φ φ)
    (y : Fin n₁ × Fin d₁ → Fv F v) :
    coneFin B M om v ev K μK μ u ν z φ y =
      ∫ l, ev (locOp v (M.co.rho B.ψ (partFin v (u l.1))) φ) y * (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z ∂μ := by
  haveI : IsProbabilityMeasure μK := ⟨hK.2⟩
  have e : ∀ k : KAt K (evFin F v), locOp v (om (k.1, 1)) φ = φ := fun k => locOp_eq hφ hφ (hfix k.1 k.2)
  simp only [coneFin, coneFinInt, e]
  simp

example : coneFin B M om v ev K μK μ u ν z 0 = 0 := by
  have t : ∀ r, tens (evFin F v) (0 : (Fin n × Fin d → Fv F v) → ℂ) r = 0 := fun r => funext fun x => zero_mul _
  have e : ∀ k, locOp v (om (k, 1)) 0 = 0 := fun k =>
    locOp_eq (zero_mem _) (zero_mem _) fun r _ => by rw [t, map_zero]
  have e' : ∀ w, locOp v (M.co.rho B.ψ w) 0 = 0 := fun w =>
    locOp_eq (zero_mem _) (zero_mem _) fun r _ => by rw [t]; exact funext fun x => mul_zero _
  funext y
  simp [coneFin, coneFinInt, e, e']

end Fin

section Inf

variable (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
  (K : Subgroup (UA σ X.J)) (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F)))
  (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ)

def coneInfInt (f : SInf F (Fin n × Fin d)) (k : UA σ X.J) (l : (AE F E)ˣ) : SInf F (Fin n₁ × Fin d₁) :=
  ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) • ei (locOpInf (M.co.rho B.ψ (partInf F (u l))) (locOpInf (om (k, 1)) f))

def coneInfFun (f : SInf F (Fin n × Fin d)) : (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun y => ∫ k, ∫ l, coneInfInt B M om ei u ν z f k.1 l.1 y ∂μ ∂μK

open Classical in

def coneInf (f : SInf F (Fin n × Fin d)) : SInf F (Fin n₁ × Fin d₁) :=
  if h : ∃ g : SInf F (Fin n₁ × Fin d₁), ⇑g = coneInfFun B M om ei K μK μ u ν z f then h.choose else 0

variable {B M om ei K μK μ u ν z}

theorem coneInfInt_apply (f : SInf F (Fin n × Fin d)) (k : UA σ X.J) (l : (AE F E)ˣ)
    (y : Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) :
    coneInfInt B M om ei u ν z f k l y =
      ei (locOpInf (M.co.rho B.ψ (partInf F (u l))) (locOpInf (om (k, 1)) f)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z :=
  (mul_comm _ _).trans (mul_assoc _ _ _).symm

theorem coe_coneInf {f : SInf F (Fin n × Fin d)}
    (h : ∃ g : SInf F (Fin n₁ × Fin d₁), ⇑g = coneInfFun B M om ei K μK μ u ν z f) :
    ⇑(coneInf B M om ei K μK μ u ν z f) = coneInfFun B M om ei K μK μ u ν z f := by
  rw [coneInf, dif_pos h]
  exact h.choose_spec

theorem coneInf_eq {f : SInf F (Fin n × Fin d)} {g : SInf F (Fin n₁ × Fin d₁)}
    (h : ⇑g = coneInfFun B M om ei K μK μ u ν z f) : coneInf B M om ei K μK μ u ν z f = g :=
  DFunLike.coe_injective ((coe_coneInf ⟨g, h⟩).trans h.symm)

theorem coneInfInt_lin (hψ : IsStd B.ψ) {k : UA σ X.J}
    (hk : ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f f₁)
    (a b : ℂ) (f f' : SInf F (Fin n × Fin d)) (l : (AE F E)ˣ) :
    coneInfInt B M om ei u ν z (a • f + b • f') k l =
      a • coneInfInt B M om ei u ν z f k l + b • coneInfInt B M om ei u ν z f' k l := by
  have hT : IsLinearMap ℂ (M.co.rho B.ψ (partInf F (u l))) :=
    ⟨fun f g => funext fun x => mul_add _ _ _, fun c f => funext fun x => mul_left_comm _ _ _⟩
  simp only [coneInfInt]
  rw [locOpInf_lin (om (k, 1)).isLinear hk, locOpInf_lin hT fun g => ⟨_, (locOpInf_rho M.co hψ (u l) g).1⟩,
    map_add, map_smul, map_smul, smul_add, smul_comm _ a, smul_comm _ b]

theorem mem_KAt_inf {B : Base F E} {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {k : UA σ X.J} :
    k ∈ KAt K (evI F) ↔ k ∈ KInf σ X B.emb := by
  refine ⟨fun h => ⟨h.2, ((hK k).1 h.1).1⟩, fun h => ⟨(hK k).2 ⟨h.2, fun y hy => ?_⟩, h.1⟩⟩
  have h0 : realAd F 1 • y = 0 := by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, -, x, -, rfl⟩ := hy
      rw [smul_comm]
      exact at_partInf _ a ha
    | zero => exact smul_zero _
    | add _ _ _ _ h1 h2 => rw [smul_add, h1, h2, add_zero]
    | neg _ _ h1 => rw [smul_neg, h1, neg_zero]
  have key : ∀ g ∈ UAtSub σ X (evI F), mat g *ᵥ y = y := fun g hg => by
    have h1 : (mat g - 1) *ᵥ y = 0 := by
      rw [← partInf_of_at hg, partInf, Matrix.smul_mulVec, ← Matrix.mulVec_smul, h0, Matrix.mulVec_zero]
    rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1
  rw [key k h.1, key k⁻¹ (inv_mem (show k ∈ UAtSub σ X (evI F) from h.1))]
  exact ⟨hy, hy⟩

end Inf

end Cone

example (v : Pl F) (a : (Fv F v)ˣ) (ha : ‖a.1‖₊ ≠ 1) :
    ideleAt F E v (Units.map (algebraMap (Fv F v) (Fv F v ⊗[F] E)).toMonoidHom a) ∉ unitsAt E v := fun h => by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 := absE_of_mem_unitsAt h
  rw [GlobalTheory.Doubling.absE_ideleAt, GlobalTheory.Doubling.absEv_algebraMap] at h1
  exact ha ((pow_eq_one_iff_of_nonneg zero_le' Module.finrank_pos.ne').1 h1)

example (v : Pl F) : ideleAt F E v (-1) ∈ unitsAt E v := by
  refine ⟨ideleAt_mem v _, ?_⟩
  change unitFin F E v (ideleAt F E v (-1)) ∈ (intLoc F E v).toSubmonoid.units
  rw [GlobalTheory.Doubling.unitFin_ideleAt_self]
  exact (Submonoid.mem_units_iff _ _).2 ⟨(intLoc F E v).neg_mem (one_mem _), (intLoc F E v).neg_mem (one_mem _)⟩

example {κ : Type} [Fintype κ] (v : Pl F) (t : κ → Fv F v) {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) :
    locOp v (fun Φ x => Φ (x + fun i => GlobalTheory.LatVac.liftV v (t i))) φ = fun x => φ (x + t) := by
  refine locOp_eq hφ ⟨hφ.1.comp_continuous (continuous_add_const t),
    hφ.2.comp_homeomorph (Homeomorph.addRight t)⟩ fun r hr => funext fun x => ?_
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  simp only [tens, hr.1 x _ hz, Pi.add_apply, map_add, GlobalTheory.LatVac.evFin_liftV]
  rfl

example {b a' : ℕ} (B : Base F E) (G : Geo σ (b + 2) a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (v : Pl F)
    (ev : ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ)
    (K : Subgroup (UA σ G.V.J)) (hK : IsCompact (K : Set (UA σ G.V.J))) :
    ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) → (Fin b × Fin (b + a') → Fv F v) → ℂ :=
  coneFin B G.M om v ev K (existsUnique_isNormK hK _).choose (existsUnique_isNormE E v).choose (shiftA H H') X.ν
    ((b + 2 - a') / 2)

example {a b : ℕ} (B : Base F E) (G : Geo σ a (b + 2)) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b))
    (X : Chars F E) (om' : Rep σ G.V' G.W) (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
    (K : Subgroup (UA σ G.V'.J)) (hK : IsCompact (K : Set (UA σ G.V'.J))) :
    SInf F (Fin (b + 2) × Fin (a + (b + 2))) → SInf F (Fin b × Fin (a + b)) :=
  coneInf B G.M' om' ei K (existsUnique_isNormK hK _).choose (exists_haar_idelesAt E (evI F)).choose (shiftB σ H H') X.ν
    ((a - (b + 2)) / 2 + 1)

end GlobalTheory.ThK

end
