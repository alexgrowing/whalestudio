import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompMemOfIsStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIOneSubEInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.ConeEuler.CompIntegral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {n : ℕ} {X : Spc F E n} {K : Subgroup (UA σ X.J)}

theorem list_prod_map_single {α M : Type} [Monoid M] (l : List α) (hl : l.Nodup) {w : α} (hw : w ∈ l) (f : α → M)
    (hf : ∀ v ∈ l, v ≠ w → f v = 1) : (l.map f).prod = f w := by
  induction l with
  | nil => exact absurd hw List.not_mem_nil
  | cons x xs ih =>
    rw [List.map_cons, List.prod_cons]
    obtain ⟨hx, hxs⟩ := List.nodup_cons.1 hl
    by_cases h : x = w
    · subst h
      rw [List.prod_eq_one, mul_one]
      intro y hy
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hy
      exact hf v (List.mem_cons_of_mem _ hv) fun e => hx (e ▸ hv)
    · rw [hf x List.mem_cons_self h, one_mul]
      exact ih hxs ((List.mem_cons.1 hw).resolve_left (Ne.symm h)) fun v hv => hf v (List.mem_cons_of_mem _ hv)

def archK (hK : IsStab B K) : K →* KAt K (evI F) :=
  ((compArch σ X.J).comp K.subtype).codRestrict _ fun k =>
    ⟨(StabComp.comp_mem_of_isStab F E σ B n X K hK k.1 k.2).2, compArch_mem k.1⟩

def atK (hK : IsStab B K) (v : Pl F) : K →* KAt K (evFin F v) :=
  ((compAt σ X.J v).comp K.subtype).codRestrict _ fun k =>
    ⟨(StabComp.comp_mem_of_isStab F E σ B n X K hK k.1 k.2).1 v, compAt_mem v k.1⟩

def compT (hK : IsStab B K) (T : Finset (Pl F)) : K →* KAt K (evI F) × ((v : T) → KAt K (evFin F v.1)) :=
  (archK hK).prod (Pi.monoidHom fun v : T => atK hK v.1)

theorem continuous_compT (hK : IsStab B K) (T : Finset (Pl F)) : Continuous (compT hK T) := by
  obtain ⟨h1, h2⟩ := continuous_components F E σ n X.J
  refine Continuous.prodMk ((h2.comp continuous_subtype_val).subtype_mk _) (continuous_pi fun v => ?_)
  exact ((h1 v.1).comp continuous_subtype_val).subtype_mk _

theorem surjective_compT (hK : IsStab B K) (T : Finset (Pl F)) : Function.Surjective (compT hK T) := by
  classical
  rintro ⟨a, b⟩
  set l : List T := (Finset.univ : Finset T).toList with hl
  set k0 : UA σ X.J := a.1 * (l.map fun v => (b v).1).prod with hk0
  have hmem : k0 ∈ K := mul_mem a.2.1 (K.list_prod_mem fun x hx => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
    exact (b v).2.1)
  refine ⟨⟨k0, hmem⟩, Prod.ext (Subtype.ext ?_) (funext fun w => Subtype.ext ?_)⟩
  · change compArch σ X.J k0 = a.1
    rw [hk0, map_mul, map_list_prod, ((SuppOne.comp_of_supp F E σ n X a.1).2 a.2.2).1, List.map_map,
      List.prod_eq_one, mul_one]
    intro y hy
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hy
    exact ((SuppOne.comp_of_supp F E σ n X (b v).1).1 v.1 (b v).2.2).2.1
  · change compAt σ X.J w.1 k0 = (b w).1
    rw [hk0, map_mul, map_list_prod, ((SuppOne.comp_of_supp F E σ n X a.1).2 a.2.2).2 w.1, one_mul, List.map_map,
      list_prod_map_single l (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ w))]
    · exact ((SuppOne.comp_of_supp F E σ n X (b w).1).1 w.1 (b w).2.2).1
    · intro v _ hv
      exact ((SuppOne.comp_of_supp F E σ n X (b v).1).1 v.1 (b v).2.2).2.2 w.1 fun e => hv (Subtype.ext e.symm)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem integral_components : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n r s : ℕ} {X : Spc F E n}, B.IsGood σ → X.IsHerm σ B r s →
    ∀ {K : Subgroup (UA σ X.J)}, IsStab B K →
    ∀ (μK : Measure K), μK.IsHaarMeasure →
    ∀ (μKI : Measure (KAt K (evI F))), IsNormK K (evI F) μKI →
    ∀ (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))), (∀ v, IsNormK K (evFin F v) (μKv v)) →
    ∃ κK : ℝ, 0 < κK ∧ ∀ (T : Finset (Pl F)) (a : UA σ X.J → ℂ) (b : Pl F → UA σ X.J → ℂ),
      Integrable (fun k : KAt K (evI F) => a k.1) μKI →
      (∀ v ∈ T, Integrable (fun k : KAt K (evFin F v) => b v k.1) (μKv v)) →
      Integrable (fun k : K => a (compArch σ X.J k.1) * ∏ v ∈ T, b v (compAt σ X.J v k.1)) μK ∧
      ∫ k : K, a (compArch σ X.J k.1) * ∏ v ∈ T, b v (compAt σ X.J v k.1) ∂μK =
        κK * (∫ k : KAt K (evI F), a k.1 ∂μKI) * ∏ v ∈ T, ∫ k : KAt K (evFin F v), b v k.1 ∂(μKv v) := by
  intro F E _ _ _ _ _ σ B n r s X hB hX K hK μK hμK μKI hKI μKv hKv
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
  have hKc : IsCompact (K : Set (UA σ X.J)) := by
    have e : (K : Set (UA σ X.J)) = (GlobalTheory.StabHaar.stabK (σ := σ) B X : Set (UA σ X.J)) := Set.ext fun g => hK g
    obtain ⟨C, hC, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B n X r s hB hX
    rw [e]
    exact hC.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B X (GlobalTheory.T.isClosed_adelic_lattice_closure F E n X hX.lat)) hsub
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  haveI : CompactSpace (KAt K (evI F)) := isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)
  haveI : ∀ v : Pl F, CompactSpace (KAt K (evFin F v)) := fun v => isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)
  haveI : IsFiniteMeasure μK := inferInstance
  have hpos : 0 < μK Set.univ := (isOpen_univ.measure_pos μK Set.univ_nonempty)
  refine ⟨(μK Set.univ).toReal, ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _), fun T a b ha hb => ?_⟩
  haveI := hKI.1
  haveI : IsProbabilityMeasure μKI := ⟨hKI.2⟩
  haveI := fun v => (hKv v).1
  haveI : ∀ v, IsProbabilityMeasure (μKv v) := fun v => ⟨(hKv v).2⟩
  set π := CompIntegral.compT hK T with hπdef
  have hπc : Continuous π := CompIntegral.continuous_compT hK T
  haveI : ∀ v : Pl F, MeasurableMul (KAt K (evFin F v)) := fun v => inferInstance
  haveI : MeasurableMul (KAt K (evI F)) := inferInstance
  haveI : ∀ v : Pl F, BorelSpace (KAt K (evFin F v)) := fun v => inferInstance
  haveI : ∀ v : Pl F, SecondCountableTopology (KAt K (evFin F v)) := fun v => inferInstance
  haveI : ∀ v : Pl F, IsTopologicalGroup (KAt K (evFin F v)) := fun v => inferInstance
  haveI hpiH : (Measure.pi fun v : T => μKv v.1).IsHaarMeasure := Measure.pi.isHaarMeasure _
  set P := μKI.prod (Measure.pi fun v : T => μKv v.1) with hP
  haveI hPH : P.IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  have hPu : P Set.univ = 1 := measure_univ
  haveI : Measure.IsMulLeftInvariant (μK.map π) := isMulLeftInvariant_map π.toMulHom hπc.measurable (CompIntegral.surjective_compT hK T)
  have h1 := Measure.isMulInvariant_eq_smul_of_compactSpace (μK.map π) P
  have h2 : μK.map π Set.univ = μK Set.univ := by
    rw [Measure.map_apply hπc.measurable MeasurableSet.univ, Set.preimage_univ]
  have h3 : ((Measure.haarScalarFactor (μK.map π) P : ℝ≥0) : ENNReal) = μK Set.univ := by
    have := congrArg (fun m : Measure _ => m Set.univ) h1
    simp only [Measure.smul_apply, hPu, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    rw [← h2, this]
  have hν : μK.map π = μK Set.univ • P := by
    rw [h1, ENNReal.smul_def, h3]
  set f : KAt K (evI F) × ((v : T) → KAt K (evFin F v.1)) → ℂ :=
    fun x => a x.1.1 * ∏ v : T, b v.1 (x.2 v).1 with hf
  have hcomp : (fun k : K => a (compArch σ X.J k.1) * ∏ v ∈ T, b v (compAt σ X.J v k.1)) = f ∘ π := by
    funext k
    show a (compArch σ X.J k.1) * ∏ v ∈ T, b v (compAt σ X.J v k.1) = a (π k).1.1 * ∏ v : T, b v.1 ((π k).2 v).1
    rw [← Finset.prod_coe_sort T]
    rfl
  have hfP : Integrable f P := ha.mul_prod (Integrable.fintype_prod_dep fun v : T => hb v.1 v.2)
  have hfν : Integrable f (μK.map π) := by
    rw [hν]; exact hfP.smul_measure (measure_ne_top _ _)
  refine ⟨hcomp ▸ (integrable_map_measure hfν.aestronglyMeasurable hπc.measurable.aemeasurable).1 hfν, ?_⟩
  have hI := integral_map hπc.measurable.aemeasurable hfν.aestronglyMeasurable
  have hPint : ∫ x, f x ∂P = (∫ k, a k.1 ∂μKI) * ∏ v ∈ T, ∫ k, b v k.1 ∂(μKv v) := by
    rw [hP, hf, integral_prod_mul (fun x : KAt K (evI F) => a x.1) (fun y : (v : T) → KAt K (evFin F v.1) => ∏ v : T, b v.1 (y v).1),
      integral_fintype_prod_eq_prod (fun v : T => fun k : KAt K (evFin F v.1) => b v.1 k.1)]
    exact congrArg _ (Finset.prod_coe_sort T fun v => ∫ k, b v k.1 ∂(μKv v))
  rw [hcomp, Function.comp_def, ← hI, hν, integral_smul_measure, hPint, Complex.real_smul, mul_assoc]

end GlobalTheory.ThK.ConeEuler.CompIntegral
