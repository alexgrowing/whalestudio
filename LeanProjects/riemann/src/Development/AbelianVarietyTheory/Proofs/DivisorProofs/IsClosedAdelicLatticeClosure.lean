import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact

noncomputable section

namespace GlobalTheory.LatHatClosed

open scoped TensorProduct RestrictedProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU Topology

variable (F : Type) [Field F] [NumberField F]

theorem isCompact_integralFinite :
    IsCompact {b : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), b.1 v ∈ v.adicCompletionIntegers F} := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

def intAd : AddSubgroup (AF F) where
  carrier := {a | evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := ⟨show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0 from map_zero _,
    fun v => by rw [map_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, fun v => ?_⟩
    · simp only [evI] at ha hb ⊢
      rw [show (a + b).1 = a.1 + b.1 from rfl, map_add, ha, hb, add_zero]
    · rw [map_add]; exact add_mem (ha' v) (hb' v)
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, fun v => ?_⟩
    · simp only [evI] at ha ⊢
      rw [show (-a).1 = -a.1 from rfl, map_neg, ha, neg_zero]
    · rw [map_neg]; exact neg_mem (ha' v)

theorem isCompact_intAd : IsCompact (intAd F : Set (AF F)) := by
  have e : (intAd F : Set (AF F)) = (({0} : Set (InfiniteAdeleRing F)) ×ˢ
      {b : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), b.1 v ∈ v.adicCompletionIntegers F} : Set _) := by
    ext a
    simp only [SetLike.mem_coe, Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf_eq]
    show (evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ↔ _
    have h1 : evI F a = 0 ↔ a.1 = 0 := by
      simp only [evI]; exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff
    rw [h1]
    rfl
  rw [e]
  exact isCompact_singleton.prod (isCompact_integralFinite F)

theorem incV_add {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ} (x y : Fin n → E) :
    incV F (x + y) = incV F x + incV F y := by
  funext i; simp [incV, map_add]

theorem incV_zero {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ} :
    incV F (0 : Fin n → E) = 0 := by
  funext i; simp [incV]

theorem incV_zsmul {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ} (m : ℤ) (x : Fin n → E) :
    incV F (m • x) = m • incV F x := by
  funext i; simp [incV, map_zsmul]

theorem isClosed_latHat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (X : Spc F E n), X.L.IsLattice E → IsClosed ((latHat X : AddSubgroup (Fin n → AE F E)) : Set (Fin n → AE F E)) := by
  intro F E _ _ _ _ _ n X hL
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  obtain ⟨s, hs⟩ := Submodule.FG.restrictScalars (R := ℤ) hL.fg
  let ψ : (s → AF F) →+ (Fin n → AE F E) :=
    { toFun := fun c => ∑ i, c i • incV F (i : Fin n → E)
      map_zero' := by simp
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] }
  let P : AddSubgroup (s → AF F) := AddSubgroup.pi Set.univ (fun _ => intAd F)
  have hψc : Continuous ψ :=
    continuous_finset_sum _ fun i _ => by
      show Continuous fun c : s → AF F => c i • incV F (i : Fin n → E)
      exact (continuous_apply i : Continuous fun c : s → AF F => c i).smul
        (continuous_const : Continuous fun _ : s → AF F => incV F (i : Fin n → E))
  have hPc : IsCompact (P : Set (s → AF F)) := by
    have : (P : Set (s → AF F)) = Set.pi Set.univ (fun _ => (intAd F : Set (AF F))) := by
      ext c; simp [P, AddSubgroup.mem_pi]
    rw [this]; exact isCompact_univ_pi fun _ => isCompact_intAd F
  have hsL : ∀ i ∈ s, i ∈ X.L := fun i hi => by
    have : i ∈ Submodule.span ℤ (s : Set (Fin n → E)) := Submodule.subset_span hi
    rw [hs] at this; exact this
  have key : ∀ x ∈ Submodule.span ℤ (s : Set (Fin n → E)), ∀ a ∈ intAd F, a • incV F x ∈ P.map ψ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      intro a ha
      refine ⟨Pi.single ⟨y, hy⟩ a, ?_, ?_⟩
      · intro i _
        by_cases h : i = ⟨y, hy⟩
        · subst h; simpa using ha
        · simp [Pi.single_apply, h, zero_mem]
      · simp [ψ, Pi.single_apply, ite_smul]
    | zero =>
      intro a _
      rw [incV_zero, smul_zero]; exact zero_mem _
    | add y y' _ _ ih ih' =>
      intro a ha
      rw [incV_add, smul_add]; exact add_mem (ih a ha) (ih' a ha)
    | smul m y _ ih =>
      intro a ha
      rw [incV_zsmul, smul_comm, ← smul_assoc]
      exact ih (m • a) (zsmul_mem ha m)
  have heq : latHat X = P.map ψ := by
    apply le_antisymm
    · refine (AddSubgroup.closure_le _).2 ?_
      rintro z ⟨a, ha0, hav, x, hx, rfl⟩
      have hx' : x ∈ Submodule.span ℤ (s : Set (Fin n → E)) := by rw [hs]; exact hx
      exact key x hx' a ⟨ha0, hav⟩
    · rintro z ⟨c, hc, rfl⟩
      exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure
        ⟨c i, (hc i trivial).1, (hc i trivial).2, i, hsL i i.2, rfl⟩
  rw [heq, AddSubgroup.coe_map]
  exact (hPc.image hψc).isClosed

end GlobalTheory.LatHatClosed
