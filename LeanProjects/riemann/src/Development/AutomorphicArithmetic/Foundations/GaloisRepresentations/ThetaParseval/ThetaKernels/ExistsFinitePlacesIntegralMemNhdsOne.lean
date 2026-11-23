import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.LatticeBasics.BadFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleEqZeroOfComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP
section SlopeTestRemainingChoices
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}
private def fixG_pk {R : Type} [Ring R] (σ : E →ₐ[F] E) (X : Spc F E n) (f : AE F E →+* R) : Subgroup (UA σ X.J) where
  carrier := {g | (mat g).map f = 1}
  one_mem' := Matrix.map_one f (map_zero _) (map_one _)
  mul_mem' := fun {a b} ha hb => by
    show (mat (a * b)).map f = 1
    rw [Euler.mm, Matrix.map_mul]
    exact (congrArg₂ (· * ·) ha hb).trans (mul_one _)
  inv_mem' := fun {a} ha => by
    have e : (mat a⁻¹).map f * (mat a).map f = 1 := by
      rw [← Matrix.map_mul, ← Euler.mm, inv_mul_cancel]
      exact Matrix.map_one f (map_zero _) (map_one _)
    rw [show (mat a).map f = 1 from ha, mul_one] at e
    exact e
private theorem gOff_parts_pk {S : Finset (Pl F)} {c : UA σ X.J} (h : c ∈ gOff σ X S) :
    (∀ w : InfinitePlace F, (mat c).map (compInf F E w) = 1) ∧ ∀ v ∈ S, OffAt v c := by
  constructor
  · intro w
    have : gOff σ X S ≤ fixG_pk σ X (compInf F E w : AE F E →+* _) :=
      (Subgroup.closure_le _).2 fun g hg => hg.1 w
    exact this h
  · intro v hv
    have : gOff σ X S ≤ fixG_pk σ X (compFin F E v : AE F E →+* _) :=
      (Subgroup.closure_le _).2 fun g hg => hg.2 v hv
    exact this h
private theorem eq_one_of_parts_pk {c : UA σ X.J} (h1 : ∀ w : InfinitePlace F, (mat c).map (compInf F E w) = 1)
    (h2 : ∀ v, OffAt v c) : c = 1 := by
  refine Subtype.ext (Units.ext ?_)
  show mat c = 1
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.SWOpFin.tens_eq_zero_of_comp (fun v => ?_) (fun w => ?_))
  · have e : (mat c).map (compFin F E v) = (1 : Matrix (Fin n) (Fin n) (AE F E)).map (compFin F E v) := by
      rw [Matrix.map_one (compFin F E v) (map_zero _) (map_one _)]
      exact h2 v
    rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun e i) j)
  · have e : (mat c).map (compInf F E w) = (1 : Matrix (Fin n) (Fin n) (AE F E)).map (compInf F E w) := by
      rw [Matrix.map_one (compInf F E w) (map_zero _) (map_one _)]
      exact h1 w
    rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun e i) j)
end SlopeTestRemainingChoices
theorem UpperTheory.exists_finite_places_integral_mem_nhds_one :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n}, _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B n 0 → IsCompact {g : UA σ X.J | IntAll g} → (∀ S, IsClosed (gOff σ X S : Set (UA σ X.J))) → ∀ {N : Set (UA σ X.J)}, N ∈ 𝓝 (1 : UA σ X.J) → ∃ S₀ : Finset (Pl F), ∀ c ∈ gOff σ X S₀, IntAll c → c ∈ N := by
  intro F E _ _ _ _ _ σ B n X _ _ hK hC N hN
  classical
  have hs : IsCompact ({g : UA σ X.J | IntAll g} ∩ (interior N)ᶜ) := hK.inter_right isOpen_interior.isClosed_compl
  have anti : ∀ {S T : Finset (Pl F)}, S ⊆ T → (gOff σ X T : Set (UA σ X.J)) ⊆ gOff σ X S := fun {S T} h =>
    Subgroup.closure_mono fun g hg => ⟨hg.1, fun v hv => hg.2 v (h hv)⟩
  have hd : Directed (· ⊇ ·) (fun S : Finset (Pl F) => (gOff σ X S : Set (UA σ X.J))) := fun S T =>
    ⟨S ∪ T, anti Finset.subset_union_left, anti Finset.subset_union_right⟩
  have hi : ({g : UA σ X.J | IntAll g} ∩ (interior N)ᶜ) ∩ ⋂ S : Finset (Pl F), (gOff σ X S : Set (UA σ X.J)) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun c hc => ?_
    have h := Set.mem_iInter.1 hc.2
    have e : c = 1 := eq_one_of_parts_pk (gOff_parts_pk (h ∅)).1
      fun v => (gOff_parts_pk (h {v})).2 v (Finset.mem_singleton_self v)
    exact hc.1.2 (e ▸ mem_interior_iff_mem_nhds.2 hN)
  obtain ⟨S, hS⟩ := hs.elim_directed_family_closed _ hC hi hd
  refine ⟨S, fun c hc hI => ?_⟩
  by_contra hn
  have hm : c ∈ ({g : UA σ X.J | IntAll g} ∩ (interior N)ᶜ) ∩ (gOff σ X S : Set (UA σ X.J)) :=
    ⟨⟨hI, fun h => hn (interior_subset h)⟩, hc⟩
  rw [hS] at hm
  exact hm
end
