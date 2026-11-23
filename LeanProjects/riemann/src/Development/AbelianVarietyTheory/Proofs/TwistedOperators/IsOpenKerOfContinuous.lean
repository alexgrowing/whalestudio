import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PositiveTwistAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrbitLocallyConstant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open Filter Topology

noncomputable section
namespace GlobalTheory.RootEx.UniformLattices

theorem eq_one_of_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hp : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have h1 : ‖(∑ k ∈ Finset.range n, z ^ k) - n‖ ≤ n / 2 := by
    have : (∑ k ∈ Finset.range n, z ^ k) - n = ∑ k ∈ Finset.range n, (z ^ k - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => (h k).le).trans ?_
    simp; linarith
  have h2 : (n : ℝ) / 2 ≤ ‖∑ k ∈ Finset.range n, z ^ k‖ := by
    have := norm_sub_norm_le (n : ℂ) (∑ k ∈ Finset.range n, z ^ k)
    rw [norm_sub_rev, Complex.norm_natCast] at this
    linarith
  have h3 := h n
  rw [← geom_sum_mul, norm_mul] at h3
  rw [div_lt_iff₀ hp] at hn
  nlinarith

section Lattices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_ker_of_cball (μ : kˣ →* ℂˣ) (s : kˣ) (h : ∀ x : kˣ, (x : k) - 1 ∈ cball s → μ x = 1) :
    IsOpen (μ.ker : Set kˣ) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have : (fun x : kˣ => (x : k) - 1) ⁻¹' cball s ∈ 𝓝 (1 : kˣ) :=
    ((isOpen_cball s).preimage (Units.continuous_val.sub continuous_const)).mem_nhds (by simp [cball])
  exact mem_of_superset this h

theorem isOpen_ker_of_continuous (μ : kˣ →* ℂˣ) (hμ : Continuous μ) : IsOpen (μ.ker : Set kˣ) := by
  have hV : {u | ‖((μ u : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : kˣ) := by
    refine (isOpen_lt (((Units.continuous_val.comp hμ).sub continuous_const).norm) continuous_const).mem_nhds ?_
    simp
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  have h1 : (fun b : k => 1 + b) ⁻¹' T ∩ cball 1 ∈ 𝓝 (0 : k) :=
    inter_mem ((continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hT))
      (cball_mem_nhds 1)
  obtain ⟨s, hs⟩ := exists_cball_subset h1
  refine isOpen_ker_of_cball μ s fun x hx => Units.ext (eq_one_of_pow_near fun n => ?_)
  have hx1 : valuation k (x : k) ≤ 1 := by
    have := add_mem_cball (hs hx).2 (show (1 : k) ∈ cball 1 by simp [cball])
    simpa [cball] using this
  have hn : (x : k) ^ n - 1 ∈ cball s := by
    induction n with
    | zero => simp [cball]
    | succ n ih =>
      have e : (x : k) ^ (n + 1) - 1 = x * (x ^ n - 1) + (x - 1) := by ring
      rw [e]
      refine add_mem_cball ?_ hx
      show valuation k _ ≤ valuation k (s : k)
      rw [map_mul]
      exact (mul_le_of_le_one_left' hx1).trans ih
  have := hTV (a := x ^ n) (by simpa using (hs hn).1)
  simpa using this

variable {m : Type} [Fintype m]

def ballLat (m : Type) (s : kˣ) : Submodule 𝒪[k] (m → k) where
  carrier := {x | ∀ i, x i ∈ cball s}
  add_mem' hx hy i := add_mem_cball (hx i) (hy i)
  zero_mem' i := by simp [cball]
  smul_mem' a x hx i := by
    show valuation k ((a : k) * x i) ≤ valuation k (s : k)
    rw [map_mul]
    exact (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).mp a.2)).trans (hx i)

theorem ballLat_isLattice (s : kˣ) : (ballLat m s).IsLattice k := by
  classical
  have hs : ∀ i : m, (Pi.single i (s : k) : m → k) ∈ ballLat m s := fun i j => by
    rw [Pi.single_apply]; split_ifs <;> simp [cball]
  constructor
  · refine ⟨Finset.univ.image fun i : m => (Pi.single i (s : k) : m → k), le_antisymm ?_ fun x hx => ?_⟩
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hs i
    · rw [← Finset.univ_sum_single x]
      refine sum_mem fun i _ => ?_
      have h1 : x i * (s : k)⁻¹ ∈ 𝒪[k] := by
        rw [Valuation.mem_integer_iff, map_mul, map_inv₀, mul_inv_le_iff₀ (by simp [zero_lt_iff]), one_mul]
        exact hx i
      have e : (Pi.single i (x i) : m → k) = (⟨_, h1⟩ : 𝒪[k]) • (Pi.single i (s : k) : m → k) := by
        funext j
        show _ = x i * (s : k)⁻¹ * (Pi.single i (s : k) : m → k) j
        simp only [Pi.single_apply]; split_ifs <;> simp
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rw [eq_top_iff]
    intro x _
    rw [← Finset.univ_sum_single x]
    refine sum_mem fun i _ => ?_
    have e : (Pi.single i (x i) : m → k) = (x i * (s : k)⁻¹) • (Pi.single i (s : k) : m → k) := by
      funext j
      simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hs i))

theorem exists_ballLat_subset {V : Set (m → k)} (hV : V ∈ 𝓝 (0 : m → k)) :
    ∃ s : kˣ, (ballLat m s : Set (m → k)) ⊆ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, h⟩ := hV
  obtain ⟨s, hs⟩ := exists_cball_subset (U := ⋂ i, t i) (iInter_mem.2 ht)
  exact ⟨s, fun x hx => h fun i _ => Set.mem_iInter.1 (hs (hx i)) i⟩

theorem exists_subset_ballLat {K : Set (m → k)} (hK : IsCompact K) :
    ∃ s : kˣ, K ⊆ (ballLat m s : Set (m → k)) := by
  have hK' : IsCompact (⋃ i, (fun x : m → k => x i) '' K) :=
    isCompact_iUnion fun i => hK.image (continuous_apply i)
  obtain ⟨s, hs⟩ := hK'.elim_directed_cover (fun s : kˣ => cball s) isOpen_cball (fun x _ => by
    by_cases h : x = 0
    · exact Set.mem_iUnion.2 ⟨1, by simp [cball, h]⟩
    · exact Set.mem_iUnion.2 ⟨Units.mk0 x h, by simp [cball]⟩) fun a b => by
    rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
    · exact ⟨b, fun x (hx : x ∈ cball a) => le_trans (a := valuation k x) (c := valuation k (b : k)) hx h, subset_rfl⟩
    · exact ⟨a, subset_rfl, fun x (hx : x ∈ cball b) => le_trans (a := valuation k x) (c := valuation k (a : k)) hx h⟩
  exact ⟨s, fun x hx i => hs (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩)⟩

theorem isCompact_lattice (L : Submodule 𝒪[k] (m → k)) (hL : L.IsLattice k) : IsCompact (L : Set (m → k)) := by
  obtain ⟨S, hS⟩ := hL.fg
  obtain ⟨s, hs⟩ := exists_subset_ballLat (K := (S : Set (m → k))) S.finite_toSet.isCompact
  have h1 : L ≤ ballLat m s := hS ▸ Submodule.span_le.2 hs
  have h2 : IsCompact (ballLat m s : Set (m → k)) := by
    have := isCompact_univ_pi fun _ : m => isCompact_cball s
    convert this using 1
    ext x; exact ⟨fun h i _ => h i, fun h i => h i trivial⟩
  exact h2.of_isClosed_subset (LatPair.isClopen_lattice L).1 h1

variable {ψ : AddChar k Circle}

theorem perp_mem_nhds (hψ : Continuous ψ) (L : Submodule 𝒪[k] (m → k)) (hL : L.IsLattice k) :
    (perp ψ L : Set (m → k)) ∈ 𝓝 (0 : m → k) := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  refine IsCompact.eventually_forall_of_forall_eventually (isCompact_lattice L hL)
    (P := fun β u => ψ (u ⬝ᵥ β) = 1) fun u _ => ?_
  have hc : Continuous fun q : (m → k) × (m → k) => q.2 ⬝ᵥ q.1 := by fun_prop
  filter_upwards [((isOpen_cball s).preimage hc).mem_nhds (x := (0, u)) (by simp [cball])] with q hq
  exact hs _ hq

theorem isCompact_perp (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) [DecidableEq m] (L : Submodule 𝒪[k] (m → k))
    (hL : L.IsLattice k) : IsCompact (perp ψ L : Set (m → k)) := by
  have h := ExchangeSupport.mem_SB_of hψ1 ((perp ψ L : Set (m → k)).indicator fun _ => (1 : ℂ)) ?_ ?_
  · have h2 : IsCompact (closure _) := h.2
    rwa [Set.support_indicator, Function.support_const one_ne_zero, Set.inter_univ,
      (AddSubgroup.isClosed_of_isOpen _
        (AddSubgroup.isOpen_of_mem_nhds _ (perp_mem_nhds hψ L hL))).closure_eq] at h2
  · filter_upwards [perp_mem_nhds hψ L hL] with w hw u
    by_cases hu : u ∈ perp ψ L
    · rw [Set.indicator_of_mem (add_mem hu hw), Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem (fun h => hu (by simpa using sub_mem h hw)), Set.indicator_of_notMem hu]
  · filter_upwards [(LatPair.isClopen_lattice L).2.mem_nhds L.zero_mem] with β hβ u
    by_cases hu : u ∈ perp ψ L
    · rw [dotProduct_comm, hu β hβ]; simp
    · rw [Set.indicator_of_notMem hu, mul_zero]

end Lattices

section Reps
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem exists_isReps (D B : AddSubgroup V) (hD : IsCompact (D : Set V)) (hB : IsOpen (B : Set V)) :
    ∃ T, IsReps D B T := by
  classical
  haveI : DiscreteTopology (V ⧸ B) := QuotientAddGroup.discreteTopology hB
  have hfin : ((QuotientAddGroup.mk : V → V ⧸ B) '' D).Finite :=
    (hD.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have hs : ∀ q : V ⧸ B, ∃ v : V, q ∈ (QuotientAddGroup.mk : V → V ⧸ B) '' D →
      v ∈ D ∧ (QuotientAddGroup.mk v : V ⧸ B) = q := fun q => by
    by_cases h : q ∈ (QuotientAddGroup.mk : V → V ⧸ B) '' D
    · obtain ⟨v, hv, e⟩ := h
      exact ⟨v, fun _ => ⟨hv, e⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose s hs using hs
  refine ⟨hfin.toFinset.image s, fun t ht => ?_, fun β hβ => ⟨s β, ⟨?_, ?_⟩, ?_⟩⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
    exact (hs q (by simpa using hq)).1
  · exact Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ⟨β, hβ, rfl⟩)
  · exact QuotientAddGroup.eq_iff_sub_mem.1 (hs β ⟨β, hβ, rfl⟩).2.symm
  · rintro t ⟨ht, h⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
    rw [QuotientAddGroup.eq_iff_sub_mem.2 h, (hs q (hfin.mem_toFinset.1 hq)).2]

theorem integral_eq_sum_reps [MeasurableSpace V] [BorelSpace V] (m : Measure V) [m.IsAddHaarMeasure]
    {D B : AddSubgroup V} (hBD : B ≤ D) (hB : IsOpen (B : Set V)) (hBc : IsCompact (B : Set V))
    {T : Finset V} (hT : IsReps D B T) (f : V → ℂ) (h0 : ∀ β, β ∉ D → f β = 0)
    (h1 : ∀ β, ∀ b ∈ B, f (β + b) = f β) :
    ∫ β, f β ∂m = ((m.real (B : Set V) : ℝ) : ℂ) * ∑ t ∈ T, f t := by
  have hm : ∀ t : V, MeasurableSet ((fun β => -t + β) ⁻¹' (B : Set V)) := fun t =>
    (hB.preimage (by fun_prop)).measurableSet
  have e : ∀ β, f β = ∑ t ∈ T, ((fun β => -t + β) ⁻¹' (B : Set V)).indicator (fun _ => f t) β := by
    intro β
    by_cases hβ : β ∈ D
    · obtain ⟨t, ⟨ht, hb⟩, hu⟩ := hT.2 β hβ
      rw [Finset.sum_eq_single_of_mem t ht, Set.indicator_of_mem (by simpa [neg_add_eq_sub] using hb),
        ← h1 t _ hb, add_sub_cancel]
      intro t' ht' hne
      exact Set.indicator_of_notMem (fun h => hne (hu t' ⟨ht', by simpa [neg_add_eq_sub] using h⟩)) _
    · rw [h0 β hβ]
      refine (Finset.sum_eq_zero fun t ht => Set.indicator_of_notMem (fun h => hβ ?_) _).symm
      simpa using add_mem (hT.1 t ht) (hBD h)
  rw [integral_congr_ae (Eventually.of_forall e), integral_finset_sum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [integral_indicator_const _ (hm t), Measure.real, measure_preimage_add, Complex.real_smul]
    rfl
  · intro t _
    refine (integrable_indicator_iff (hm t)).2 (integrableOn_const ?_)
    rw [measure_preimage_add]
    exact hBc.measure_lt_top.ne

end Reps

section Abstract
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
  {ψ : AddChar k Circle} {ν : Measure k} {V : Type} [AddCommGroup V] [Module ℂ V]
  {ω : Representation ℂ (GL (n ⊕ Fin c) k) V} {l : V →ₗ[ℂ] ℂ} {v : V}

end Abstract

section Target
open Unfolding
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ} {ψ : AddChar k Circle} {ν : Measure k} {μ : kˣ →* ℂˣ}
  {A P P' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
  {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} {π : Representation ℂ (GL n k) P}
  {π' : Representation ℂ (GL n' k) P'}

def omS {a : Type} (b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL a k) (SB (Matrix b a k)) := (omR μ).comp (MonoidHom.inl _ _)

def untw {m : Type} [Fintype m] [DecidableEq m] (η : kˣ →* ℂˣ) (σ : Representation ℂ (GL m k) A) :
    Representation ℂ (GL m k) A where
  toFun g := (((η (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) • σ g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, mul_inv, Units.val_mul, smul_mul_smul_comm]

end Target

end GlobalTheory.RootEx.UniformLattices
