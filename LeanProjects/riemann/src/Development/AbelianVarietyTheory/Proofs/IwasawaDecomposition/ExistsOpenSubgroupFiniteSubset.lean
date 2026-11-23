import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SmallSub

theorem eq_zero_of_pow_mul {K : Type} [NormedField K] {C : Set K} (hC : IsCompact C) {c x : K} (hc : ‖c‖ < 1)
    (h : ∀ n : ℕ, ∃ u ∈ C, x = c ^ n * u) : x = 0 := by
  obtain ⟨B, hB⟩ := hC.isBounded.exists_norm_le
  have ht : Filter.Tendsto (fun n : ℕ => ‖c‖ ^ n * B) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg c) hc).mul_const B
  refine norm_le_zero_iff.1 (ge_of_tendsto' ht fun n => ?_)
  obtain ⟨u, hu, rfl⟩ := h n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (hB u hu) (by positivity)

theorem finiteAdele_eq_zero (F : Type) [Field F] [NumberField F] {C : Set (Af F)} (hC : IsCompact C) {x : Af F}
    (h : ∀ M : ℕ, 0 < M → ∃ u ∈ C, x = M • u) : x = 0 := by
  refine Subtype.ext (funext fun v => ?_)
  change evalV F v x = 0
  have hv : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  have h1 := (NumberField.FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
  rw [map_natCast, map_natCast] at h1
  have h0 : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero fun e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  refine eq_zero_of_pow_mul (hC.image hv) h1 fun n => ?_
  obtain ⟨u, hu, rfl⟩ := h _ (pow_pos h0 n)
  exact ⟨_, ⟨u, hu, rfl⟩, by rw [map_nsmul, nsmul_eq_mul, Nat.cast_pow]⟩

theorem tensor_eq_zero (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {C : Set (Af F ⊗[F] E)} (hC : IsCompact C) {x : Af F ⊗[F] E}
    (h : ∀ M : ℕ, 0 < M → ∃ u ∈ C, x = M • u) : x = 0 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)
  refine b.ext_elem fun i => ?_
  have hc : Continuous (b.coord i) := IsModuleTopology.continuous_of_linearMap _
  rw [map_zero, Finsupp.zero_apply]
  change b.coord i x = 0
  refine finiteAdele_eq_zero F (hC.image hc) fun M hM => ?_
  obtain ⟨u, hu, rfl⟩ := h M hM
  exact ⟨_, ⟨u, hu, rfl⟩, map_nsmul _ _ _⟩

theorem mem_GinfC_of_cong {D : D7} (V : HSp D) (k : GA D V)
    (h : ∀ n : ℕ, GlobalTheory.Ker.CongK V (GlobalTheory.SW.stdL D.host.E V.rank) n.factorial k) : k ∈ GinfC V := by
  obtain ⟨C, hC, hLC⟩ := GlobalTheory.StabCompact.exists_compact_latHat D.host.F D.host.E (GlobalTheory.SW.stdL D.host.E V.rank)
    (Submodule.fg_span (Set.finite_range _))
  refine Units.ext ?_
  change GlobalTheory.Ker.fmt V k = 1
  ext i j
  have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := fun w => by rw [map_one]; exact one_mem _
  have hy : (Pi.single j 1 : Fin V.rank → GlobalTheory.Ker.AfE D) ∈ GlobalTheory.Ker.hatV (D := D) (GlobalTheory.SW.stdL D.host.E V.rank) := by
    refine AddSubgroup.subset_closure ⟨1, h1, Pi.single j 1, Submodule.subset_span ⟨j, rfl⟩, ?_⟩
    funext a
    by_cases e : a = j
    · subst e
      simp only [Pi.single_eq_same]
      rfl
    · simp [Pi.single_eq_of_ne e]
  have key : (GlobalTheory.Ker.fmt V k *ᵥ Pi.single j 1 - (Pi.single j 1 : Fin V.rank → GlobalTheory.Ker.AfE D)) i = 0 := by
    refine tensor_eq_zero D.host.F D.host.E (hC.image (continuous_apply i)) fun M hM => ?_
    obtain ⟨u, hu, e⟩ := (h M).2 _ hy
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hM le_rfl
    refine ⟨_, ⟨c • u, hLC _ (nsmul_mem hu c), rfl⟩, ?_⟩
    rw [e, hc, mul_smul]
    rfl
  rw [Pi.sub_apply, sub_eq_zero, Matrix.mulVec_single_one] at key
  rw [Matrix.one_apply, ← Pi.single_apply]
  exact key

theorem exists_open_subgroup_finite_subset : ∀ (D : D7) (V : HSp D), ∀ N ∈ 𝓝 (1 : GA D V), ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ N := by
  intro D V N hN
  obtain ⟨i0, -, -, i3, -, -, hK⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  have hL : (GlobalTheory.SW.stdL D.host.E V.rank).FG ∧ Submodule.span D.host.E
      (GlobalTheory.SW.stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    exact ⟨a, by simp⟩
  choose K hK1 hK2 hK3 _ using fun n : ℕ => hK _ n.factorial hL n.factorial_pos
  have hanti : Antitone fun n => (K n : Set (GA D V)) ∩ GfC V := by
    intro m n hmn k hk
    refine ⟨(hK1 m k).2 ⟨((hK1 n k).1 hk.1).1, fun u hu => ?_⟩, hk.2⟩
    obtain ⟨w, hw, e⟩ := ((hK1 n k).1 hk.1).2 u hu
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hmn
    exact ⟨c • w, nsmul_mem hw c, by rw [e, hc, mul_smul]⟩
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact' (U := N) hanti.directed_ge hK3 (fun n => (hK3 n).isClosed)
    (fun x hx => by
      rw [Set.mem_iInter] at hx
      rwa [GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V (hx 0).2 (mem_GinfC_of_cong V x fun n => (hK1 n x).1 (hx n).1)])
  exact ⟨K n, hK2 n, fun k hk hf => hn ⟨hk, hf⟩⟩

end GlobalTheory.Mem.SmallSub
