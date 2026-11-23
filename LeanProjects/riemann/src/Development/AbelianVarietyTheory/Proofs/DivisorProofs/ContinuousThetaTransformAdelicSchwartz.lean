import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableOfRapidDecay

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaTrCont

open GlobalTheory.WeilM

section Gen

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def archV (x : κ → AdeleRing (𝓞 F) F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1

def finV (x : κ → AdeleRing (𝓞 F) F) : κ → FiniteAdeleRing (𝓞 F) F := fun i => (x i).2

theorem continuous_archV : Continuous (archV F (κ := κ)) :=
  continuous_pi fun i => (GlobalTheory.Core.Rk.RapidInt.continuous_toMixed F).comp (continuous_fst.comp (continuous_apply i))

theorem continuous_finV : Continuous (finV F (κ := κ)) :=
  continuous_pi fun i => continuous_snd.comp (continuous_apply i)

theorem archV_add (x y : κ → AdeleRing (𝓞 F) F) : archV F (x + y) = archV F x + archV F y := by
  funext i
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1 (y i).1

theorem finV_add (x y : κ → AdeleRing (𝓞 F) F) : finV F (x + y) = finV F x + finV F y := by
  funext i
  rfl

theorem archV_alg (ξ : κ → F) :
    archV F (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = fun i => mixedEmbedding F (ξ i) := by
  funext i
  simp only [archV]
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem finV_alg (ξ : κ → F) :
    finV F (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) :=
  rfl

theorem pureA_eq (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → AdeleRing (𝓞 F) F) : pureA F f g x = f (archV F x) * g (finV F x) := rfl

theorem one_add_norm_le {V : Type} [NormedAddCommGroup V] (z a : V) :
    1 + ‖z‖ ≤ (1 + ‖z + a‖) * (1 + ‖a‖) := by
  have h1 : ‖z‖ ≤ ‖z + a‖ + ‖a‖ := by
    simpa using norm_sub_le (z + a) a
  nlinarith [norm_nonneg (z + a), norm_nonneg a]

theorem schwartz_shift_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (k : ℕ)
    {R : ℝ} (z a : V) (ha : ‖a‖ ≤ R) :
    ‖f (z + a)‖ ≤ (1 + R) ^ k * (2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f) *
      ((1 + ‖z‖) ^ k)⁻¹ := by
  set C := 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  have hf : (1 + ‖z + a‖) ^ k * ‖f (z + a)‖ ≤ C := by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f (z + a)
    rwa [norm_iteratedFDeriv_zero] at this
  have hpos : 0 < (1 + ‖z‖) ^ k := pow_pos (by positivity) k
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have h1 : (1 + ‖z‖) ^ k ≤ (1 + ‖z + a‖) ^ k * (1 + R) ^ k := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ((one_add_norm_le z a).trans ?_) k
    gcongr
  calc ‖f (z + a)‖ * (1 + ‖z‖) ^ k ≤ ‖f (z + a)‖ * ((1 + ‖z + a‖) ^ k * (1 + R) ^ k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (1 + ‖z + a‖) ^ k * ‖f (z + a)‖ * (1 + R) ^ k := by ring
    _ ≤ C * (1 + R) ^ k := mul_le_mul_of_nonneg_right hf (pow_nonneg (by linarith [norm_nonneg a]) k)
    _ = (1 + R) ^ k * C := by ring

theorem summable_one_add_norm_inv {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] {k : ℕ} (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖) ^ k)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L k hk) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖z‖) ^ k)⁻¹‖ ≤ ‖z‖⁻¹ ^ k
  rw [Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg (by positivity) k)), ← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.2 (by positivity)) (inv_anti₀ hz0 (by linarith)) k

end Gen

end GlobalTheory.ThetaTrCont

namespace GlobalTheory.ThetaTrCont

open GlobalTheory.WeilM
open scoped Classical Topology

section Theta

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

theorem local_bound (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) (p₀ : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    ∃ s ∈ 𝓝 p₀, ∃ u : (κ → F) → ℝ, Summable u ∧ ∀ ξ : κ → F, ∀ p ∈ s,
      ‖schr ψ p (pureA F f g) (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ ≤ u ξ := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  set x₀ := finV F p₀.1
  have hK : IsCompact ((fun z => z - x₀) '' tsupport g) :=
    hg.2.isCompact.image (continuous_id.sub continuous_const)
  obtain ⟨N, hN, hKN⟩ := exists_nat_mul_integral_of_isCompact F hK
  haveI := discreteTopology_denomLattice F κ hN
  set k := Module.finrank ℤ (denomLattice F κ N) + 1
  set C := 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  set R := ‖archV F p₀.1‖ + 1
  set S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  set s : Set ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :=
    {p | ‖archV F p.1 - archV F p₀.1‖ < 1} ∩
      ⋂ i, (fun p : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) =>
        (N : FiniteAdeleRing (𝓞 F) F) * (finV F p.1 i - x₀ i)) ⁻¹'
        {a | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  have hs : s ∈ 𝓝 p₀ := by
    refine IsOpen.mem_nhds (IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => (isOpen_integral F).preimage ?_)) ?_
    · exact isOpen_lt (((continuous_archV F).comp continuous_fst).sub continuous_const).norm continuous_const
    · exact continuous_const.mul
        (((continuous_apply i).comp ((continuous_finV F).comp continuous_fst)).sub continuous_const)
    · refine ⟨by simp, Set.mem_iInter.2 fun i => ?_⟩
      intro v
      simp [x₀]
  refine ⟨s, hs, S.indicator fun ξ => B * ((1 + R) ^ k * C * ((1 + ‖(fun i => mixedEmbedding F (ξ i))‖) ^ k)⁻¹),
    ?_, ?_⟩
  · rw [← summable_subtype_iff_indicator]
    let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    exact (((summable_one_add_norm_inv (denomLattice F κ N) (Nat.lt_succ_self _)).comp_injective hj).mul_left
      ((1 + R) ^ k * C)).mul_left B
  · intro ξ p hp
    have hp1 : ‖archV F p.1‖ ≤ R := by
      have h := hp.1
      calc ‖archV F p.1‖ = ‖(archV F p.1 - archV F p₀.1) + archV F p₀.1‖ := by rw [sub_add_cancel]
        _ ≤ ‖archV F p.1 - archV F p₀.1‖ + ‖archV F p₀.1‖ := norm_add_le _ _
        _ ≤ R := by simp only [Set.mem_setOf_eq] at h; linarith
    have hn : ‖schr ψ p (pureA F f g) (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ =
        ‖f ((fun i => mixedEmbedding F (ξ i)) + archV F p.1)‖ *
          ‖g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + finV F p.1)‖ := by
      simp only [schr]
      rw [norm_mul, hψ, one_mul, pureA_eq, archV_add, finV_add, archV_alg, finV_alg, norm_mul]
    rw [hn]
    by_cases hξ : ξ ∈ S
    · rw [Set.indicator_of_mem hξ]
      have h1 := schwartz_shift_le f k (fun i => mixedEmbedding F (ξ i)) (archV F p.1) hp1
      calc _ ≤ ((1 + R) ^ k * C * ((1 + ‖(fun i => mixedEmbedding F (ξ i))‖) ^ k)⁻¹) * B :=
            mul_le_mul h1 (hB _) (norm_nonneg _) ((norm_nonneg _).trans h1)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hξ]
      have hg0 : g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + finV F p.1) = 0 := by
        by_contra h0
        apply hξ
        have hy : ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + finV F p.1) - x₀ ∈
            (fun z => z - x₀) '' tsupport g := ⟨_, subset_tsupport _ h0, rfl⟩
        refine fun i => ?_
        have H : ∀ v, ((N : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) v ∈
            HeightOneSpectrum.adicCompletionIntegers F v := by
          intro v
          have h1 := hKN _ hy i v
          have h2 := (Set.mem_iInter.1 hp.2 i) v
          have e : (N : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) =
              (N : FiniteAdeleRing (𝓞 F) F) *
                  (((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + finV F p.1) - x₀) i -
                (N : FiniteAdeleRing (𝓞 F) F) * (finV F p.1 i - x₀ i) := by
            simp only [Pi.sub_apply, Pi.add_apply]
            ring
          rw [e]
          exact sub_mem h1 h2
        obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
          rw [map_mul, map_natCast]
          exact H v
        refine ⟨y, ?_⟩
        have h2 := congrArg (mixedEmbedding F) hy
        rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
        exact h2.symm
      rw [hg0, norm_zero, mul_zero]

end Theta

end GlobalTheory.ThetaTrCont

namespace GlobalTheory.ThetaTrCont

open GlobalTheory.WeilM
open scoped Classical Topology

section Theta2

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem pure_cont (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (∀ p, Summable fun ξ : κ → F => schr ψ p (pureA F f g) (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
      Continuous fun p => thetaSum F (schr ψ p (pureA F f g)) := by
  have hterm : ∀ ξ : κ → F, Continuous fun p : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) =>
      schr ψ p (pureA F f g) (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := fun ξ => by
    simp only [schr, pureA_eq]
    refine (hψc.comp ?_).mul ((f.continuous.comp ?_).mul (hg.1.continuous.comp ?_))
    · exact (continuous_const.dotProduct continuous_snd).add
        (continuous_const.mul (continuous_fst.dotProduct continuous_snd))
    · exact (continuous_archV F).comp (continuous_const.add continuous_fst)
    · exact (continuous_finV F).comp (continuous_const.add continuous_fst)
  refine ⟨fun p => ?_, continuous_iff_continuousAt.2 fun p₀ => ?_⟩
  · obtain ⟨s, hs, u, hu, hb⟩ := local_bound F ψ hψ f hg p
    exact hu.of_norm_bounded fun ξ => hb ξ p (mem_of_mem_nhds hs)
  · obtain ⟨s, hs, u, hu, hb⟩ := local_bound F ψ hψ f hg p₀
    exact (continuousOn_tsum (fun ξ => (hterm ξ).continuousOn) hu fun ξ p hp => hb ξ p hp).continuousAt hs

theorem schA_cont (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (∀ p, Summable fun ξ : κ → F => schr ψ p Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
      Continuous fun p => thetaSum F (schr ψ p Φ) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact pure_cont F ψ hψc hψ f hg
  | zero =>
    have e : ∀ p, schr ψ p (0 : (κ → AdeleRing (𝓞 F) F) → ℂ) = 0 := fun p => funext fun x => by simp [schr]
    refine ⟨fun p => by simpa [e] using (summable_zero : Summable fun _ : κ → F => (0 : ℂ)), ?_⟩
    simp only [e, thetaSum, Pi.zero_apply, tsum_zero]
    exact continuous_const
  | add Φ Ψ _ _ h1 h2 =>
    have e : ∀ p, schr ψ p (Φ + Ψ) = schr ψ p Φ + schr ψ p Ψ := fun p => funext fun x => by
      simp [schr, mul_add]
    refine ⟨fun p => by simpa [e] using (h1.1 p).add (h2.1 p), ?_⟩
    have e2 : (fun p => thetaSum F (schr ψ p (Φ + Ψ))) =
        fun p => thetaSum F (schr ψ p Φ) + thetaSum F (schr ψ p Ψ) := funext fun p => by
      rw [e]
      exact (h1.1 p).tsum_add (h2.1 p)
    rw [e2]
    exact h1.2.add h2.2
  | smul c Φ _ h =>
    have e : ∀ p, schr ψ p (c • Φ) = c • schr ψ p Φ := fun p => funext fun x => by
      simp only [schr, Pi.smul_apply, smul_eq_mul]
      ring
    refine ⟨fun p => by simpa [e] using (h.1 p).mul_left c, ?_⟩
    simp only [e, thetaSum_smul]
    exact continuous_const.mul h.2

end Theta2

theorem continuous_thetaTr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) := by
  intro D ψ hψ S T JA JB ξ _ _ κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF D.host.F) (Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)) :=
    inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin T.rank → Fin S.rank → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E))
  have hc : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  exact (schA_cont D.host.F ψ hψ.1.1 hψ.1.2.1 hΦ).2.comp hc

end GlobalTheory.ThetaTrCont
