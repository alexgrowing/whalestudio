import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassSumIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFundamentalDomainEqSumDoubleCosetAvg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarOpenSubgroupVolumeInvEqRelIndex
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelA
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Formalism.L2.Theta Formalism.IndefR GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteClassAvg

theorem measurePreserving_mul_right_of_mem {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (J : Subgroup G) (hJ : IsOpen (J : Set G)) (h0 : μ J ≠ 0) (htop : μ J ≠ ⊤) {g : G}
    (hg : g ∈ J) : MeasurePreserving (· * g) μ μ := by
  refine ⟨measurable_mul_const g, ?_⟩
  set c := Measure.haarScalarFactor (Measure.map (· * g) μ) μ with hcdef
  have e : Measure.map (· * g) μ = c • μ := Measure.isMulLeftInvariant_eq_smul _ _
  have hpre : (· * g) ⁻¹' (J : Set G) = J := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact J.mul_mem_cancel_right hg
  have h1 : Measure.map (· * g) μ J = μ J := by
    rw [Measure.map_apply (measurable_mul_const g) hJ.measurableSet, hpre]
  rw [e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
  have hc : ((c : ENNReal)) = 1 := by
    have h2 : (c : ENNReal) * μ J / μ J = (c : ENNReal) := ENNReal.mul_div_cancel_right h0 htop
    rw [h1, ENNReal.div_self h0 htop] at h2
    exact h2.symm
  have hc' : c = 1 := by exact_mod_cast hc
  rw [e, hc', one_smul]

theorem setIntegral_comp_mul_right_of_mp {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant]
    (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (f : G → ℂ)
    (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) (hg : MeasurePreserving (· * g) μ μ) :
    ∫ x in 𝓕, f (x * g) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have hg' : MeasurePreserving (MeasurableEquiv.mulRight g) μ μ := hg
  have h2 : IsFundamentalDomain Γ ((fun x => x * g) '' 𝓕) μ :=
    h𝓕.image_of_equiv (MeasurableEquiv.mulRight g).toEquiv hg'.symm.quasiMeasurePreserving (Equiv.refl _)
      (fun γ x => by
        show (γ • x) * g = γ • (x * g)
        simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc])
  rw [← hg.setIntegral_image_emb (measurableEmbedding_mulRight g) f 𝓕]
  refine h2.setIntegral_eq h𝓕 ?_
  intro γ x
  rw [Subgroup.smul_def, smul_eq_mul]
  exact hf γ γ.2 x

end GlobalTheory.DefiniteClassAvg

namespace GlobalTheory.DefiniteClassAvg

theorem integral_eq_sum_avg (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ K Kf : Subgroup G) [Countable Γ]
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hK : IsOpen (K : Set G)) (hKfin : μ K ≠ ⊤)
    (U : Type) [Group U] [TopologicalSpace U] [IsTopologicalGroup U] [CompactSpace U] [MeasurableSpace U] [BorelSpace U]
    (ν : Measure U) [ν.IsMulLeftInvariant] [IsProbabilityMeasure ν] (j : U →* G) (hj : Continuous j)
    (hrt : ∀ w, MeasurePreserving (· * j w) μ μ)
    (hdec : ∀ k ∈ K, ∃ k' ∈ Kf, ∃ w, k = k' * j w) (hcomm : ∀ k ∈ Kf, ∀ w, k * j w = j w * k)
    (ι : Type) [Fintype ι] (h : ι → G) (huniq : ∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k)
    (hfin : ∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite) (f : G → ℂ) (hf : Continuous f)
    (hfl : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (hfr : ∀ k ∈ Kf, ∀ x, f (x * k) = f x) :
    IntegrableOn f 𝓕 μ ∧ ∫ x in 𝓕, f x ∂μ = ((μ K).toReal : ℂ) *
      ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ℕ) : ℂ)⁻¹ * ∫ v, f (h i * j v) ∂ν := by
  have key : ∀ x, ∀ k' ∈ Kf, ∀ w, f (x * (k' * j w)) = f (x * j w) := by
    intro x k' hk' w
    rw [hcomm k' hk' w, ← mul_assoc, hfr k' hk']
  have hbd : ∃ C, ∀ x, ‖f x‖ ≤ C := by
    have hi : ∀ i, ∃ C, ∀ v, ‖f (h i * j v)‖ ≤ C := fun i =>
      (isCompact_range ((hf.comp (continuous_const.mul hj)).norm)).bddAbove.imp
        fun C hC v => hC ⟨v, rfl⟩
    choose B hB using hi
    refine ⟨∑ i, |B i|, fun x => ?_⟩
    obtain ⟨i, ⟨γ, hγ, k, hk, rfl⟩, -⟩ := huniq x
    obtain ⟨k', hk', w, rfl⟩ := hdec k hk
    rw [mul_assoc, hfl γ hγ, key _ k' hk' w]
    exact (hB i w).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |B i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨C, hC⟩ := hbd
  have hFl : ∀ γ ∈ Γ, ∀ x, ∫ v, f (γ * x * j v) ∂ν = ∫ v, f (x * j v) ∂ν := by
    intro γ hγ x
    congr 1; funext v; rw [mul_assoc, hfl γ hγ]
  have hFr : ∀ k ∈ K, ∀ x, ∫ v, f (x * k * j v) ∂ν = ∫ v, f (x * j v) ∂ν := by
    intro k hk x
    obtain ⟨k', hk', w, rfl⟩ := hdec k hk
    have e : ∀ v, f (x * (k' * j w) * j v) = f (x * j (w * v)) := by
      intro v
      have : x * (k' * j w) * j v = x * j (w * v) * k' := by
        calc x * (k' * j w) * j v = x * j w * (k' * j v) := by
                rw [hcomm k' hk' w]; simp only [mul_assoc]
          _ = x * j w * (j v * k') := by rw [hcomm k' hk' v]
          _ = x * j (w * v) * k' := by rw [map_mul]; simp only [mul_assoc]
      rw [this, hfr k' hk']
    simp_rw [e]
    exact integral_mul_left_eq_self (fun v => f (x * j v)) w
  obtain ⟨hfin𝓕, -, hFeq⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G μ Γ K 𝓕 h𝓕 hK
    hKfin ι h huniq hfin (fun x => ∫ v, f (x * j v) ∂ν) hFl hFr
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin𝓕
  have hint : IntegrableOn f 𝓕 μ :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  refine ⟨hint, ?_⟩
  have hc : Continuous fun p : G × U => f (p.1 * j p.2) :=
    hf.comp (continuous_fst.mul (hj.comp continuous_snd))
  have hI : Integrable (Function.uncurry fun x v => f (x * j v)) ((μ.restrict 𝓕).prod ν) :=
    Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hC _)
  have hsh : ∀ v, ∫ x in 𝓕, f (x * j v) ∂μ = ∫ x in 𝓕, f x ∂μ := fun v =>
    setIntegral_comp_mul_right_of_mp μ Γ 𝓕 h𝓕 f hfl (j v) (hrt v)
  calc ∫ x in 𝓕, f x ∂μ = ∫ x in 𝓕, ∫ v, f (x * j v) ∂ν ∂μ := by
        rw [integral_integral_swap hI]
        simp only [hsh]
        simp
    _ = _ := hFeq

end GlobalTheory.DefiniteClassAvg

namespace GlobalTheory.DefiniteClassAvg

variable {D : D7}

noncomputable def realPart (V : HSp D) (y : GA D V) : GA D V :=
  Eqv.UI.brg (Eqv.UI.framesV D V) (((Eqv.UI.brg (Eqv.UI.framesV D V)).symm y).1, 1)

noncomputable def finPart (V : HSp D) (y : GA D V) : GA D V :=
  Eqv.UI.brg (Eqv.UI.framesV D V) (1, ((Eqv.UI.brg (Eqv.UI.framesV D V)).symm y).2)

theorem realPart_mem (V : HSp D) (y : GA D V) : realPart V y ∈ GinfC V := (Eqv.brg_mem_GinfC _ _).2 rfl

theorem finPart_mem (V : HSp D) (y : GA D V) : finPart V y ∈ GfC V := (Eqv.brg_mem_GfC _ _).2 rfl

theorem realPart_mul_finPart (V : HSp D) (y : GA D V) : realPart V y * finPart V y = y := by
  unfold realPart finPart
  rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  exact (Eqv.UI.brg (Eqv.UI.framesV D V)).apply_symm_apply y

theorem finPart_mul_realPart (V : HSp D) (y : GA D V) : finPart V y * realPart V y = y := by
  rw [← Eqv.Act.comm_inf_fin (realPart_mem V y) (finPart_mem V y)]
  exact realPart_mul_finPart V y

theorem continuous_realPart (V : HSp D) : Continuous (realPart V) :=
  (Eqv.UI.brg (Eqv.UI.framesV D V)).continuous.comp
    ((continuous_fst.comp (Eqv.UI.brg (Eqv.UI.framesV D V)).symm.continuous).prodMk continuous_const)

theorem finE_eq_one_of_mem {V : HSp D} {a : GA D V} (ha : a ∈ GinfC V) : Lev.finE V a = 1 := by
  have h : finHom V a = 1 := ha
  show Formalism.UG.bc (Lev.swapAE D) (finHom V a) = 1
  rw [h, map_one]

theorem finE_finPart (V : HSp D) (y : GA D V) : Lev.finE V (finPart V y) = Lev.finE V y := by
  conv_rhs => rw [← realPart_mul_finPart V y]
  rw [map_mul, finE_eq_one_of_mem (realPart_mem V y), one_mul]

theorem finPart_mem_levA (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} {y : GA D V}
    (h : Lev.finE V y ∈ K) : finPart V y ∈ Lev.levA V K :=
  Subgroup.mem_inf.2 ⟨finPart_mem V y, by show Lev.finE V (finPart V y) ∈ K; rw [finE_finPart]; exact h⟩

theorem continuous_of_level (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (ho : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) (Φ : GA D V → ℂ)
    (hr : ∀ k ∈ Lev.levA V K, ∀ h, Φ (h * k) = Φ h) (hc : ∀ x, Continuous fun k : GinfC V => Φ (x * k)) :
    Continuous Φ := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hG := hT.2.2.2.2.1
  rw [continuous_iff_continuousAt]
  intro x0
  let p : GA D V → GinfC V := fun x => ⟨realPart V (x0⁻¹ * x), realPart_mem V _⟩
  have hp : Continuous p :=
    ((continuous_realPart V).comp (continuous_mul_left x0⁻¹)).subtype_mk _
  have hev : (fun x => Φ (x0 * (p x : GA D V))) =ᶠ[𝓝 x0] Φ := by
    have hn : (fun x => x0⁻¹ * x) ⁻¹' ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) ∈ 𝓝 x0 :=
      (ho.preimage (continuous_mul_left x0⁻¹)).mem_nhds (by
        simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
        exact (K.comap (Lev.finE V)).one_mem)
    filter_upwards [hn] with x hx
    have hx' : Lev.finE V (x0⁻¹ * x) ∈ K := hx
    have hq := finPart_mem_levA V hx'
    show Φ (x0 * realPart V (x0⁻¹ * x)) = Φ x
    calc Φ (x0 * realPart V (x0⁻¹ * x)) = Φ (x0 * realPart V (x0⁻¹ * x) * finPart V (x0⁻¹ * x)) := (hr _ hq _).symm
      _ = Φ x := by rw [mul_assoc, realPart_mul_finPart, mul_inv_cancel_left]
  exact ((hc x0).comp hp).continuousAt.congr hev

end GlobalTheory.DefiniteClassAvg

namespace GlobalTheory.DefiniteClassAvg

theorem existsUnique_doubleCoset {G H : Type} [Group G] [Group H] (π : G →* H) (Γ : Subgroup G) (J : Subgroup H) {I : Type}
    (y : I → H) (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (a : I → G) (ha : ∀ i, π (a i) = y i) :
    ∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ J.comap π, x = γ * a i * k := by
  intro x
  refine (existsUnique_congr fun i => ?_).1 (hy (π x))
  constructor
  · rintro ⟨γ, k, e⟩
    refine ⟨γ, γ.2, ((γ : G) * a i)⁻¹ * x, ?_, by group⟩
    rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, ha, e]
    change (π γ * y i)⁻¹ * (π γ * y i * k) ∈ J
    rw [inv_mul_cancel_left]
    exact k.2
  · rintro ⟨γ, hγ, k, hk, rfl⟩
    exact ⟨⟨γ, hγ⟩, ⟨π k, hk⟩, by rw [map_mul, map_mul, ha]; rfl⟩

end GlobalTheory.DefiniteClassAvg

namespace GlobalTheory.DefiniteClassAvg

end GlobalTheory.DefiniteClassAvg
