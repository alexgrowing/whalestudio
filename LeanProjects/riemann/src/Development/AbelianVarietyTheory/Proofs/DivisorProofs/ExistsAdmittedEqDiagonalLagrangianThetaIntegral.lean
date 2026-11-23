import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.LagrThetaAdm

open GlobalTheory.ThetaTrCont
open scoped Classical

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem uniform_majorant {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (k : ℕ) (c : ℝ), 0 ≤ c ∧ ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (a : κ → AdeleRing (𝓞 F) F),
      ∃ u : (κ → F) → ℝ, Summable u ∧
        ∑' ξ, u ξ ≤ c * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f ∧
        ∀ ξ : κ → F, ‖pureA F f g ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + a)‖ ≤ u ξ := by
  obtain ⟨KA, hKA, hcov⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  set Kκ : Set (κ → AdeleRing (𝓞 F) F) := Set.univ.pi fun _ => KA
  have hKκ : IsCompact Kκ := isCompact_univ_pi fun _ => hKA
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨R, hR⟩ := hKκ.exists_bound_of_continuousOn (continuous_archV F (κ := κ)).continuousOn
  have hR0 : ∀ b ∈ Kκ, ‖archV F b‖ ≤ max R 0 := fun b hb => (hR b hb).trans (le_max_left _ _)
  set R' := max R 0
  set Kf : Set (κ → FiniteAdeleRing (𝓞 F) F) := (fun p => p.1 - finV F p.2) '' (tsupport g ×ˢ Kκ)
  have hKf : IsCompact Kf := (hg.2.isCompact.prod hKκ).image (continuous_fst.sub ((continuous_finV F).comp continuous_snd))
  obtain ⟨N, hN, hKN⟩ := exists_nat_mul_integral_of_isCompact F hKf
  haveI := discreteTopology_denomLattice F κ hN
  set k := Module.finrank ℤ (denomLattice F κ N) + 1
  set S : Set (κ → F) := {η | (fun i => mixedEmbedding F (η i)) ∈ denomLattice F κ N}
  have hw : Summable (S.indicator fun η => ((1 + ‖(fun i => mixedEmbedding F (η i))‖) ^ k)⁻¹) := by
    rw [← summable_subtype_iff_indicator]
    let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    have hs := (summable_one_add_norm_inv (denomLattice F κ N) (k := k) (Nat.lt_succ_self _)).comp_injective hj
    refine hs.congr fun η => ?_
    simp only [Function.comp_apply, j, Submodule.coe_norm]
  set w : (κ → F) → ℝ := S.indicator fun η => ((1 + ‖(fun i => mixedEmbedding F (η i))‖) ^ k)⁻¹ with hwdef
  have hw0 : ∀ η, 0 ≤ w η := fun η => Set.indicator_nonneg (fun _ _ => inv_nonneg.2 (by positivity)) η
  refine ⟨k, B * (1 + R') ^ k * 2 ^ k * ∑' η, w η, by
    have h1 : 0 ≤ ∑' η, w η := tsum_nonneg hw0
    have h2 : 0 ≤ R' := le_max_right _ _
    positivity, fun f a => ?_⟩
  set C := (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  choose y hy using fun i => hcov (a i)
  set b : κ → AdeleRing (𝓞 F) F := fun i => a i - algebraMap F (AdeleRing (𝓞 F) F) (y i)
  have hb : b ∈ Kκ := fun i _ => hy i
  have hab : ∀ ξ : κ → F, (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + a =
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((ξ + y) i)) + b := by
    intro ξ; funext i; simp [b, map_add]
  refine ⟨fun ξ => B * ((1 + R') ^ k * (2 ^ k * C)) * w (ξ + y), ?_, ?_, fun ξ => ?_⟩
  · exact ((Equiv.addRight y).summable_iff.2 hw).mul_left _
  · have e : ∑' x, w (x + y) = ∑' η, w η := (Equiv.addRight y).tsum_eq w
    rw [tsum_mul_left, e]
    apply le_of_eq; ring
  · beta_reduce
    rw [hab, pureA_eq, archV_add, finV_add, archV_alg, finV_alg, norm_mul]
    by_cases hξ : ξ + y ∈ S
    · have h1 := schwartz_shift_le f k (fun i => mixedEmbedding F ((ξ + y) i)) (archV F b) (hR0 b hb)
      have e : w (ξ + y) = ((1 + ‖(fun i => mixedEmbedding F ((ξ + y) i))‖) ^ k)⁻¹ := by rw [hwdef, Set.indicator_of_mem hξ]
      rw [e]
      calc _ ≤ ((1 + R') ^ k * (2 ^ k * C) * ((1 + ‖(fun i => mixedEmbedding F ((ξ + y) i))‖) ^ k)⁻¹) * B :=
            mul_le_mul h1 (hB _) (norm_nonneg _) ((norm_nonneg _).trans h1)
        _ = _ := by ring
    · have hg0 : g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ξ + y) i)) + finV F b) = 0 := by
        by_contra h0
        apply hξ
        have hmem : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ξ + y) i)) ∈ Kf :=
          ⟨(_, b), ⟨subset_tsupport _ h0, hb⟩, by simp⟩
        refine fun i => ?_
        obtain ⟨z, hz⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * (ξ + y) i)
          fun v => by
            rw [map_mul, map_natCast]
            exact hKN _ hmem i v
        refine ⟨z, ?_⟩
        have h2 := congrArg (mixedEmbedding F) hz
        rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
        exact h2.symm
      rw [hg0, norm_zero, mul_zero]
      exact mul_nonneg (mul_nonneg hB0 (by have : 0 ≤ R' := le_max_right _ _; positivity)) (hw0 _)

end GlobalTheory.LagrThetaAdm

namespace GlobalTheory.LagrThetaAdm

open GlobalTheory.ThetaTrCont
open scoped Classical

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem thetaSum_pure_le (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (k : ℕ) (c : ℝ), 0 ≤ c ∧ ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
      (p : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)),
      ‖thetaSum F (schr ψ p (pureA F f g))‖ ≤ c * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
  obtain ⟨k, c, hc, h⟩ := uniform_majorant F hg
  refine ⟨k, c, hc, fun f p => ?_⟩
  obtain ⟨u, hu, hsum, hb⟩ := h f p.1
  refine (tsum_of_norm_bounded hu.hasSum fun ξ => ?_).trans hsum
  simp only [schr]
  rw [norm_mul, hψ, one_mul]
  exact hb ξ

theorem thetaSum_schA_bdd (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ C : ℝ, ∀ p, ‖thetaSum F (schr ψ p Φ)‖ ≤ C := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨k, c, -, hb⟩ := thetaSum_pure_le F ψ hψ hg
    exact ⟨_, fun p => hb f p⟩
  | zero =>
    refine ⟨0, fun p => ?_⟩
    have e : schr ψ p (0 : (κ → AdeleRing (𝓞 F) F) → ℂ) = 0 := funext fun x => by simp [schr]
    simp [e, thetaSum]
  | add Φ Ψ hΦ hΨ h1 h2 =>
    obtain ⟨C1, hC1⟩ := h1
    obtain ⟨C2, hC2⟩ := h2
    refine ⟨C1 + C2, fun p => ?_⟩
    have e : schr ψ p (Φ + Ψ) = schr ψ p Φ + schr ψ p Ψ := funext fun x => by simp [schr, mul_add]
    have e2 : thetaSum F (schr ψ p (Φ + Ψ)) = thetaSum F (schr ψ p Φ) + thetaSum F (schr ψ p Ψ) := by
      rw [e]
      exact ((schA_cont F ψ hψc hψ hΦ).1 p).tsum_add ((schA_cont F ψ hψc hψ hΨ).1 p)
    rw [e2]
    exact (norm_add_le _ _).trans (add_le_add (hC1 p) (hC2 p))
  | smul a Φ _ h =>
    obtain ⟨C, hC⟩ := h
    refine ⟨‖a‖ * C, fun p => ?_⟩
    have e : schr ψ p (a • Φ) = a • schr ψ p Φ := funext fun x => by
      simp only [schr, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, thetaSum_smul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC p) (norm_nonneg _)

end GlobalTheory.LagrThetaAdm

namespace GlobalTheory.LagrThetaAdm

open GlobalTheory.ThetaTrCont GlobalTheory.WeilSchrodinger
open scoped Classical

theorem exists_admitted_eq_diagonalLagrangian_thetaIntegral_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∃ l₂ ∈ (adeleClass F).adm κ, ∀ Φ ∈ schA F κ, l₂ Φ = GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hrat ν 𝓕 hν h𝓕
  have hψ : IsCharAF F B.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  set Cm : Matrix (Fin (nT + nT)) (Fin nT) (AF F ⊗[F] E) :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id with hCm
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hfin : ν 𝓕 < ⊤ :=
    GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  haveI : IsModuleTopology (AF F) (Matrix (Fin (nT + nT)) (Fin nS) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (nT + nT) → Fin nS → AE F E))
  have hce : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hCu : Continuous fun u : WOF F E nS nT => Cm * u := continuous_const.matrix_mul continuous_id
  have hcont : ∀ Φ ∈ schA F κ, Continuous fun u : WOF F E nS nT => thetaTr F co B.ψ Φ (Cm * u) :=
    fun Φ hΦ => ((schA_cont F B.ψ hψ.1 hψ.2.1 hΦ).2.comp hce).comp hCu
  have hint : ∀ Φ ∈ schA F κ, Integrable (fun u => thetaTr F co B.ψ Φ (Cm * u)) (ν.restrict 𝓕) := fun Φ hΦ => by
    obtain ⟨C, hC⟩ := thetaSum_schA_bdd F B.ψ hψ.1 hψ.2.1 hΦ
    exact Integrable.of_bound (hcont Φ hΦ).aestronglyMeasurable C (Filter.Eventually.of_forall fun u => hC _)
  have hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, ∀ w,
      thetaTr F co B.ψ (Φ + Ψ) w = thetaTr F co B.ψ Φ w + thetaTr F co B.ψ Ψ w := by
    intro Φ hΦ Ψ hΨ w
    have e : schr B.ψ (co.e w) (Φ + Ψ) = schr B.ψ (co.e w) Φ + schr B.ψ (co.e w) Ψ :=
      funext fun x => by simp [schr, mul_add]
    show thetaSum F (schr B.ψ (co.e w) (Φ + Ψ)) = thetaSum F (schr B.ψ (co.e w) Φ) + thetaSum F (schr B.ψ (co.e w) Ψ)
    rw [e]
    exact ((schA_cont F B.ψ hψ.1 hψ.2.1 hΦ).1 _).tsum_add ((schA_cont F B.ψ hψ.1 hψ.2.1 hΨ).1 _)
  have hsmul : ∀ (a : ℂ) (Φ : (κ → AF F) → ℂ) w, thetaTr F co B.ψ (a • Φ) w = a * thetaTr F co B.ψ Φ w := by
    intro a Φ w
    have e : schr B.ψ (co.e w) (a • Φ) = a • schr B.ψ (co.e w) Φ := funext fun x => by
      simp only [schr, Pi.smul_apply, smul_eq_mul]
      ring
    show thetaSum F (schr B.ψ (co.e w) (a • Φ)) = a * thetaSum F (schr B.ψ (co.e w) Φ)
    rw [e, thetaSum_smul]
  let L : schA F κ →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => GlobalTheory.LagrTheta.lagrInt ν 𝓕 Cm (thetaTr F co B.ψ Φ)
      map_add' := fun Φ Ψ => by
        show ∫ u in 𝓕, thetaTr F co B.ψ (Φ.1 + Ψ.1) (Cm * u) ∂ν =
          ∫ u in 𝓕, thetaTr F co B.ψ Φ.1 (Cm * u) ∂ν + ∫ u in 𝓕, thetaTr F co B.ψ Ψ.1 (Cm * u) ∂ν
        simp_rw [hadd Φ.1 Φ.2 Ψ.1 Ψ.2]
        exact integral_add (hint _ Φ.2) (hint _ Ψ.2)
      map_smul' := fun a Φ => by
        show ∫ u in 𝓕, thetaTr F co B.ψ (a • Φ.1) (Cm * u) ∂ν = a • ∫ u in 𝓕, thetaTr F co B.ψ Φ.1 (Cm * u) ∂ν
        simp_rw [hsmul]
        rw [integral_const_mul, smul_eq_mul] }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend L
  have hlL : ∀ Φ (hΦ : Φ ∈ schA F κ), l Φ = L ⟨Φ, hΦ⟩ := fun Φ hΦ => LinearMap.congr_fun hl ⟨Φ, hΦ⟩
  refine ⟨l, ?_, fun Φ hΦ => hlL Φ hΦ⟩
  intro g hg
  obtain ⟨k, c, hc, hb⟩ := thetaSum_pure_le F B.ψ hψ.2.1 hg
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hsn : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f =
        ((Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
    intro f
    rw [Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
    congr 2
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => L ⟨pureA F f g, hmem f⟩)
    (fun f f' => ?_) (fun a f => ?_) ⟨Finset.Iic (k, 0), c * ν.real 𝓕, mul_nonneg hc measureReal_nonneg, fun f => ?_⟩,
    fun f => ?_⟩
  · rw [← map_add]
    congr 1
    exact Subtype.ext (funext fun x => by simp [pureA, add_mul])
  · rw [RingHom.id_apply, ← map_smul]
    congr 1
    exact Subtype.ext (funext fun x => by simp [pureA, mul_assoc])
  · show ‖∫ u in 𝓕, thetaTr F co B.ψ (pureA F f g) (Cm * u) ∂ν‖ ≤ _
    refine (norm_setIntegral_le_of_norm_le_const hfin fun u _ => hb f (co.e (Cm * u))).trans (le_of_eq ?_)
    rw [hsn]
    ring
  · exact hlL _ (hmem f)

end GlobalTheory.LagrThetaAdm

end
