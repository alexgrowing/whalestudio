import Mathlib
import GroundTheory.AutomorphicForms.HaarSK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitBasisCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviLiftOfAdaptedPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryFiniteInfiniteSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHaarRightInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain

noncomputable section

namespace GlobalTheory.KAvg

section Abstract
open MeasureTheory Topology
open scoped NNReal ENNReal Pointwise

theorem lintegral_K_mul_right {G T : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (K : Subgroup G) (hK : IsCompact (K : Set G))
    (κ : Measure K) (τ : Measure T) (π : T → G) (hπ : Measurable π) (d : T → ℝ≥0∞) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ⊤)
    (hform : ∀ φ : G → ℝ≥0∞, Measurable φ → ∫⁻ g, φ g ∂μ = c * ∫⁻ k, ∫⁻ t, φ (π t * k.1) * d t ∂τ ∂κ)
    (hinv : ∀ g, ∃ k ∈ K, ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ t, f (π t * g) ∂τ = ∫⁻ t, f (π t * k) ∂τ)
    (ψ : G → ℝ≥0) (hψ : Continuous ψ) (heq : ∀ t g, (ψ (π t * g) : ℝ≥0∞) * d t = ψ g) (g : G) :
    ∫⁻ k, (ψ (k.1 * g) : ℝ≥0∞) ∂κ = ∫⁻ k, (ψ k.1 : ℝ≥0∞) ∂κ := by
  obtain ⟨A, hA, hA1⟩ := exists_compact_mem_nhds (1 : G)
  set C : Set G := A * (K : Set G) with hC
  have hCc : IsCompact C := hA.mul hK
  have hAC : A ⊆ C := fun a ha => ⟨a, ha, 1, K.one_mem, mul_one a⟩
  have hpos : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ (Filter.mem_of_superset hA1 hAC)).ne'
  have hCK : ∀ x, ∀ k ∈ K, x * k ∈ C ↔ x ∈ C := by
    intro x k hk
    constructor
    · rintro ⟨a, ha, k', hk', he⟩
      exact ⟨a, ha, k' * k⁻¹, K.mul_mem hk' (K.inv_mem hk), by
        dsimp only at he ⊢; rw [← mul_assoc, he, mul_inv_cancel_right]⟩
    · rintro ⟨a, ha, k', hk', he⟩
      exact ⟨a, ha, k' * k, K.mul_mem hk' hk, by dsimp only at he ⊢; rw [← mul_assoc, he]⟩
  set β : G → ℝ≥0∞ := C.indicator 1 with hβ
  have hβm : Measurable β := measurable_one.indicator hCc.measurableSet
  have hβK : ∀ x, ∀ k ∈ K, β (x * k) = β x := fun x k hk => by
    by_cases hx : x ∈ C
    · rw [hβ, Set.indicator_of_mem hx, Set.indicator_of_mem ((hCK x k hk).2 hx)]; rfl
    · rw [hβ, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hCK x k hk).1 h))]
  set b : ℝ≥0∞ := ∫⁻ t, β (π t) ∂τ with hb
  have hB : ∀ h, ∫⁻ t, β (π t * h) ∂τ = b := fun h => by
    obtain ⟨k, hk, e⟩ := hinv h
    rw [e β hβm]
    exact lintegral_congr fun t => hβK _ k hk
  have hb0 : b ≠ 0 := by
    intro h0
    apply hpos
    have h1 := hform β hβm
    rw [hβ, lintegral_indicator_one hCc.measurableSet, ← hβ] at h1
    rw [h1]
    have h2 : ∀ k : K, ∫⁻ t, β (π t * k.1) * d t ∂τ = 0 := fun k => by
      have h3 := (lintegral_eq_zero_iff (hβm.comp (hπ.mul_const k.1))).1 ((hB k.1).trans h0)
      rw [lintegral_congr_ae (g := fun _ => 0) (h3.mono fun t ht => by
        have ht' : β (π t * k.1) = 0 := ht
        simp only [ht', zero_mul]), lintegral_zero]
    simp only [h2, lintegral_zero, mul_zero]
  have key : ∀ φ : G → ℝ≥0, Continuous φ → (∀ t g, (φ (π t * g) : ℝ≥0∞) * d t = φ g) → ∀ x,
      ∫⁻ h, β (h * x) * φ h ∂μ = c * ∫⁻ k, b * φ k.1 ∂κ := by
    intro φ hφ he x
    rw [hform (fun h => β (h * x) * φ h) ((hβm.comp (measurable_mul_const x)).mul (ENNReal.continuous_coe.comp hφ).measurable)]
    congr 1
    refine lintegral_congr fun k => ?_
    rw [← hB (k.1 * x), ← lintegral_mul_const' _ _ ENNReal.coe_ne_top]
    refine lintegral_congr fun t => ?_
    rw [mul_assoc, he, mul_assoc]
  have hψg : Continuous fun h => ψ (h * g) := hψ.comp (continuous_mul_right g)
  have k1 := key ψ hψ heq g⁻¹
  have k2 := key (fun h => ψ (h * g)) hψg (fun t h => by rw [mul_assoc, heq]) 1
  have k3 : ∫⁻ h, β (h * g⁻¹) * ψ h ∂μ = ∫⁻ h, β (h * 1) * ψ (h * g) ∂μ := by
    rw [← lintegral_mul_right_eq_self (fun h => β (h * g⁻¹) * ψ h) g]
    simp only [mul_inv_cancel_right, mul_one]
  have hfin : ∫⁻ h, β (h * 1) * ψ (h * g) ∂μ ≠ ⊤ := by
    obtain ⟨M, hM⟩ := (hCc.image hψg).bddAbove
    refine ne_top_of_le_ne_top (b := ∫⁻ h, C.indicator (fun _ => (M : ℝ≥0∞)) h ∂μ) ?_ (lintegral_mono fun h => ?_)
    · rw [lintegral_indicator_const hCc.measurableSet]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top hCc.measure_lt_top.ne
    · by_cases hx : h ∈ C
      · rw [mul_one, hβ, Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul]
        exact ENNReal.coe_le_coe.2 (hM ⟨h, hx, rfl⟩)
      · rw [mul_one, hβ, Set.indicator_of_notMem hx, zero_mul]
        exact zero_le
  have m1 : Measurable fun k : K => (ψ k.1 : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp (hψ.comp continuous_subtype_val)).measurable
  have m2 : Measurable fun k : K => (ψ (k.1 * g) : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp (hψg.comp continuous_subtype_val)).measurable
  rw [lintegral_const_mul _ m1] at k1
  rw [lintegral_const_mul _ m2] at k2
  have e := k2.symm.trans (k3.symm.trans k1)
  have e' := (ENNReal.mul_right_inj hc0 hcT).1 e
  by_cases hbT : b = ⊤
  · have z : ∀ I : ℝ≥0∞, c * (b * I) ≠ ⊤ → I = 0 := fun I hI => by
      by_contra h0
      apply hI
      rw [hbT, ENNReal.top_mul h0, ENNReal.mul_top hc0]
    exact (z _ (by rw [← k2]; exact hfin)).trans (z _ (by rw [← k1, k3]; exact hfin)).symm
  · exact (ENNReal.mul_right_inj hb0 hbT).1 e'

end Abstract

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem hom_eq_one_of_compact {G : Type} [Group G] [TopologicalSpace G] (L : Subgroup G) (hL : IsCompact (L : Set G))
    (φ : G →* ℝ≥0) (hφ : Continuous φ) {l : G} (hl : l ∈ L) : φ l = 1 := by
  obtain ⟨C, hC⟩ := (hL.image hφ).bddAbove
  have key : ∀ m ∈ L, φ m ≤ 1 := fun m hm => by
    by_contra h
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.1 h)
    exact not_le.2 hk (by rw [← map_pow]; exact hC ⟨_, pow_mem hm k, rfl⟩)
  refine le_antisymm (key l hl) ?_
  have h1 := key _ (inv_mem hl)
  calc (1 : ℝ≥0) = φ l * φ l⁻¹ := by rw [← map_mul, mul_inv_cancel, map_one]
    _ ≤ φ l * 1 := by gcongr
    _ = _ := mul_one _

section Height

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def cf (x : Fin n → E) (i : Fin n) (p : UA σ J) : AE F E :=
  (mat p *ᵥ incV F x) i * inclR (F := F) (AF F) (x i)⁻¹

theorem cf_eq {x : Fin n → E} {i : Fin n} (hxi : x i ≠ 0) {p : UA σ J} {l : AE F E}
    (hl : mat p *ᵥ incV F x = l • incV F x) : cf x i p = l := by
  rw [cf, hl, Pi.smul_apply, smul_eq_mul, mul_assoc, incV, ← map_mul, mul_inv_cancel₀ hxi, map_one, mul_one]

theorem continuous_mat : Continuous (mat : UA σ J → Matrix (Fin n) (Fin n) (AE F E)) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_cf (x : Fin n → E) (i : Fin n) : Continuous (cf (σ := σ) (J := J) x i) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  exact ((continuous_apply i).comp (continuous_mat.matrix_mulVec continuous_const)).mul continuous_const

def eigHom {x : Fin n → E} {i : Fin n} (hxi : x i ≠ 0) : GlobalTheory.IwLine.lineStab σ J x →* AE F E where
  toFun p := cf x i p.1
  map_one' := cf_eq hxi (by rw [Subgroup.coe_one, GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec, one_smul])
  map_mul' p q := by
    obtain ⟨a, ha⟩ := p.2
    obtain ⟨b, hb⟩ := q.2
    rw [cf_eq hxi ha, cf_eq hxi hb]
    refine cf_eq hxi ?_
    rw [Subgroup.coe_mul, GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_smul, ha, smul_smul, mul_comm]

theorem continuous_eigU {x : Fin n → E} {i : Fin n} (hxi : x i ≠ 0) :
    Continuous (eigHom (σ := σ) (J := J) hxi).toHomUnits := by
  haveI := (GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n J).1
  refine Units.continuous_iff.2 ⟨(continuous_cf x i).comp continuous_subtype_val, ?_⟩
  have e : (fun m => ((((eigHom (σ := σ) (J := J) hxi).toHomUnits m)⁻¹ : (AE F E)ˣ) : AE F E)) =
      fun m => cf x i (m⁻¹).1 := funext fun m => by rw [← map_inv]; rfl
  rw [e]
  exact (continuous_cf x i).comp (continuous_subtype_val.comp continuous_inv)

theorem exists_height {x : Fin n → E} {i : Fin n} (hxi : x i ≠ 0) (K : Subgroup (UA σ J)) (hK : IsCompact (K : Set (UA σ J)))
    (hP : IsClosed (GlobalTheory.IwLine.lineStab σ J x : Set (UA σ J)))
    (hdec : ∀ g, ∃ p ∈ GlobalTheory.IwLine.lineStab σ J x, ∃ k ∈ K, g = p * k) :
    ∃ h : UA σ J → ℝ≥0, Continuous h ∧ (∀ k ∈ K, h k = 1) ∧
      ∀ (p g : UA σ J) (l : (AE F E)ˣ), mat p *ᵥ incV F x = l.1 • incV F x → h (p * g) = absE F E l * h g := by
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n J
  haveI := t1; haveI := t2; haveI := t3; haveI := t4
  let φ : GlobalTheory.IwLine.lineStab σ J x →* ℝ≥0 := (absE F E).comp (eigHom hxi).toHomUnits
  have hφ : Continuous φ := GlobalTheory.Doubling.continuous_absE.comp (continuous_eigU hxi)
  have hsurj : Function.Surjective (GroundTheory.Automorphic.HaarSK.mulMap (GlobalTheory.IwLine.lineStab σ J x) K) := fun g => by
    obtain ⟨p, hp, k, hk, rfl⟩ := hdec g
    exact ⟨(⟨p, hp⟩, ⟨k, hk⟩), rfl⟩
  have hL : IsCompact ((GroundTheory.Automorphic.HaarSK.inter (GlobalTheory.IwLine.lineStab σ J x) K : Subgroup _) :
      Set (GlobalTheory.IwLine.lineStab σ J x)) := by
    rw [Subgroup.coe_subgroupOf]
    exact hP.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hu : ∀ s, ∀ m ∈ GroundTheory.Automorphic.HaarSK.inter (GlobalTheory.IwLine.lineStab σ J x) K,
      (fun s => (φ s : ℝ)) (s * m) = (fun s => (φ s : ℝ)) s := fun s m hm => by
    simp only [map_mul, hom_eq_one_of_compact _ hL φ hφ hm, mul_one]
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GlobalTheory.IwLine.lineStab σ J x) := hP.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : CompactSpace (GroundTheory.Automorphic.HaarSK.inter (GlobalTheory.IwLine.lineStab σ J x) K) := isCompact_iff_compactSpace.1 hL
  have hc := GroundTheory.Automorphic.HaarSK.continuous_lift hP hK hsurj hu (NNReal.continuous_coe.comp hφ)
  have hv : ∀ (s : GlobalTheory.IwLine.lineStab σ J x) (k : K),
      (GroundTheory.Automorphic.HaarSK.lift hsurj (fun s => (φ s : ℝ)) (s.1 * k.1)).toNNReal = φ s := fun s k => by
    rw [GroundTheory.Automorphic.HaarSK.lift_mul hu, Real.toNNReal_coe]
  refine ⟨fun g => (GroundTheory.Automorphic.HaarSK.lift hsurj (fun s => (φ s : ℝ)) g).toNNReal,
    continuous_real_toNNReal.comp hc, fun k hk => ?_, fun p g l hl => ?_⟩
  · have := hv 1 ⟨k, hk⟩
    rwa [Subgroup.coe_one, one_mul, map_one] at this
  · obtain ⟨q, hq, k, hk, rfl⟩ := hdec g
    have e1 := hv (⟨p, l, hl⟩ * ⟨q, hq⟩) ⟨k, hk⟩
    have e2 := hv ⟨q, hq⟩ ⟨k, hk⟩
    have e3 : φ ⟨p, l, hl⟩ = absE F E l := congrArg (absE F E) (Units.ext (cf_eq hxi hl))
    dsimp only at e1 e2 ⊢
    rw [e2, ← e3, ← map_mul, ← e1, ← mul_assoc]
    rfl

end Height

section Proj

open GlobalTheory.ArchFinSplit

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

variable (σ J) in

def prH {e : AF F} (he : IsIdempotentElem e) : UA σ J →* UA σ J where
  toFun g := ⟨prU he g.1, prU_mem he _ _ g.1 g.2⟩
  map_one' := Subtype.ext (Units.ext (pr_one e))
  map_mul' _ _ := Subtype.ext (Units.ext (pr_mul he _ _).symm)

theorem mat_prH {e : AF F} (he : IsIdempotentElem e) (g : UA σ J) : mat (prH σ J he g) = pr e (mat g) := rfl

theorem continuous_prH {e : AF F} (he : IsIdempotentElem e) : Continuous (prH σ J he) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := (GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n J).1
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (continuous_mat.const_smul e).add continuous_const
  · exact ((continuous_mat.comp continuous_inv).const_smul e).add continuous_const

theorem prH_mul_prH {e : AF F} (he : IsIdempotentElem e) (g : UA σ J) : prH σ J he g * prH σ J he.one_sub g = g :=
  Subtype.ext (Units.ext (pr_mul_pr_compl he _))

def prUnit {e : AF F} (he : IsIdempotentElem e) (l : (AE F E)ˣ) : (AE F E)ˣ where
  val := e • l.1 + (1 - e) • 1
  inv := e • (l⁻¹).1 + (1 - e) • 1
  val_inv := by
    have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
    have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, he.eq, he.one_sub.eq, h1, h2,
      zero_smul, add_zero, zero_add, Units.mul_inv, mul_one]
    rw [← add_smul, add_sub_cancel, one_smul]
  inv_val := by
    have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
    have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, he.eq, he.one_sub.eq, h1, h2,
      zero_smul, add_zero, zero_add, Units.inv_mul, mul_one]
    rw [← add_smul, add_sub_cancel, one_smul]

theorem prUnit_mul {e : AF F} (he : IsIdempotentElem e) (l : (AE F E)ˣ) : prUnit he l * prUnit he.one_sub l = l := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  refine Units.ext ?_
  show (e • l.1 + (1 - e) • 1) * ((1 - e) • l.1 + (1 - (1 - e)) • 1) = l.1
  simp only [sub_sub_cancel, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, he.eq, he.one_sub.eq,
    h1, h2, zero_smul, add_zero, zero_add, mul_one, one_mul]
  rw [← add_smul, sub_add_cancel, one_smul]

theorem prH_mulVec {e : AF F} (he : IsIdempotentElem e) {g : UA σ J} {v : Fin n → AE F E} {l : (AE F E)ˣ}
    (hl : mat g *ᵥ v = l.1 • v) : mat (prH σ J he g) *ᵥ v = (prUnit he l).1 • v := by
  rw [mat_prH, pr, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hl]
  show _ = (e • l.1 + (1 - e) • (1 : AE F E)) • v
  rw [add_smul, smul_assoc, smul_assoc, one_smul]

variable (F) in
theorem realAd_one_fst : (realAd F 1).1 = 1 := by
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ 1) = 1
  rw [map_one, map_one]

variable (F) in

theorem idem_realAd : IsIdempotentElem (realAd F 1) :=
  Prod.ext (show (realAd F 1).1 * (realAd F 1).1 = _ by rw [realAd_one_fst, mul_one]) (show (0 : Af F) * 0 = 0 from mul_zero _)

variable {X : Spc F E n}

theorem prH_mem (g : UA σ X.J) : prH σ X.J (idem_realAd F) g ∈ UAt σ X (evI F) := by
  show At (evI F) (pr (realAd F 1) (mat g) - 1)
  rw [pr_sub_one]
  exact at_partInf (mat g - 1)

theorem prH_of_mem {g : UA σ X.J} (hg : g ∈ UAt σ X (evI F)) : prH σ X.J (idem_realAd F) g = g := by
  refine Subtype.ext (Units.ext ?_)
  show pr (realAd F 1) (mat g) = mat g
  rw [← sub_left_inj (a := 1), pr_sub_one]
  exact partInf_of_at hg

theorem prH_mem_KAt {B : Base F E} {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {k : UA σ X.J} (hk : k ∈ K) :
    prH σ X.J (idem_realAd F) k ∈ KAt K (evI F) := by
  refine (mem_KAt_inf hK).2 ⟨prH_mem k, fun w => ?_⟩
  have h1 : evInf F w (realAd F 1) = 1 := by
    show (realAd F 1).1 w = 1
    rw [realAd_one_fst]; rfl
  have e : (mat (prH σ X.J (idem_realAd F) k)).map (piInf (B.emb w)) = (mat k).map (piInf (B.emb w)) := by
    ext i j
    simp only [mat_prH, pr, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, piInf, RingHom.comp_apply, map_add,
      compInf_smul, map_sub, map_one, h1, sub_self, zero_smul, one_smul, map_zero, add_zero]
  rw [e]
  exact ((hK k).1 hk).1 w

end Proj

open GlobalTheory.UnipMass GlobalTheory.UnipMassHerm in

theorem unip_isMulRightInvariant {B : Base F E} {b : ℕ} {X : Spc F E (b + 2)} {X₁ : Spc F E b} {H : Plane E (b + 2) b}
    {i₀ i₁ r s : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁)
    (μN : Measure (unip σ X H)) (hμ : μN.IsHaarMeasure) : μN.IsMulRightInvariant := by
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hB.cm
  have hspan : ∀ v : Fin (b + 2) → E, ∃ (s t : E) (u : Fin b → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
    intro v
    have hv : v ∈ Submodule.span E (X.L : Set (Fin (b + 2) → E)) := by
      rw [hX.lat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, hz⟩ := hH.split z hz
      exact ⟨s, t, u, hz⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, t, u, rfl⟩ := hy
      obtain ⟨s', t', u', rfl⟩ := hz
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul a y _ hy =>
      obtain ⟨s, t, u, rfl⟩ := hy
      exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩
  have hx0 : H.x ≠ 0 := fun h0 => by
    have h1 := hH.xy
    rw [h0] at h1
    simp [form] at h1
  obtain ⟨δ, hδ0, hδ⟩ := exists_anti hB.cm
  let W' : Spc F E (b + 2) := ⟨δ • X.J, X.L, X.θ, X.bas⟩
  let H'' : Plane E (b + 2) b := ⟨H.x, (-δ⁻¹) • H.y, H.ι, H.𝔟⟩
  have hform : ∀ v w, form σ W'.J v w = δ * form σ X.J v w := form_smul_mat σ X.J δ
  have hσt : σ (-δ⁻¹) = δ⁻¹ := by rw [map_neg, map_inv₀, hδ, inv_neg, neg_neg]
  have hxx : form σ W'.J H''.x H''.x = 0 := by rw [hform]; show δ * form σ X.J H.x H.x = 0; rw [hH.xx, mul_zero]
  have hyy : form σ W'.J H''.y H''.y = 0 := by
    rw [hform]; show δ * form σ X.J ((-δ⁻¹) • H.y) ((-δ⁻¹) • H.y) = 0
    rw [form_smul_left, form_smul_right, hH.yy]; ring
  have hxy : form σ W'.J H''.x H''.y = 1 := by
    rw [hform]; show δ * form σ X.J H.x ((-δ⁻¹) • H.y) = 1
    rw [form_smul_right, hH.xy, hσt, mul_one, mul_inv_cancel₀ hδ0]
  have horth : ∀ u, form σ W'.J (H''.ι *ᵥ u) H''.x = 0 ∧ form σ W'.J (H''.ι *ᵥ u) H''.y = 0 := by
    intro u
    refine ⟨?_, ?_⟩
    · rw [hform]; show δ * form σ X.J (H.ι *ᵥ u) H.x = 0; rw [(hH.orth u).1, mul_zero]
    · rw [hform]; show δ * form σ X.J (H.ι *ᵥ u) ((-δ⁻¹) • H.y) = 0; rw [form_smul_right, (hH.orth u).2]; ring
  have hspan'' : ∀ v : Fin (b + 2) → E, ∃ (s t : E) (u : Fin b → E), v = s • H''.x + H''.ι *ᵥ u + t • H''.y := by
    intro v
    obtain ⟨s, t, u, hv⟩ := hspan v
    refine ⟨s, t * -δ, u, ?_⟩
    show v = s • H.x + H.ι *ᵥ u + (t * -δ) • (-δ⁻¹) • H.y
    rw [smul_smul, show t * -δ * -δ⁻¹ = t by field_simp, hv]
  have horthA : ∀ z, hA σ W'.J (incM F H''.ι *ᵥ z) (incV F H''.x) = 0 := by
    intro z
    rw [hA_incM_incV]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 := (horth (Pi.single j 1)).1
    rw [Matrix.mulVec_single_one] at h1
    rw [show (fun i => H''.ι i j) = H''.ι.col j from rfl, h1, map_zero, mul_zero]
  have hyp : Hyp σ W' H'' := by
    refine ⟨hσ, fun i j => ?_, by rw [hA_incV, hxx, map_zero], horthA⟩
    show σ (δ * X.J j i) = -(δ * X.J i j)
    rw [map_mul, hδ, hX.herm]; ring
  obtain ⟨K', hK', hcov'⟩ := cocompact hyp hxx hyy hxy horth hspan''
  have hUG := UG_smul (F := F) σ X.J hδ0
  let φ : UA σ W'.J →* UA σ X.J := Subgroup.inclusion hUG.le
  let φ' : UA σ X.J →* UA σ W'.J := Subgroup.inclusion hUG.ge
  have hmap : (unip σ W' H'').map φ ≤ unip σ X H := by
    rw [unip, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  have hmap' : (unip σ X H).map φ' ≤ unip σ W' H'' := by
    rw [unip, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  let Ψ : unip σ W' H'' → unip σ X H := fun g => ⟨φ g.1, hmap ⟨g.1, g.2, rfl⟩⟩
  have hΨ : Continuous Ψ :=
    Continuous.subtype_mk (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) _
  have hcov : ∀ g : unip σ X H, ∃ γ : (ratU σ X.J).subgroupOf (unip σ X H), γ • g ∈ Ψ '' K' := by
    intro g
    obtain ⟨γ', hγ'⟩ := hcov' ⟨φ' g.1, hmap' ⟨g.1, g.2, rfl⟩⟩
    refine ⟨⟨Ψ γ'.1, ?_⟩, ⟨_, hγ', ?_⟩⟩
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2
        (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 γ'.2)))
    · exact unip_ext rfl
  obtain ⟨hTG, hLC, hSC, hT2⟩ := topUA σ X.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have hcl := GlobalTheory.T.unipotent_radical_closed_nonzero F E σ _ _ X H hx0
  haveI : LocallyCompactSpace (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ X H) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := countable_ratU' σ X.J (unip σ X H)
  haveI := GlobalTheory.T.discrete_rational_points_subgroup F E σ _ X.J (unip σ X H)
  haveI := hμ
  obtain ⟨𝓕, h𝓕, h0, h1⟩ := exists_fundDom_pos_finite _ (Ψ '' K') (hK'.image hΨ) hcov μN
  exact GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain _ μN h𝓕 h0 h1

section Adelic

variable {B : Base F E} {b : ℕ} {X : Spc F E (b + 2)} {X₁ : Spc F E b} {H : Plane E (b + 2) b} {i₀ i₁ r s : ℕ}

theorem isCompact_stabK {n : ℕ} {X : Spc F E n} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) :
    IsCompact ((GlobalTheory.StabHaar.stabK (σ := σ) B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by
  obtain ⟨C, hC, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B n X r s hB hX
  exact hC.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B X (GlobalTheory.T.isClosed_adelic_lattice_closure F E n X hX.lat)) hsub

theorem unip_fix {n n₁ : ℕ} {X : Spc F E n} {H : Plane E n n₁} {u : UA σ X.J} (hu : u ∈ unip σ X H) :
    mat u *ᵥ incV F H.x = incV F H.x := by
  induction hu using Subgroup.closure_induction with
  | mem u hu => exact hu.1
  | one => rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
  | mul u v _ _ hu hv => rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hv, hu]
  | inv u _ hu =>
    calc mat u⁻¹ *ᵥ incV F H.x = mat u⁻¹ *ᵥ (mat u *ᵥ incV F H.x) := by rw [hu]
      _ = incV F H.x := by rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]

theorem absE_pos (l : (AE F E)ˣ) : 0 < absE F E l := by
  refine pos_iff_ne_zero.2 fun h => ?_
  have h1 := map_mul_eq_one (absE F E) (mul_inv_cancel l)
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem adelic_kavg (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁)
    (κ : Measure (GlobalTheory.StabHaar.stabK (σ := σ) B X)) [κ.IsHaarMeasure] (ψ : UA σ X.J → ℝ≥0) (hψ : Continuous ψ)
    (heq : ∀ (p g : UA σ X.J) (l : (AE F E)ˣ), mat p *ᵥ incV F H.x = l.1 • incV F H.x →
      ψ (p * g) = absE F E l ^ (b + 1) * ψ g) (g : UA σ X.J) :
    ∫⁻ k, (ψ (k.1 * g) : ℝ≥0∞) ∂κ = ∫⁻ k, (ψ k.1 : ℝ≥0∞) ∂κ := by
  have hX₁ := GlobalTheory.HermPlaneCompl.isHerm_compl hB hX hH
  choose m hm using GlobalTheory.LeviFrameH.exists_levi_herm F E σ B _ _ X X₁ H r s i₀ i₁ hB hX hH
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (b + 2) X.J
  obtain ⟨u1, u2, u3, u4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ b X₁.J
  obtain ⟨v1, v2, v3, v4⟩ := GlobalTheory.IwInt.ideleTop (F := F) (E := E)
  haveI := t1; haveI := t2; haveI := t3; haveI := t4; haveI := u1; haveI := u2; haveI := u3; haveI := u4
  haveI := v1; haveI := v2; haveI := v3; haveI := v4
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ X₁.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨hmul, hcont, -, huniq, -, hNc, -, hnorm⟩ :=
    GlobalTheory.T.levi_embedding_multiplicative F E σ B _ _ X X₁ r s _ _ i₀ i₁ H hB hX hX₁ hH m hm
  haveI : LocallyCompactSpace (unip σ X H) := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ X H) := TopologicalSpace.Subtype.secondCountableTopology _
  let μG : Measure (UA σ X.J) := Measure.haar
  let μ : Measure (AE F E)ˣ := Measure.haar
  let μ₁ : Measure (UA σ X₁.J) := Measure.haar
  obtain ⟨μN, c, hμN, hc0, hcT, hform⟩ := GlobalTheory.IwInt.intform B hB hX hX₁ hH μG κ μ μ₁ m hm
  haveI := hμN
  haveI := GlobalTheory.HermUnimod.isMulRightInvariant_of_isHerm F E σ B _ X r s hB hX μG inferInstance
  haveI := GlobalTheory.HermUnimod.isMulRightInvariant_of_isHerm F E σ B _ X₁ _ _ hB hX₁ μ₁ inferInstance
  haveI := unip_isMulRightInvariant hB hX hH μN hμN
  haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (UA σ X₁.J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (unip σ X H) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  haveI : SigmaFinite μ₁ := Measure.IsHaarMeasure.sigmaFinite μ₁
  haveI : SigmaFinite μN := Measure.IsHaarMeasure.sigmaFinite μN
  let π : (AE F E)ˣ × UA σ X₁.J × unip σ X H → UA σ X.J := fun t => t.2.2.1 * m t.1 t.2.1
  have hπc : Continuous π := (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).mul
    (hcont.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
  have hπ : Measurable π := hπc.measurable
  let d : (AE F E)ˣ → ℝ≥0∞ := fun l => ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ)))
  have hd : Measurable d := (ENNReal.continuous_ofReal.comp ((NNReal.continuous_coe.comp
      (GlobalTheory.Doubling.continuous_absE (F := F) (E := E))).rpow_const
        fun x => Or.inl (NNReal.coe_pos.2 (absE_pos x)).ne')).measurable
  have nest : ∀ f : (AE F E)ˣ × UA σ X₁.J × unip σ X H → ℝ≥0∞, Measurable f →
      ∫⁻ t, f t ∂(μ.prod (μ₁.prod μN)) = ∫⁻ l, ∫⁻ g₀, ∫⁻ u, f (l, g₀, u) ∂μN ∂μ₁ ∂μ := fun f hf => by
    rw [lintegral_prod _ hf.aemeasurable]
    exact lintegral_congr fun l => lintegral_prod _ (hf.comp measurable_prodMk_left).aemeasurable
  refine lintegral_K_mul_right μG _ (isCompact_stabK hB hX) κ (μ.prod (μ₁.prod μN)) π hπ (fun t => d t.1) c hc0 hcT
    (fun φ hφ => ?_) (fun h => ?_) ψ hψ (fun t h => ?_) g
  · rw [hform φ hφ]
    congr 1
    refine lintegral_congr fun k => ?_
    rw [nest (fun t => φ (π t * k.1) * d t.1) ((hφ.comp (hπ.mul_const _)).mul (hd.comp measurable_fst))]
  · obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.IwLine.iwasawa B hB hX hH h
    obtain ⟨⟨n₀, l₀, g₁⟩, rfl, -⟩ := huniq p hp
    refine ⟨k, hk, fun f hf => ?_⟩
    rw [nest (fun t => f (π t * _)) (hf.comp (hπ.mul_const _)), nest (fun t => f (π t * _)) (hf.comp (hπ.mul_const _))]
    rw [← lintegral_mul_right_eq_self (fun l => ∫⁻ g₀, ∫⁻ u, f (π (l, g₀, u) * k) ∂μN ∂μ₁) l₀]
    refine lintegral_congr fun l => ?_
    rw [← lintegral_mul_right_eq_self (fun g₀ => ∫⁻ u, f (π (l * l₀, g₀, u) * k) ∂μN) g₁]
    refine lintegral_congr fun g₀ => ?_
    rw [← lintegral_mul_right_eq_self (fun u => f (π (l * l₀, g₀ * g₁, u) * k))
      ⟨m l g₀ * n₀.1 * (m l g₀)⁻¹, hnorm _ ⟨l, (hm l g₀).1⟩ _ n₀.2⟩]
    refine lintegral_congr fun u => congrArg f ?_
    simp only [π, hmul, Subgroup.coe_mul]
    group
  · have hx : mat (π t) *ᵥ incV F H.x = t.1.1 • incV F H.x := by
      simp only [π]
      rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, (hm _ _).1, Matrix.mulVec_smul, unip_fix t.2.2.2]
    have ha := NNReal.coe_pos.2 (absE_pos t.1)
    have e : ((absE F E t.1 ^ (b + 1) : ℝ≥0) : ℝ≥0∞) * d t.1 = 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _), NNReal.coe_pow, ← Real.rpow_natCast,
        ← Real.rpow_add ha]
      have : ((b + 1 : ℕ) : ℝ) + (1 - ((b + 2 : ℕ) : ℝ)) = 0 := by push_cast; ring
      rw [this, Real.rpow_zero, ENNReal.ofReal_one]
    rw [heq _ h _ hx, ENNReal.coe_mul, mul_right_comm, e, one_mul]

end Adelic

set_option synthInstance.maxHeartbeats 400000 in

theorem kInf_integral_mul_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ r s : ℕ), B.IsGood σ →
    X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ K : Subgroup (UA σ X.J), IsStab B K →
    ∀ μK : Measure (KAt K (evI F)), μK.IsHaarMeasure → ∀ Ψ : UA σ X.J → ℂ, ContinuousOn Ψ (UAt σ X (evI F)) →
    (∀ p ∈ UAt σ X (evI F), ∀ g ∈ UAt σ X (evI F), ∀ t : (AE F E)ˣ, mat p *ᵥ incV F H.x = t.1 • incV F H.x →
      Ψ (p * g) = (((absE F E t : ℝ) ^ (n₁ + 1) : ℝ) : ℂ) * Ψ g) →
    ∀ g ∈ UAt σ X (evI F), ∫ k, Ψ (k.1 * g) ∂μK = ∫ k, Ψ k.1 ∂μK := by
  intro F E _ _ _ _ _ σ B b X X₁ H i₀ i₁ r s hB hX hH K hK μK hμK Ψ hΨ heq g hg
  obtain rfl : K = GlobalTheory.StabHaar.stabK B X := Subgroup.ext fun g => hK g
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (b + 2) X.J
  haveI := t1; haveI := t2; haveI := t3; haveI := t4
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have hKc := isCompact_stabK hB hX
  haveI : CompactSpace (GlobalTheory.StabHaar.stabK (σ := σ) B X) := isCompact_iff_compactSpace.1 hKc
  haveI : CompactSpace (KAt (GlobalTheory.StabHaar.stabK (σ := σ) B X) (evI F)) :=
    isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)
  haveI : SecondCountableTopology (KAt (GlobalTheory.StabHaar.stabK (σ := σ) B X) (evI F)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (KAt (GlobalTheory.StabHaar.stabK (σ := σ) B X) (evI F)) :=
    IsCompact.locallyCompactSpace_of_mem_nhds_of_group isCompact_univ (x := 1) univ_mem
  obtain ⟨κ, hκ⟩ := GlobalTheory.StabHaar.exists_haar_of_isCompact _ hKc

  obtain ⟨i, hxi⟩ : ∃ i, H.x i ≠ 0 := by
    by_contra h
    push_neg at h
    have h1 := hH.xy
    rw [show H.x = 0 from funext h] at h1
    simp [form] at h1
  choose m hm using GlobalTheory.LeviFrameH.exists_levi_herm F E σ B _ _ X X₁ H r s i₀ i₁ hB hX hH
  obtain ⟨-, -, -, -, hP, -⟩ :=
    GlobalTheory.T.levi_embedding_multiplicative F E σ B _ _ X X₁ r s _ _ i₀ i₁ H hB hX (GlobalTheory.HermPlaneCompl.isHerm_compl hB hX hH) hH m hm
  obtain ⟨ht, htc, ht1, htm⟩ := exists_height hxi _ hKc hP (GlobalTheory.IwLine.iwasawa B hB hX hH)

  set pi := prH σ X.J (idem_realAd F) with hpi
  set pf := prH σ X.J (idem_realAd F).one_sub with hpf
  have hpif : ∀ x, pf x = (pi x)⁻¹ * x := fun x => eq_inv_mul_of_mul_eq (prH_mul_prH _ x)
  let ρ : GlobalTheory.StabHaar.stabK (σ := σ) B X →* KAt (GlobalTheory.StabHaar.stabK (σ := σ) B X) (evI F) :=
    (pi.comp (Subgroup.subtype _)).codRestrict _ fun k => prH_mem_KAt hK k.2
  have hρ : Continuous ρ := ((continuous_prH _).comp continuous_subtype_val).subtype_mk _
  have hρs : Function.Surjective ρ := fun k => ⟨⟨k.1, k.2.1⟩, Subtype.ext (prH_of_mem k.2.2)⟩
  haveI : (κ.map ρ).IsHaarMeasure := Measure.isHaarMeasure_map_of_isFiniteMeasure κ ρ hρ hρs
  have hμ : μK = Measure.haarScalarFactor μK (κ.map ρ) • κ.map ρ := Measure.isMulLeftInvariant_eq_smul _ _
  have hcg : ∀ x ∈ UAt σ X (evI F), Continuous fun k : KAt (GlobalTheory.StabHaar.stabK (σ := σ) B X) (evI F) => Ψ (k.1 * x) :=
    fun x hx => hΨ.comp_continuous (continuous_subtype_val.mul continuous_const)
      fun k => (UAtSub σ X (evI F)).mul_mem k.2.2 hx
  have hc1 : Continuous fun k : KAt (GlobalTheory.StabHaar.stabK (σ := σ) B X) (evI F) => Ψ k.1 :=
    hΨ.comp_continuous continuous_subtype_val fun k => k.2.2
  have main : ∀ L : ℂ →L[ℝ] ℝ, ∫⁻ k, ENNReal.ofReal (L (Ψ (k.1 * g))) ∂μK = ∫⁻ k, ENNReal.ofReal (L (Ψ k.1)) ∂μK := by
    intro L
    let ψ : UA σ X.J → ℝ≥0 := fun x => (L (Ψ (pi x))).toNNReal * ht (pf x) ^ (b + 1)
    have hψ : Continuous ψ :=
      (continuous_real_toNNReal.comp (L.continuous.comp (hΨ.comp_continuous (continuous_prH _) prH_mem))).mul
        ((htc.comp (continuous_prH _)).pow _)
    have hlaw : ∀ (p x : UA σ X.J) (l : (AE F E)ˣ), mat p *ᵥ incV F H.x = l.1 • incV F H.x →
        ψ (p * x) = absE F E l ^ (b + 1) * ψ x := fun p x l hl => by
      simp only [ψ, map_mul]
      rw [heq _ (prH_mem p) _ (prH_mem x) _ (prH_mulVec _ hl), htm _ _ _ (prH_mulVec _ hl), ← Complex.real_smul,
        L.map_smul, smul_eq_mul, Real.toNNReal_mul (by positivity), ← NNReal.coe_pow, Real.toNNReal_coe]
      conv_rhs => rw [← prUnit_mul (idem_realAd F) l, map_mul]
      ring
    have h := adelic_kavg hB hX hH κ ψ hψ hlaw g
    have hv : ∀ x ∈ UAt σ X (evI F), ∀ k : GlobalTheory.StabHaar.stabK (σ := σ) B X,
        (ψ (k.1 * x) : ℝ≥0∞) = ENNReal.ofReal (L (Ψ ((ρ k).1 * x))) := fun x hx k => by
      have e1 : pi x = x := prH_of_mem hx
      have e2 : pf (k.1 * x) ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X := by
        rw [map_mul, hpif x, e1, inv_mul_cancel, mul_one, hpif]
        exact mul_mem (inv_mem (ρ k).2.1) k.2
      simp only [ψ]
      rw [ht1 _ e2, one_pow, mul_one, map_mul, e1]
      rfl
    have hv1 : ∀ k : GlobalTheory.StabHaar.stabK (σ := σ) B X, (ψ k.1 : ℝ≥0∞) = ENNReal.ofReal (L (Ψ (ρ k).1)) := fun k => by
      simpa only [mul_one] using hv 1 (UAtSub σ X (evI F)).one_mem k
    simp only [hv g hg, hv1] at h
    rw [hμ, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_map (f := fun k : KAt _ (evI F) => ENNReal.ofReal (L (Ψ (k.1 * g))))
        (ENNReal.continuous_ofReal.comp (L.continuous.comp (hcg g hg))).measurable hρ.measurable,
      lintegral_map (f := fun k : KAt _ (evI F) => ENNReal.ofReal (L (Ψ k.1)))
        (ENNReal.continuous_ofReal.comp (L.continuous.comp hc1)).measurable hρ.measurable, h]
  have i1 : Integrable (fun k : KAt _ (evI F) => Ψ (k.1 * g)) μK :=
    (hcg g hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable (fun k : KAt _ (evI F) => Ψ k.1) μK :=
    hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have real : ∀ L : ℂ →L[ℝ] ℝ, L (∫ k, Ψ (k.1 * g) ∂μK) = L (∫ k, Ψ k.1 ∂μK) := fun L => by
    rw [← L.integral_comp_comm i1, ← L.integral_comp_comm i2,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (L.integrable_comp i1),
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (L.integrable_comp i2)]
    have a := main L
    have a' := main (-L)
    simp only [ContinuousLinearMap.neg_apply] at a'
    rw [a, a']
  exact Complex.ext (real Complex.reCLM) (real Complex.imCLM)

end GlobalTheory.KAvg
