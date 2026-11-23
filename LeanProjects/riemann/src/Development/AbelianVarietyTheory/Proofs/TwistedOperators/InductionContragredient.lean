import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIntegralGLMulRightComplexProductSigma

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology

namespace GlobalTheory.SmGL.IndDual

section Abstract

variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W'] {P : Subgroup G}

def cell (P J : Subgroup G) : Set G := {g | ∃ p : P, (p : G)⁻¹ * g ∈ J}

theorem isOpen_cell {J : Subgroup G} (hJ : IsOpen (J : Set G)) : IsOpen (cell P J) := by
  have : cell P J = ⋃ p : P, (fun g => (p : G)⁻¹ * g) ⁻¹' J := by ext; simp [cell]
  rw [this]
  exact isOpen_iUnion fun p => hJ.preimage (by fun_prop)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem cell_cases (J : Subgroup G) (g : G) : g ∉ cell P J ∨ ∃ p : P, ∃ j ∈ J, g = p * j := by
  by_cases h : g ∈ cell P J
  · obtain ⟨p, hp⟩ := h
    exact Or.inr ⟨p, _, hp, by simp⟩
  · exact Or.inl h

open Classical in

def extFun (σ : Representation ℂ P W) (J : Subgroup G) (φ : G → W) (g : G) : W :=
  if h : g ∈ cell P J then σ h.choose (φ ((h.choose : G)⁻¹ * g)) else 0

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem extFun_mul {σ : Representation ℂ P W} {J : Subgroup G} {φ : G → W}
    (hφ : ∀ p : P, (p : G) ∈ J → ∀ j ∈ J, φ (p * j) = σ p (φ j)) (p : P) {j : G} (hj : j ∈ J) :
    extFun σ J φ (p * j) = σ p (φ j) := by
  have h : (p : G) * j ∈ cell P J := ⟨p, by simpa using hj⟩
  rw [extFun, dif_pos h]
  have h1 := h.choose_spec
  generalize h.choose = q at h1
  have h2 : ((q⁻¹ * p : P) : G) ∈ J := by simpa [mul_assoc] using mul_mem h1 (inv_mem hj)
  have h3 := hφ _ h2 j hj
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] at h3
  rw [h3, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem extFun_zero (σ : Representation ℂ P W) {J : Subgroup G} (φ : G → W) {g : G}
    (h : g ∉ cell P J) : extFun σ J φ g = 0 := dif_neg h

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem extFun_right {σ : Representation ℂ P W} {J : Subgroup G} {φ : G → W}
    (hφ : ∀ p : P, (p : G) ∈ J → ∀ j ∈ J, φ (p * j) = σ p (φ j)) {i : G} (hi : i ∈ J)
    (hφ' : ∀ j ∈ J, φ (j * i) = φ j) (g : G) : extFun σ J φ (g * i) = extFun σ J φ g := by
  rcases cell_cases (P := P) J g with h | ⟨p, j, hj, rfl⟩
  · rw [extFun_zero _ _ h, extFun_zero]
    rintro ⟨p, hp⟩
    exact h ⟨p, by simpa [mul_assoc] using mul_mem hp (inv_mem hi)⟩
  · rw [mul_assoc, extFun_mul hφ p hj, extFun_mul hφ p (mul_mem hj hi), hφ' j hj]

def extInd (σ : Representation ℂ P W) {J I : Subgroup G} (hI : IsOpen (I : Set G)) (hle : I ≤ J) (φ : G → W)
    (hφ : ∀ p : P, (p : G) ∈ J → ∀ j ∈ J, φ (p * j) = σ p (φ j))
    (hφ' : ∀ i ∈ I, ∀ j ∈ J, φ (j * i) = φ j) : smoothPart (ind P σ) :=
  ⟨⟨extFun σ J φ, fun q g => by
      rcases cell_cases (P := P) J g with h | ⟨p, j, hj, rfl⟩
      · rw [extFun_zero _ _ h, extFun_zero, map_zero]
        rintro ⟨p, hp⟩
        exact h ⟨q⁻¹ * p, by simpa [mul_assoc] using hp⟩
      · rw [← mul_assoc, ← Subgroup.coe_mul, extFun_mul hφ _ hj, extFun_mul hφ _ hj, map_mul,
          Module.End.mul_apply]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hI.mem_nhds (one_mem I)) fun i hi =>
      Subtype.ext (funext fun g => extFun_right hφ (hle hi) (hφ' i hi) g))⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem mem_fixed_iff {σ : Representation ℂ G W} {H : Subgroup G} {w : W} :
    w ∈ fixed σ H ↔ ∀ h ∈ H, σ h w = w :=
  ⟨fun hw h hh => by simpa using hw ⟨h, hh⟩, fun hw h => by simpa using hw h h.2⟩

def bump (σ : Representation ℂ P W) {J : Subgroup G} (hJ : IsOpen (J : Set G)) :
    fixed σ (J.subgroupOf P) →ₗ[ℂ] smoothPart (ind P σ) where
  toFun w := extInd σ hJ le_rfl (fun _ => w.1) (fun p hp _ _ => (mem_fixed_iff.1 w.2 p hp).symm)
    fun _ _ _ _ => rfl
  map_add' v w := by
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    show extFun σ J (fun _ => v.1 + w.1) g = extFun σ J (fun _ => v.1) g + extFun σ J (fun _ => w.1) g
    unfold extFun
    split_ifs <;> simp
  map_smul' c w := by
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    show extFun σ J (fun _ => c • w.1) g = c • extFun σ J (fun _ => w.1) g
    unfold extFun
    split_ifs <;> simp

theorem bump_mul (σ : Representation ℂ P W) {J : Subgroup G} (hJ : IsOpen (J : Set G))
    (w : fixed σ (J.subgroupOf P)) (p : P) {j : G} (hj : j ∈ J) :
    (bump σ hJ w).1.1 (p * j) = σ p w :=
  extFun_mul (φ := fun _ => w.1) (fun p hp _ _ => (mem_fixed_iff.1 w.2 p hp).symm) p hj

theorem bump_zero (σ : Representation ℂ P W) {J : Subgroup G} (hJ : IsOpen (J : Set G))
    (w : fixed σ (J.subgroupOf P)) {g : G} (h : g ∉ cell P J) : (bump σ hJ w).1.1 g = 0 :=
  extFun_zero σ (fun _ => w.1) h

theorem smInd_apply (σ : Representation ℂ P W) (f : smoothPart (ind P σ)) (g x : G) :
    (smInd P σ g f).1.1 x = f.1.1 (x * g) := rfl

theorem smInd_bump (σ : Representation ℂ P W) {J : Subgroup G} (hJ : IsOpen (J : Set G)) (q : P)
    (hq : ∀ j ∈ J, (q : G) * j * (q : G)⁻¹ ∈ J) (hq' : ∀ j ∈ J, (q : G)⁻¹ * j * q ∈ J)
    (w v : fixed σ (J.subgroupOf P)) (hv : v.1 = σ q w) : smInd P σ q (bump σ hJ w) = bump σ hJ v := by
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  rw [smInd_apply]
  rcases cell_cases (P := P) J g with h | ⟨p, j, hj, rfl⟩
  · rw [bump_zero _ _ _ h, bump_zero]
    rintro ⟨p, hp⟩
    exact h ⟨p * q⁻¹, by simpa [mul_assoc] using hq _ hp⟩
  · have : (p : G) * j * q = (p * q : P) * ((q : G)⁻¹ * j * q) := by simp [mul_assoc]
    rw [this, bump_mul _ _ _ _ (hq' j hj), bump_mul _ _ _ _ hj, hv, map_mul, Module.End.mul_apply]

theorem mem_span_bump (σ : Representation ℂ P W) {J K : Subgroup G} (hJ : IsOpen (J : Set G))
    (hK : IsCompact (K : Set G)) (hle : J ≤ K) (hn : ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x) (f : smoothPart (ind P σ))
    (hf : ∀ j ∈ J, smInd P σ j f = f) :
    f ∈ Submodule.span ℂ {v | ∃ z ∈ K, ∃ w, v = smInd P σ z⁻¹ (bump σ hJ w)} := by
  classical
  have hf' : ∀ j ∈ J, ∀ x, f.1.1 (x * j) = f.1.1 x := fun j hj x => by rw [← smInd_apply, hf j hj]
  have hK' : ∀ (p : P) (x : K), (p : G)⁻¹ * x ∈ J → (p : G) ∈ K := fun p x h => by
    simpa using mul_mem x.2 (inv_mem (hle h))
  let H : Subgroup K :=
    { carrier := {x | (x : G) ∈ cell P J}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro x y ⟨p, hp⟩ ⟨q, hq⟩
        exact ⟨p * q, by simpa [mul_assoc] using mul_mem (hn _ (inv_mem (hK' q y hq)) _ hp) hq⟩
      inv_mem' := by
        rintro x ⟨p, hp⟩
        exact ⟨p⁻¹, by simpa [mul_assoc] using hn _ (hK' p x hp) _ (inv_mem hp)⟩ }
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ H) := H.quotient_finite_of_isOpen ((isOpen_cell hJ).preimage continuous_subtype_val)
  haveI := Fintype.ofFinite (K ⧸ H)
  have hw : ∀ z : K, f.1.1 (z : G)⁻¹ ∈ fixed σ (J.subgroupOf P) := fun z => mem_fixed_iff.2 fun h hh => by
    rw [← f.1.2 h, ← hf' _ (hn z z.2 h hh) (z : G)⁻¹]
    simp [mul_assoc]
  have key : f = ∑ q : K ⧸ H, smInd P σ (q.out : G) (bump σ hJ ⟨_, hw q.out⟩) := by
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    obtain ⟨p, hp, y, hy, rfl⟩ := hPK g
    rw [f.1.2 ⟨p, hp⟩, Subtype.property (p := (· ∈ indSpace P σ)) _ ⟨p, hp⟩]
    congr 1
    simp only [Submodule.coe_sum, Finset.sum_apply, smInd_apply]
    rw [Finset.sum_eq_single (QuotientGroup.mk (⟨y, hy⟩⁻¹ : K))]
    · have h1 := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk (⟨y, hy⟩⁻¹ : K) : K ⧸ H)).symm
      generalize (QuotientGroup.mk (⟨y, hy⟩⁻¹ : K) : K ⧸ H).out = z at h1
      obtain ⟨q, hq⟩ := h1
      have h2 : y * z = q * ((q : G)⁻¹ * (y * z)) := by simp
      have hq' : (q : G)⁻¹ * (y * z) ∈ J := by simpa using hq
      rw [h2, bump_mul _ _ _ _ hq', ← f.1.2 q, ← hf' _ (hn z z.2 _ hq') (q * (z : G)⁻¹)]
      simp [mul_assoc]
    · intro q _ hq
      refine bump_zero _ _ _ fun h => hq ?_
      rw [← QuotientGroup.out_eq' q, eq_comm, QuotientGroup.eq]
      rw [inv_inv]
      exact h
    · simp
  rw [key]
  exact Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨(q.out : G)⁻¹, inv_mem q.out.2, _, by rw [inv_inv]⟩

theorem dual_ext {σ : Representation ℂ G W} (hσ : IsSmooth σ) {H : Subgroup G} (hH : IsCompact (H : Set G))
    {l l' : Module.Dual ℂ W} (hl : ∀ h ∈ H, ∀ w, l (σ h w) = l w) (hl' : ∀ h ∈ H, ∀ w, l' (σ h w) = l' w)
    (h : ∀ w ∈ fixed σ H, l w = l' w) : l = l' := by
  ext u
  obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hσ hH (l - l') u fun g hg => by
    simp [hl g hg, hl' g hg]
  simp only [LinearMap.sub_apply, h v hv, sub_self] at e
  exact sub_eq_zero.1 e.symm

variable [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G}
  (hK : IsCompact (K : Set G)) (σ : Representation ℂ P W) (τ : Representation ℂ P W')
  (B : W' →ₗ[ℂ] Module.Dual ℂ W)

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
theorem continuous_pair (f' : smoothPart (ind P τ)) (f : smoothPart (ind P σ)) :
    Continuous fun x => B (f'.1.1 x) (f.1.1 x) :=
  ((isLocallyConstant_smInd f').comp₂ (isLocallyConstant_smInd f) fun l w => B l w).continuous

def pair : smoothPart (ind P τ) →ₗ[ℂ] Module.Dual ℂ (smoothPart (ind P σ)) :=
  LinearMap.mk₂ ℂ (fun f' f => ∫ x in (K : Set G), B (f'.1.1 x) (f.1.1 x) ∂μ)
    (fun f' g' f => by
      rw [← integral_add ((continuous_pair σ τ B f' f).continuousOn.integrableOn_compact hK)
        ((continuous_pair σ τ B g' f).continuousOn.integrableOn_compact hK)]
      simp)
    (fun c f' f => by rw [← integral_smul]; simp)
    (fun f' f g => by
      rw [← integral_add ((continuous_pair σ τ B f' f).continuousOn.integrableOn_compact hK)
        ((continuous_pair σ τ B f' g).continuousOn.integrableOn_compact hK)]
      simp)
    (fun c f' f => by rw [← integral_smul]; simp)

theorem pair_apply (f' : smoothPart (ind P τ)) (f : smoothPart (ind P σ)) :
    pair μ hK σ τ B f' f = ∫ x in (K : Set G), B (f'.1.1 x) (f.1.1 x) ∂μ := rfl

theorem pair_bump (hB : ∀ p : P, (p : G) ∈ K → ∀ w' w, B (τ p w') (σ p w) = B w' w)
    {J : Subgroup G} (hJ : IsOpen (J : Set G)) (hle : J ≤ K) (f' : smoothPart (ind P τ))
    (hf : ∀ j ∈ J, f'.1.1 j = f'.1.1 1) (w : fixed σ (J.subgroupOf P)) :
    pair μ hK σ τ B f' (bump σ hJ w) = (μ.real (K ∩ cell P J) : ℂ) * B (f'.1.1 1) w := by
  rw [pair_apply, setIntegral_congr_fun hK.measurableSet
    (g := (cell P J).indicator fun _ => B (f'.1.1 1) w), setIntegral_indicator (isOpen_cell hJ).measurableSet,
    setIntegral_const, Complex.real_smul]
  intro x hx
  rcases cell_cases (P := P) J x with h | ⟨p, j, hj, rfl⟩
  · simp [bump_zero _ _ _ h, h]
  · have hp : (p : G) ∈ K := by simpa using mul_mem hx (inv_mem (hle hj))
    have hm : (p : G) * j ∈ cell P J := ⟨p, by simpa using hj⟩
    simp only [Set.indicator_of_mem hm]
    rw [bump_mul _ _ _ _ hj, f'.1.2 p j, hB p hp, hf j hj]

include hK in
theorem vol_ne_zero (hKo : IsOpen (K : Set G)) {J : Subgroup G} (hJ : IsOpen (J : Set G)) :
    (μ.real (K ∩ cell P J) : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero, Ne, measureReal_eq_zero_iff
    ((measure_mono Set.inter_subset_left).trans_lt hK.measure_lt_top).ne]
  exact ((hKo.inter (isOpen_cell hJ)).measure_pos μ ⟨1, one_mem K, 1, by simp⟩).ne'

theorem pair_bijective (hKo : IsOpen (K : Set G)) (hP : IsClosed (P : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x)
    (hbasis : ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ (J : Set G) ⊆ U ∧ J ≤ K ∧
      ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hσ : IsSmooth σ) (hB : ∀ p : P, (p : G) ∈ K → ∀ w' w, B (τ p w') (σ p w) = B w' w)
    (hBi : Function.Injective B)
    (hBs : ∀ l : Module.Dual ℂ W, (∀ᶠ p in 𝓝 (1 : P), ∀ w, l (σ p w) = l w) → l ∈ LinearMap.range B)
    (hinv : ∀ g f' f, pair μ hK σ τ B (smInd P τ g f') (smInd P σ g f) = pair μ hK σ τ B f' f) :
    Function.Injective (pair μ hK σ τ B) ∧
      ∀ l ∈ smoothPart (smInd P σ).dual, l ∈ LinearMap.range (pair μ hK σ τ B) := by
  have hinv' : ∀ g f' f, pair μ hK σ τ B f' (smInd P σ g⁻¹ f) = pair μ hK σ τ B (smInd P τ g f') f := by
    intro g f' f
    rw [← hinv g, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro f' h0
    refine Subtype.ext (Subtype.ext (funext fun g => hBi (LinearMap.ext fun w => ?_)))
    obtain ⟨U, hU, hU'⟩ := (mem_nhds_subtype _ _ _).1 ((hσ w).mem_nhds (x := 1) (by simp))
    obtain ⟨J, hJ, hJU, hle, -⟩ := hbasis _ (Filter.inter_mem hU
      (IsOpen.mem_nhds (isSmooth_smoothRep _ (smInd P τ g f')) (by simp)))
    have h1 := pair_bump μ hK σ τ B hB hJ hle (smInd P τ g f') (fun j hj => by
      have h2 : (smInd P τ g f').1.1 (1 * j) = _ := congrArg (fun φ => φ.1.1 1) (hJU hj).2
      rwa [one_mul] at h2) ⟨w, mem_fixed_iff.2 fun h hh => hU' (hJU hh).1⟩
    rw [← hinv', h0, LinearMap.zero_apply, smInd_apply, one_mul] at h1
    simpa [vol_ne_zero μ hK hKo hJ] using h1
  · intro l hl
    obtain ⟨J, hJ, hJU, hle, hn⟩ := hbasis _ (IsOpen.mem_nhds hl (by
      rw [Set.mem_ofPred_eq, map_one, Module.End.one_apply]))
    have hlJ : ∀ j ∈ J, ∀ f, l (smInd P σ j f) = l f := fun j hj f => by
      have h2 : l (smInd P σ j⁻¹⁻¹ f) = l f := LinearMap.congr_fun (hJU (inv_mem hj)) f
      rwa [inv_inv] at h2
    have hJc : IsCompact (J : Set G) := hK.of_isClosed_subset (J.isClosed_of_isOpen hJ) hle
    have hHc : IsCompact (J.subgroupOf P : Set P) := hP.isClosedEmbedding_subtypeVal.isCompact_preimage hJc
    set c : ℂ := ((μ.real (K ∩ cell P J) : ℝ) : ℂ) with hc
    have hc0 : c ≠ 0 := vol_ne_zero μ hK hKo hJ
    have hex : ∀ z : G, ∃ w' : W', (∀ h ∈ J.subgroupOf P, ∀ w, B w' (σ h w) = B w' w) ∧
        ∀ w : fixed σ (J.subgroupOf P), B w' w = c⁻¹ * l (smInd P σ z⁻¹ (bump σ hJ w)) := by
      intro z
      obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend (c⁻¹ • (l ∘ₗ smInd P σ z⁻¹ ∘ₗ bump σ hJ))
      obtain ⟨l₁, h1, h2⟩ := GlobalTheory.SmGL.DualAverage.exists_invariant_form P W σ hσ _ hHc l₀
      obtain ⟨w', rfl⟩ := hBs l₁ (Filter.mem_of_superset
        ((hJ.preimage continuous_subtype_val).mem_nhds (one_mem J)) h1)
      exact ⟨w', h1, fun w => (h2 _ (mem_fixed_iff.1 w.2)).trans (LinearMap.congr_fun hl₀ w)⟩
    choose φ hφ1 hφ2 using hex
    have hφr : ∀ i ∈ J, ∀ j ∈ K, φ (j * i) = φ j := fun i hi j _ =>
      hBi (dual_ext hσ hHc (hφ1 _) (hφ1 _) fun w hw => by
        rw [hφ2 _ ⟨w, hw⟩, hφ2 _ ⟨w, hw⟩, mul_inv_rev, map_mul, Module.End.mul_apply, hlJ _ (inv_mem hi)])
    have hφl : ∀ p : P, (p : G) ∈ K → ∀ j ∈ K, φ (p * j) = τ p (φ j) := by
      intro p hp z _
      have h1 : ∀ w, B (τ p (φ z)) w = B (φ z) (σ p⁻¹ w) := fun w => by
        rw [← hB p hp (φ z), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      have h2 : ∀ q : P, (q : G) ∈ K → ∀ h ∈ J.subgroupOf P, q * h * q⁻¹ ∈ J.subgroupOf P :=
        fun q hq h hh => hn q hq h hh
      refine hBi (dual_ext hσ hHc (hφ1 _) (fun h hh w => ?_) fun w hw => ?_)
      · rw [h1, h1, ← hφ1 z _ (h2 p⁻¹ (inv_mem hp) h hh) (σ p⁻¹ w)]
        simp only [← Module.End.mul_apply, ← map_mul]
        simp [mul_assoc]
      · have hv : σ p⁻¹ w ∈ fixed σ (J.subgroupOf P) := mem_fixed_iff.2 fun h hh => by
          conv_rhs => rw [← mem_fixed_iff.1 hw _ (h2 p hp h hh)]
          simp only [← Module.End.mul_apply, ← map_mul]
          simp [mul_assoc]
        rw [h1, hφ2 _ ⟨w, hw⟩, hφ2 _ ⟨_, hv⟩, mul_inv_rev, map_mul, Module.End.mul_apply,
          ← smInd_bump σ hJ p⁻¹ (hn _ (inv_mem hp)) (fun j hj => by simpa using hn _ hp j hj) ⟨w, hw⟩ ⟨_, hv⟩ rfl]
        rfl
    let f' := extInd τ hJ hle φ hφl hφr
    have hf1 : ∀ z ∈ K, f'.1.1 z = φ z := fun z hz => by
      show extFun τ K φ z = φ z
      simpa using extFun_mul hφl 1 hz
    have hf2 : ∀ j ∈ J, smInd P τ j f' = f' := fun j hj =>
      Subtype.ext (Subtype.ext (funext fun g => extFun_right hφl (hle hj) (hφr j hj) g))
    refine ⟨f', dual_ext (isSmooth_smoothRep _) hJc (fun j hj f => ?_) hlJ fun f hf => ?_⟩
    · conv_lhs => rw [← hf2 j hj]
      exact hinv j f' f
    · refine LinearMap.eqOn_span' ?_ (mem_span_bump σ hJ hK hle hn hPK f (mem_fixed_iff.1 hf))
      rintro _ ⟨z, hz, w, rfl⟩
      rw [hinv', pair_bump μ hK σ τ B hB hJ hle, smInd_apply, one_mul, hf1 z hz, hφ2, mul_inv_cancel_left₀ hc0]
      intro j hj
      rw [smInd_apply, smInd_apply, one_mul, hf1 z hz, hf1 _ (mul_mem (hle hj) hz),
        ← hφr _ (hn _ (inv_mem hz) j hj) z hz]
      simp [mul_assoc]

theorem exists_equiv
    (hinv : ∀ g f' f, pair μ hK σ τ B (smInd P τ g f') (smInd P σ g f) = pair μ hK σ τ B f' f)
    (hi : Function.Injective (pair μ hK σ τ B))
    (hs : ∀ l ∈ smoothPart (smInd P σ).dual, l ∈ LinearMap.range (pair μ hK σ τ B)) :
    ∃ Φ : (smInd P τ).Equiv (contra (smInd P σ)), ∀ f' f,
      (Φ f' : Module.Dual ℂ (smoothPart (ind P σ))) f = ∫ x in (K : Set G), B (f'.1.1 x) (f.1.1 x) ∂μ := by
  have hact : ∀ g f', pair μ hK σ τ B (smInd P τ g f') =
      (smInd P σ).dual g (pair μ hK σ τ B f') := fun g f' => LinearMap.ext fun f => by
    show _ = pair μ hK σ τ B f' (smInd P σ g⁻¹ f)
    rw [← hinv g f', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hsm : ∀ f', pair μ hK σ τ B f' ∈ smoothPart (smInd P σ).dual := fun f' =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      (IsOpen.mem_nhds (isSmooth_smoothRep _ f') (by
        rw [Set.mem_ofPred_eq, map_one, Module.End.one_apply])) fun g hg => by
        have hg' : smInd P τ g f' = f' := hg
        rw [Set.mem_ofPred_eq, ← hact, hg'])
  refine ⟨.mk (LinearEquiv.ofBijective ((pair μ hK σ τ B).codRestrict _ hsm)
    ⟨fun a b h => hi (congrArg Subtype.val h), fun l => ?_⟩) fun g => ?_, fun f' f => rfl⟩
  · obtain ⟨f', hf'⟩ := hs l.1 l.2
    exact ⟨f', Subtype.ext hf'⟩
  · exact LinearMap.ext fun f' => Subtype.ext (hact g f')

end Abstract

theorem inductionContragredient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionContragredient k := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e _ _ μ _ W _ _ ρ hρ
  obtain ⟨-, hK1, hK2, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  let σ : Representation ℂ (parab k e) W := (twist ρ (deltaHalf k m)).comp (leviProj k e)
  let τ : Representation ℂ (parab k e) (smoothPart ρ.dual) :=
    (twist (contra ρ) (deltaHalf k m)).comp (leviProj k e)
  let B : smoothPart ρ.dual →ₗ[ℂ] Module.Dual ℂ W := Submodule.subtype _
  have hσ : IsSmooth σ := isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont
  have hB : ∀ p w' w, B (τ p w') (σ p w) = (modulus k m (leviProj k e p) : ℂ) * B w' w := by
    intro p w' w
    show ((deltaHalf k m (leviProj k e p) : ℂ) • (contra ρ (leviProj k e p) w' : Module.Dual ℂ W))
      ((deltaHalf k m (leviProj k e p) : ℂ) • ρ (leviProj k e p) w) = _ * (w' : Module.Dual ℂ W) w
    rw [LinearMap.smul_apply, map_smul, contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply, smul_smul, val_deltaHalf, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (modulus_pos k _).le, smul_eq_mul]
  have hinv : ∀ g f' f, pair μ SplitFlip.isCompact_KO σ τ B (smInd _ τ g f') (smInd _ σ g f) =
      pair μ SplitFlip.isCompact_KO σ τ B f' f := fun g f' f =>
    GlobalTheory.SmGL.IndDual.integral_KO_mul_right k α n m e μ _ (continuous_pair σ τ B f' f)
      (fun p x => by rw [f'.1.2 p x, f.1.2 p x, hB]) g
  obtain ⟨hi, hs⟩ := pair_bijective μ SplitFlip.isCompact_KO σ τ B SplitFlip.isOpen_KO hP hPK
    (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k n) hσ (fun p hp w' w => by rw [hB, hK2 _ (hK1 p hp)]; simp) Subtype.val_injective
    (fun l hl => by
      rw [Submodule.range_subtype]
      have hc : Continuous fun g : Levi k m => (⟨leviEmb k e g⁻¹, leviEmb_mem_parab k e _⟩ : parab k e) :=
        ((continuous_leviEmb k e).comp continuous_inv).subtype_mk _
      refine mem_smoothPart_of_nhds ?_
      filter_upwards [(hc.tendsto' 1 1 (by simp)).eventually hl,
        IsOpen.mem_nhds (isSmoothChar_deltaHalf k (m := m)) (one_mem _)] with g h1 h2
      refine LinearMap.ext fun w => Eq.trans ?_ (h1 w)
      have h3 : deltaHalf k m g⁻¹ = 1 := inv_mem h2
      show l (ρ g⁻¹ w) = l (twist ρ (deltaHalf k m) (leviProj k e _) w)
      rw [leviProj_leviEmb, twist_apply, h3, Units.val_one, one_smul]) hinv
  exact exists_equiv μ SplitFlip.isCompact_KO σ τ B hinv hi hs

end GlobalTheory.SmGL.IndDual
