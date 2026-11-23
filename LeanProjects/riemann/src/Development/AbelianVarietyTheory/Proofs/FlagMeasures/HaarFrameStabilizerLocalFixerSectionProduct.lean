import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Closed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousUnitriangularSectionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFlagDualBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilpotentOfStrict
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.HaarSectionProd

def prodHomeo {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace U]
    {S0 S : Subgroup G} (hS0S : S0 ≤ S) (t0 : U → G) (ht0c : Continuous t0) (ht0S : ∀ x, t0 x ∈ S)
    (ν : S → U) (hνc : Continuous ν)
    (hνt : ∀ s : S, ∀ s0 ∈ S0, ∀ x, (s : G) = s0 * t0 x → ν s = x)
    (hsec : ∀ s : S, (s : G) * (t0 (ν s))⁻¹ ∈ S0) : S0 × U ≃ₜ S where
  toFun p := ⟨p.1 * t0 p.2, S.mul_mem (hS0S p.1.2) (ht0S p.2)⟩
  invFun s := (⟨s * (t0 (ν s))⁻¹, hsec s⟩, ν s)
  left_inv p := by
    have h : ν ⟨p.1 * t0 p.2, S.mul_mem (hS0S p.1.2) (ht0S p.2)⟩ = p.2 :=
      hνt _ p.1 p.1.2 p.2 rfl
    ext
    · simp only [h, mul_inv_cancel_right]
    · simp only [h]
  right_inv s := by
    ext
    simp only [inv_mul_cancel_right]
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_fst).mul (ht0c.comp continuous_snd)).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.mul ((ht0c.comp hνc).inv)).subtype_mk _).prodMk hνc

end GlobalTheory.HaarSectionProd

namespace GlobalTheory.HaarSectionProd

theorem haar_exists {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace G]
    [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U] [SecondCountableTopology U]
    {S0 S : Subgroup G} (hS0cl : IsClosed (S0 : Set G)) (hS0S : S0 ≤ S) (t0 : U → G)
    (ht0c : Continuous t0) (ht0S : ∀ x, t0 x ∈ S) (ν : S → U) (hνc : Continuous ν)
    (hνt : ∀ s : S, ∀ s0 ∈ S0, ∀ x, (s : G) = s0 * t0 x → ν s = x)
    (hsec : ∀ s : S, (s : G) * (t0 (ν s))⁻¹ ∈ S0)
    (μ0 : Measure S0) [μ0.IsHaarMeasure]
    (hconj : ∀ s ∈ S, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ h, f (s * (h : G) * s⁻¹) ∂μ0 = ∫⁻ h, f (h : G) ∂μ0)
    (μU : Measure U) [SigmaFinite μU] [μU.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μU]
    (hshift : ∀ s ∈ S, ∃ φ : U → U, Measurable φ ∧ μU.map φ = μU ∧
      ∀ x, s * t0 x * (t0 (φ x))⁻¹ ∈ S0) :
    ∃ μS : Measure S, μS.IsHaarMeasure ∧ ∀ h : G → ℝ≥0∞, Measurable h → ∀ t : U → G,
      (∀ x, t x * (t0 x)⁻¹ ∈ S0) →
      ∫⁻ s, h s ∂(μS.map Subtype.val) = ∫⁻ x, ∫⁻ s0, h ((s0 : G) * t x) ∂μ0 ∂μU := by
  haveI : LocallyCompactSpace S0 := hS0cl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology S0 := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace S0 := inferInstance
  haveI : SigmaFinite μ0 := inferInstance
  set e := prodHomeo hS0S t0 ht0c ht0S ν hνc hνt hsec with he
  have he_m : Measurable e := e.continuous.measurable
  set μS : Measure S := (μ0.prod μU).map e with hμS
  have hright : ∀ c ∈ S0, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ s0, f ((s0 : G) * c) ∂μ0 = ∫⁻ s0, f (s0 : G) ∂μ0 := by
    intro c hc f hf
    have h1 := hconj c⁻¹ (S.inv_mem (hS0S hc)) (fun y => f (c * y)) (hf.comp (measurable_const_mul c))
    simp only [inv_inv, mul_assoc, mul_inv_cancel_left] at h1
    rw [h1]
    exact lintegral_mul_left_eq_self (fun h : S0 => f (h : G)) ⟨c, hc⟩
  have hkey : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ s, f s ∂(μS.map Subtype.val) = ∫⁻ x, ∫⁻ s0, f ((s0 : G) * t0 x) ∂μ0 ∂μU := by
    intro f hf
    have hfv : Measurable (fun k : S => f (k : G)) := hf.comp measurable_subtype_coe
    rw [lintegral_map hf measurable_subtype_coe, hμS, lintegral_map hfv he_m,
      lintegral_prod_symm (fun p => f (e p : G)) (hfv.comp he_m).aemeasurable]
    rfl
  have hleft : ∀ g ∈ S, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, ∫⁻ s0, f (g * ((s0 : G) * t0 x)) ∂μ0 ∂μU = ∫⁻ x, ∫⁻ s0, f ((s0 : G) * t0 x) ∂μ0 ∂μU := by
    intro g hg f hf
    obtain ⟨φ, hφm, hφ, hφS⟩ := hshift g hg
    have hGm : Measurable (fun y => ∫⁻ s0, f ((s0 : G) * t0 y) ∂μ0) := by
      have : Measurable (fun p : S0 × U => f ((p.1 : G) * t0 p.2)) :=
        hf.comp ((continuous_subtype_val.comp continuous_fst).mul (ht0c.comp continuous_snd)).measurable
      exact this.lintegral_prod_left'
    have hin : ∀ x, ∫⁻ s0, f (g * ((s0 : G) * t0 x)) ∂μ0 = ∫⁻ s0, f ((s0 : G) * t0 (φ x)) ∂μ0 := by
      intro x
      set c := g * t0 x * (t0 (φ x))⁻¹ with hcdef
      have hc : c ∈ S0 := hφS x
      have e1 : ∀ s0 : G, g * (s0 * t0 x) = g * s0 * g⁻¹ * (c * t0 (φ x)) := by
        intro s0; rw [hcdef]; group
      simp_rw [e1]
      have h2 := hconj g hg (fun y => f (y * (c * t0 (φ x)))) (hf.comp (measurable_mul_const _))
      rw [h2]
      have h3 := hright c hc (fun y => f (y * t0 (φ x))) (hf.comp (measurable_mul_const _))
      simpa only [mul_assoc] using h3
    simp_rw [hin]
    rw [← lintegral_map hGm hφm, hφ]
  have hinv : μS.IsMulLeftInvariant := by
    refine ⟨fun k0 => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_mul k0) hA]
    obtain ⟨B, hB, rfl⟩ := hA
    have hB' : MeasurableSet ((fun y : G => (k0 : G) * y) ⁻¹' B) := measurable_const_mul _ hB
    have e1 : μS ((fun k => k0 * k) ⁻¹' (Subtype.val ⁻¹' B)) =
        (μS.map Subtype.val) ((fun y : G => (k0 : G) * y) ⁻¹' B) := by
      rw [Measure.map_apply measurable_subtype_coe hB']; rfl
    have e2 : μS (Subtype.val ⁻¹' B) = (μS.map Subtype.val) B := by
      rw [Measure.map_apply measurable_subtype_coe hB]
    rw [e1, e2, ← lintegral_indicator_one hB', ← lintegral_indicator_one hB,
      hkey _ (measurable_one.indicator hB'), hkey _ (measurable_one.indicator hB)]
    have hz : ∀ z, ((fun y : G => (k0 : G) * y) ⁻¹' B).indicator (1 : G → ℝ≥0∞) z =
        B.indicator 1 ((k0 : G) * z) := fun z => by
      by_cases hz : (k0 : G) * z ∈ B <;> simp [Set.indicator, hz]
    simp_rw [hz]
    exact hleft k0 k0.2 _ (measurable_one.indicator hB)
  have hfin : IsFiniteMeasureOnCompacts μS := Measure.IsFiniteMeasureOnCompacts.map _ e
  have hopen : μS.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  have hHaar : μS.IsHaarMeasure := by
    haveI := hfin; haveI := hinv; haveI := hopen
    exact ⟨⟩
  refine ⟨μS, hHaar, ?_⟩
  intro h hh t ht
  rw [hkey h hh]
  congr 1
  funext x
  have h4 := hright _ (ht x) (fun y => h (y * t0 x)) (hh.comp (measurable_mul_const _))
  simp only [mul_assoc, inv_mul_cancel, mul_one] at h4
  exact h4.symm

end GlobalTheory.HaarSectionProd

namespace GlobalTheory.HaarSectionProd

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

def umat {K : Type} [Zero K] [One K] (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → K) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0

def UTri {K : Type} [Zero K] [One K] (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : Prop :=
  (∀ i, A i i = 1) ∧ ∀ i j, j < i → A i j = 0

theorem umat_utri {K : Type} [Zero K] [One K] (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → K) :
    UTri (umat x) := by
  refine ⟨fun i => by simp [umat], fun i j h => ?_⟩
  simp [umat, h.ne', not_lt.mpr h.le]

theorem utri_mul {K : Type} [CommRing K] {A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hA : UTri A) (hB : UTri B) : UTri (A * B) := by
  refine ⟨fun i => ?_, fun i j hji => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [hA.1, hB.1]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · simp [hA.2 _ _ h]
      · simp [hB.2 _ _ h]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : c < i
    · simp [hA.2 _ _ h]
    · simp [hB.2 _ _ (lt_of_lt_of_le hji (not_lt.mp h))]

theorem umat_of_utri {K : Type} [Zero K] [One K] {A : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hA : UTri A) : umat (fun p : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} => A p.1.1 p.1.2) = A := by
  ext a b
  simp only [umat, Matrix.of_apply]
  split_ifs with h1 h2
  · subst h1; exact (hA.1 a).symm
  · rfl
  · exact (hA.2 a b (lt_of_le_of_ne (not_lt.mp h2) (fun e => h1 e.symm))).symm

variable (P : Frame E n r)

def Coef (g : HA R σ J) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) (R ⊗[F] E)) : Prop :=
  ∀ b, lin R σ J g (ratV (F := F) R (F0 P b)) = ∑ a, A a b • ratV (F := F) R (F0 P a)

variable {P}

theorem coef_mul {g k : HA R σ J} {A B : Matrix (Fin (r + 1)) (Fin (r + 1)) (R ⊗[F] E)}
    (hg : Coef P g A) (hk : Coef P k B) : Coef P (g * k) (A * B) := by
  have hg' : ∀ a, lin R σ J g (ratV (F := F) R (F0 P a)) = ∑ c, A c a • ratV (F := F) R (F0 P c) := hg
  intro b
  rw [lin_mul, hk b, map_sum]
  simp only [map_smul, hg', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

theorem coef_one_of_mem {g : HA R σ J} (hg : g ∈ S0 R σ J P) : Coef P g 1 := by
  intro b
  rw [(mem_stabT R σ J (F0 P) g).1 hg b]
  simp [Matrix.one_apply]

theorem frameFixerSubgroup_le_frameStabilizerSubgroup : S0 R σ J P ≤ Ssub R σ J P := by
  intro g hg
  show UniC R σ J (F0 P) g
  intro b
  rw [(mem_stabT R σ J (F0 P) g).1 hg b, sub_self]
  exact Submodule.zero_mem _

theorem mem_Ssub_of_coef {g : HA R σ J} {x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E}
    (hg : Coef P g (umat x)) : g ∈ Ssub R σ J P := by
  show UniC R σ J (F0 P) g
  intro b
  rw [hg b]
  have hb : ratV (F := F) R (F0 P b) = ∑ a, (if a = b then ratV (F := F) R (F0 P a) else 0) := by
    simp
  rw [hb, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun a _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · simp only [umat, Matrix.of_apply, h.ne, if_false, dif_pos h, sub_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, h, rfl⟩)
  · subst h; simp [umat]
  · simp [umat, h.ne', not_lt.mpr h.le]

theorem mul_inv_mem_frameFixer_of_agree_on_frame {g k : HA R σ J} (hk : k ∈ Ssub R σ J P)
    (h : ∀ b, lin R σ J g (ratV (F := F) R (F0 P b)) = lin R σ J k (ratV (F := F) R (F0 P b))) :
    g * k⁻¹ ∈ S0 R σ J P := by
  show g * k⁻¹ ∈ stabT R σ J (F0 P)
  rw [mem_stabT]
  have hgw : ∀ w ∈ spanR (F := F) R (F0 P) Set.univ, lin R σ J g w = lin R σ J k w := by
    intro w hw
    unfold spanR at hw
    induction hw using Submodule.span_induction with
    | mem y hy => obtain ⟨a, _, rfl⟩ := hy; exact h a
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, map_smul, hx]
  intro b
  obtain ⟨w, hw, hwk⟩ := uni_le_map (Y := F0 P) (g := k) hk Set.univ (fun _ _ _ _ => Set.mem_univ _)
    (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩)
  have hwk' : lin R σ J k w = ratV (F := F) R (F0 P b) := hwk
  rw [lin_mul, ← hwk', lin_inv_lin, hgw w hw]

theorem coef_agree {g k : HA R σ J} {A : Matrix (Fin (r + 1)) (Fin (r + 1)) (R ⊗[F] E)}
    (hg : Coef P g A) (hk : Coef P k A) (hkS : k ∈ Ssub R σ J P) : g * k⁻¹ ∈ S0 R σ J P :=
  mul_inv_mem_frameFixer_of_agree_on_frame hkS fun b => by rw [hg b, hk b]

end Alg

end GlobalTheory.HaarSectionProd

namespace GlobalTheory.HaarSectionProd

theorem umat_entry_continuous {K : Type} [TopologicalSpace K] [Zero K] [One K] {r : ℕ} (a b : Fin (r + 1)) :
    Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → K => umat x a b := by
  simp only [umat, Matrix.of_apply]
  split_ifs
  · exact continuous_const
  · exact continuous_apply _
  · exact continuous_const

theorem haar_S_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure → (∀ s ∈ Ssub (Fv F v) σ J P, ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∫⁻ h, f (s * (h : HA (Fv F v) σ J) * s⁻¹) ∂μ0 = ∫⁻ h, f (h : HA (Fv F v) σ J) ∂μ0) → ∀ μU : Measure ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), μU.IsAddHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ ∀ h : HA (Fv F v) σ J → ℝ≥0∞, Measurable h → ∀ t : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a)) → ∫⁻ s, h s ∂(amb μS) = ∫⁻ x, ∫⁻ s0, h ((s0 : HA (Fv F v) σ J) * t x) ∂μ0 ∂μU := by
  intro F E _ _ _ _ _ σ hCM n J hJ v r P T hP μ0 hμ0 hconj μU hμU
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, -⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5; haveI := i6; haveI := i7; haveI := i8
  haveI : BorelSpace (HA (Fv F v) σ J) := ⟨rfl⟩
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨t0, ht0c, ht0⟩ := GlobalTheory.T.exists_continuous_unitriangular_section F E σ hCM n J hJ v r P T hP
  obtain ⟨ν, hνc, hν⟩ := GlobalTheory.UnitriangularCoeff.exists_coeff F E σ hCM n J hJ v r P T hP
  have ht0coef : ∀ x, Coef P (t0 x) (umat x) := ht0
  have hνcoef : ∀ s : Ssub (Fv F v) σ J P, Coef P (s : HA (Fv F v) σ J) (umat (ν s)) :=
    fun s => (hν s (ν s)).1 rfl
  have ht0S : ∀ x, t0 x ∈ Ssub (Fv F v) σ J P := fun x => mem_Ssub_of_coef (ht0coef x)
  have hS0cl : IsClosed (S0 (Fv F v) σ J P : Set (HA (Fv F v) σ J)) :=
    PI.VolSemiDirect.W.isClosed_stabT (Fv F v) σ J (F0 P)
  have hνt : ∀ s : Ssub (Fv F v) σ J P, ∀ s0 ∈ S0 (Fv F v) σ J P, ∀ x,
      (s : HA (Fv F v) σ J) = s0 * t0 x → ν s = x := by
    intro s s0 hs0 x hs
    have hc : Coef P (s : HA (Fv F v) σ J) (umat x) := by
      rw [hs]
      have := coef_mul (coef_one_of_mem hs0) (ht0coef x)
      rwa [Matrix.one_mul] at this
    exact ((hν s x).2 hc).symm
  have hsec : ∀ s : Ssub (Fv F v) σ J P, (s : HA (Fv F v) σ J) * (t0 (ν s))⁻¹ ∈ S0 (Fv F v) σ J P :=
    fun s => coef_agree (hνcoef s) (ht0coef (ν s)) (ht0S _)
  have hshift : ∀ s ∈ Ssub (Fv F v) σ J P, ∃ φ : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) →
      ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), Measurable φ ∧ μU.map φ = μU ∧
      ∀ x, s * t0 x * (t0 (φ x))⁻¹ ∈ S0 (Fv F v) σ J P := by
    intro s hs
    set u := umat (ν ⟨s, hs⟩) with hu
    have hφc : Continuous (fun (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E)
        (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}) => (u * umat x) p.1.1 p.1.2) := by
      refine continuous_pi fun p => ?_
      simp only [Matrix.mul_apply]
      exact continuous_finset_sum _ fun c _ => continuous_const.mul (umat_entry_continuous c p.1.2)
    refine ⟨_, hφc.measurable, GlobalTheory.UnitriHaar.map_unitri_mul F E v r μU hμU u (umat_utri _).1 (umat_utri _).2, ?_⟩
    intro x
    have h1 : Coef P (s * t0 x) (u * umat x) := coef_mul (hνcoef ⟨s, hs⟩) (ht0coef x)
    rw [← umat_of_utri (utri_mul (umat_utri (ν ⟨s, hs⟩)) (umat_utri x))] at h1
    exact coef_agree h1 (ht0coef _) (ht0S _)
  obtain ⟨μS, hH, hF⟩ := haar_exists hS0cl frameFixerSubgroup_le_frameStabilizerSubgroup t0 ht0c ht0S ν hνc hνt hsec μ0 hconj μU hshift
  exact ⟨μS, hH, fun h hh t ht => hF h hh t fun x => coef_agree (ht x) (ht0coef x) (ht0S x)⟩

end GlobalTheory.HaarSectionProd
