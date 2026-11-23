import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.UnitaryLocalMassIdentity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.ContinuousHRRight

noncomputable section

namespace PI.LocMassTypM

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol MeasureTheory NumberField IsDedekindDomain
  Topology Filter
open scoped TensorProduct
open PI.LocMassTypW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Inst

variable (v : HeightOneSpectrum (𝓞 F))

theorem t2Space_fv : T2Space (Fv F v) := inferInstance

theorem t2Space_fv_tensorProduct : T2Space (Fv F v ⊗[F] E) := by
  haveI := t2Space_fv (F := F) v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact LocMassOrdSF.t2_tensor_product (F := F) (E := E) (R := Fv F v)

theorem sc_tensV : SecondCountableTopology (Fv F v ⊗[F] E) := by
  haveI := LocMassOrdSF.secondCountable_Fv (F := F) (v := v)
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact LocMassOrdSF.sc_tens (F := F) (E := E) (R := Fv F v)

theorem lc_tensV : LocallyCompactSpace (Fv F v ⊗[F] E) := by
  haveI := t2Space_fv (F := F) v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := LocMassOrdSF.locallyCompact_Fv (F := F) (v := v)
  exact LocMassOrdSF.lc_tens (F := F) (E := E) (R := Fv F v)

theorem borel_tensV : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩

end Inst

attribute [local instance] t2Space_fv_tensorProduct sc_tensV lc_tensV borel_tensV

section HATop

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem continuous_sigR : Continuous (sigR (Fv F v) σ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := LocMassOrdSF.isModTop_tens (F := F) (E := E) (R := Fv F v)
  let f : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
    TensorProduct.AlgebraTensorModule.map LinearMap.id σ.toLinearMap
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have heq : (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) = f := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [f, sigR]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [heq]
  exact hf

theorem isClosed_HR : IsClosed (HR (Fv F v) σ J : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  have hv : Continuous fun g : GL (Fin n) (Fv F v ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    Units.continuous_val
  have hm : Continuous fun g : GL (Fin n) (Fv F v ⊗[F] E) =>
      Formalism.UG.cT (sigR (Fv F v) σ) (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := by
    unfold Formalism.UG.cT
    exact (hv.matrix_map (continuous_sigR σ v)).matrix_transpose
  exact isClosed_eq ((hm.matrix_mul continuous_const).matrix_mul hv) continuous_const

theorem lc_HA : LocallyCompactSpace (HA (Fv F v) σ J) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    (inferInstance : LocallyCompactSpace (Fin n → Fin n → Fv F v ⊗[F] E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))).symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (Fv F v ⊗[F] E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact (isClosed_HR σ J v).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem sc_HA : SecondCountableTopology (HA (Fv F v) σ J) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    (inferInstance : SecondCountableTopology (Fin n → Fin n → Fv F v ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))).symm.isInducing.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (Fv F v ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  exact (isClosed_HR σ J v).isClosedEmbedding_subtypeVal.isInducing.secondCountableTopology

theorem continuous_smulTup {a : ℕ} (X : TupV (E := E) v n a) :
    Continuous (fun c : HA (Fv F v) σ J => c • X) := by
  refine continuous_pi fun i => ?_
  exact LocMassOrdKv.continuous_act (σ := σ) (J := J) (v := v) (X i)

theorem measurableSet_image_closed {a : ℕ} {C : Set (HA (Fv F v) σ J)} (hC : IsClosed C)
    (X : TupV (E := E) v n a) : MeasurableSet ((fun c : HA (Fv F v) σ J => c • X) '' C) := by
  haveI := lc_HA σ J v
  haveI := sc_HA σ J v
  obtain ⟨K, hK, hKU⟩ := IsSigmaCompact.image (continuous_smulTup σ J v X)
    (isSigmaCompact_univ.of_isClosed_subset hC (Set.subset_univ _))
  rw [← hKU]
  exact MeasurableSet.iUnion fun i => (hK i).measurableSet

end HATop

section Lat

variable {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem sc_one : sc (E := E) v 1 = 1 := rfl

theorem mem_gLat_iff {x : Fv F v} (hx : x ≠ 0) (w : Fin n → Fv F v ⊗[F] E) :
    (∃ y ∈ latLoc (E := E) v Λ, w = sc (E := E) v x • y) ↔
      sc (E := E) v x⁻¹ • w ∈ latLoc (E := E) v Λ := by
  have h1 : sc (E := E) v x⁻¹ * sc (E := E) v x = 1 := by
    unfold sc
    rw [Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hx, one_mul]
    rfl
  have h2 : sc (E := E) v x * sc (E := E) v x⁻¹ = 1 := by
    rw [mul_comm, h1]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [smul_smul, h1, one_smul]
  · intro hw
    exact ⟨_, hw, by rw [smul_smul, h2, one_smul]⟩

theorem continuous_locF {r : ℕ} (a : Fin (r + 1)) :
    Continuous (fun X : TupV (E := E) v n (r + 1) => locF v X a) := by
  unfold locF
  exact (continuous_const : Continuous fun _ : TupV (E := E) v n (r + 1) => sc (E := E) v (alp v r a)).smul
    (continuous_apply a : Continuous fun X : TupV (E := E) v n (r + 1) => X a)

theorem v_natCast_lt_one {g : ℕ} (hgv : (g : 𝓞 F) ∈ v.asIdeal) : Valued.v (g : Fv F v) < 1 := by
  have h := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (g : 𝓞 F)
  have h2 := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (g : 𝓞 F)).mpr hgv
  rw [← h] at h2
  convert h2 using 2
  simp

theorem eventually_pow_smul_mem {g : ℕ} (hgv : (g : 𝓞 F) ∈ v.asIdeal) {a : ℕ}
    (c : Fin a → Fv F v ⊗[F] E) : ∃ N : ℕ, ∀ i, (g : Fv F v) ^ N • c i ∈ OEv (E := E) v := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := LocMassOrdSF.isModTop_tens (F := F) (E := E) (R := Fv F v)
  have ht := Valued.tendsto_zero_pow_of_v_lt_one (v_natCast_lt_one v hgv)
  have hev : ∀ i, ∀ᶠ N in atTop, (g : Fv F v) ^ N • c i ∈ OEv (E := E) v := fun i => by
    have h2 : Tendsto (fun N : ℕ => (g : Fv F v) ^ N • c i) atTop (𝓝 ((0 : Fv F v) • c i)) :=
      ht.smul_const (c i)
    rw [zero_smul] at h2
    exact h2 ((PI.LocMassTypU.isOpen_oev (E := E) (v := v)).mem_nhds (PI.LocMassTypU.oev_zero (E := E) (v := v)))
  exact (Filter.eventually_all.mpr hev).exists

def P2 (a : ℕ) : Set (Fin a → Fin n → Fv F v ⊗[F] E) :=
  {X | ∀ c : Fin a → Fv F v ⊗[F] E, (∑ i, c i • X i) ∈ latLoc (E := E) v Λ →
    ∀ i, c i ∈ OEv (E := E) v}

def Sg (g a : ℕ) : Set (Fin a → Fv F v ⊗[F] E) :=
  (Set.univ.pi fun _ => (fun x : Fv F v ⊗[F] E => (g : Fv F v) • x) ⁻¹' OEv (E := E) v) ∩
    {c | ∃ i, c i ∉ OEv (E := E) v}

theorem compl_congruence_tuples {g : ℕ} (hgv : (g : 𝓞 F) ∈ v.asIdeal) (a : ℕ) :
    (P2 v Λ a)ᶜ = {X | ∃ c ∈ Sg (E := E) v g a, (∑ i, c i • X i) ∈ latLoc (E := E) v Λ} := by
  classical
  ext X
  constructor
  · intro hX
    simp only [Set.mem_compl_iff, P2, Set.mem_setOf_eq, not_forall, exists_prop] at hX
    obtain ⟨c, hs, i0, hi0⟩ := hX
    have hex : ∃ N : ℕ, ∀ i, (g : Fv F v) ^ N • c i ∈ OEv (E := E) v := eventually_pow_smul_mem v hgv c
    have hN := Nat.find_spec hex
    have hmin : ∀ m < Nat.find hex, ¬ ∀ i, (g : Fv F v) ^ m • c i ∈ OEv (E := E) v :=
      fun m hm => Nat.find_min hex hm
    have hN0 : Nat.find hex ≠ 0 := by
      intro h0
      apply hi0
      have := hN i0
      rwa [h0, pow_zero, one_smul] at this
    have hint : (g : Fv F v) ^ (Nat.find hex - 1) ∈ v.adicCompletionIntegers F :=
      pow_mem (natCast_mem (v.adicCompletionIntegers F) g) _
    refine ⟨fun i => (g : Fv F v) ^ (Nat.find hex - 1) • c i, ⟨fun i _ => ?_, ?_⟩, ?_⟩
    · show (g : Fv F v) • ((g : Fv F v) ^ (Nat.find hex - 1) • c i) ∈ OEv (E := E) v
      rw [smul_smul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hN0)]
      exact hN i
    · by_contra h
      apply hmin (Nat.find hex - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hN0) one_pos)
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    · show (∑ i, ((g : Fv F v) ^ (Nat.find hex - 1) • c i) • X i) ∈ latLoc (E := E) v Λ
      simp_rw [smul_assoc, ← Finset.smul_sum]
      exact (latLoc (E := E) v Λ).smul_mem (⟨_, hint⟩ : v.adicCompletionIntegers F) hs
  · rintro ⟨c, ⟨-, ⟨i, hi⟩⟩, hs⟩ hP
    exact hi (hP c hs i)

theorem isCompact_Sg {g : ℕ} (hg : g.Prime) (a : ℕ) : IsCompact (Sg (E := E) v g a) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := LocMassOrdSF.isModTop_tens (F := F) (E := E) (R := Fv F v)
  have hg0 : (g : Fv F v) ≠ 0 := by
    rw [← map_natCast (algebraMap F (Fv F v)) g]
    exact (map_ne_zero _).mpr (by exact_mod_cast hg.ne_zero)
  have h1 : IsCompact ((fun x : Fv F v ⊗[F] E => (g : Fv F v) • x) ⁻¹' OEv (E := E) v) :=
    (Homeomorph.isCompact_preimage (Homeomorph.smulOfNeZero (g : Fv F v) hg0)).mpr
      (LocMassOrdKv.isCompact_oev (v := v))
  have h2 : IsClosed {c : Fin a → Fv F v ⊗[F] E | ∃ i, c i ∉ OEv (E := E) v} := by
    have heq : {c : Fin a → Fv F v ⊗[F] E | ∃ i, c i ∉ OEv (E := E) v} =
        ⋃ i, (fun c : Fin a → Fv F v ⊗[F] E => c i) ⁻¹' (OEv (E := E) v)ᶜ := by
      ext c
      simp
    rw [heq]
    exact isClosed_iUnion_of_finite fun i =>
      (PI.LocMassTypU.isOpen_oev (v := v)).isClosed_compl.preimage (continuous_apply i)
  exact (isCompact_univ_pi fun _ => h1).inter_right h2

theorem isOpen_congruence_tuples (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hSD : IsSDLoc σ J v Λ)
    {g : ℕ} (hg : g.Prime) (hgv : (g : 𝓞 F) ∈ v.asIdeal) (a : ℕ) : IsOpen (P2 v Λ a) := by
  haveI : CompactSpace (Sg (E := E) v g a) := isCompact_iff_compactSpace.mp (isCompact_Sg v hg a)
  have hC : IsClosed {p : Sg (E := E) v g a × (Fin a → Fin n → Fv F v ⊗[F] E) |
      (∑ i, (p.1 : Fin a → Fv F v ⊗[F] E) i • p.2 i) ∈ latLoc (E := E) v Λ} := by
    refine (LocMassOrdKv.isClosed_latLoc (σ := σ) (J := J) (v := v) Λ hSD).preimage ?_
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
        ((continuous_apply i).comp continuous_snd)
  have himg : (P2 v Λ a)ᶜ = Prod.snd '' {p : Sg (E := E) v g a × (Fin a → Fin n → Fv F v ⊗[F] E) |
      (∑ i, (p.1 : Fin a → Fv F v ⊗[F] E) i • p.2 i) ∈ latLoc (E := E) v Λ} := by
    rw [compl_congruence_tuples v Λ hgv a]
    ext X
    constructor
    · rintro ⟨c, hc, hs⟩
      exact ⟨(⟨c, hc⟩, X), hs, rfl⟩
    · rintro ⟨⟨c, X'⟩, hs, rfl⟩
      exact ⟨c.1, c.2, hs⟩
  rw [← isClosed_compl_iff, himg]
  exact isClosedMap_snd_of_compactSpace _ hC

theorem isClosed_lattice_tuples (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hSD : IsSDLoc σ J v Λ) (a : ℕ) :
    IsClosed {X : Fin a → Fin n → Fv F v ⊗[F] E | ∀ i, X i ∈ latLoc (E := E) v Λ} := by
  have heq : {X : Fin a → Fin n → Fv F v ⊗[F] E | ∀ i, X i ∈ latLoc (E := E) v Λ} =
      ⋂ i, (fun X : Fin a → Fin n → Fv F v ⊗[F] E => X i) ⁻¹'
        (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext X
    simp
  rw [heq]
  exact isClosed_iInter fun i =>
    (LocMassOrdKv.isClosed_latLoc (σ := σ) (J := J) (v := v) Λ hSD).preimage (continuous_apply i)

theorem isPrim_eq (a : ℕ) :
    {X : Fin a → Fin n → Fv F v ⊗[F] E | IsPrim v Λ X} =
      {X | ∀ i, X i ∈ latLoc (E := E) v Λ} ∩ P2 v Λ a := rfl

theorem measurableSet_prim (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hSD : IsSDLoc σ J v Λ)
    {g : ℕ} (hg : g.Prime) (hgv : (g : 𝓞 F) ∈ v.asIdeal) (a : ℕ) :
    MeasurableSet {X : Fin a → Fin n → Fv F v ⊗[F] E | IsPrim v Λ X} := by
  rw [isPrim_eq]
  exact (isClosed_lattice_tuples v Λ σ J hSD a).measurableSet.inter (isOpen_congruence_tuples v Λ σ J hSD hg hgv a).measurableSet

theorem isClosed_cong (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hSD : IsSDLoc σ J v Λ)
    {g : ℕ} (hg : g.Prime) {r : ℕ} {Z : Type} [TopologicalSpace Z]
    (f1 f2 : Z → TupV (E := E) v n (r + 1)) (h1 : Continuous f1) (h2 : Continuous f2) :
    IsClosed {z | ∀ a, ∃ y ∈ latLoc (E := E) v Λ,
      locF v (f2 z) a - locF v (f1 z) a = sc (E := E) v (g : Fv F v) • y} := by
  have hg0 : (g : Fv F v) ≠ 0 := by
    rw [← map_natCast (algebraMap F (Fv F v)) g]
    exact (map_ne_zero _).mpr (by exact_mod_cast hg.ne_zero)
  have heq : {z | ∀ a, ∃ y ∈ latLoc (E := E) v Λ,
      locF v (f2 z) a - locF v (f1 z) a = sc (E := E) v (g : Fv F v) • y} =
      ⋂ a, (fun z => sc (E := E) v (g : Fv F v)⁻¹ • (locF v (f2 z) a - locF v (f1 z) a)) ⁻¹'
        (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact forall_congr' fun a => mem_gLat_iff v Λ hg0 _
  rw [heq]
  refine isClosed_iInter fun a => (LocMassOrdKv.isClosed_latLoc (σ := σ) (J := J) (v := v) Λ hSD).preimage ?_
  exact (continuous_const : Continuous fun _ : Z => sc (E := E) v (g : Fv F v)⁻¹).smul
    (((continuous_locF v a).comp h2).sub ((continuous_locF v a).comp h1))

theorem measurableSet_omTyp (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hSD : IsSDLoc σ J v Λ)
    {g : ℕ} (hg : g.Prime) (hgv : (g : 𝓞 F) ∈ v.asIdeal) (r : ℕ) :
    MeasurableSet (OmTyp v Λ g r) := by
  have hc1 : Continuous fun p : TupV (E := E) v n (r + 1) × TupV (E := E) v n (r + 1) => locF v p.1 :=
    continuous_pi fun a => (continuous_locF v a).comp continuous_fst
  have hc2 : Continuous fun p : TupV (E := E) v n (r + 1) × TupV (E := E) v n (r + 1) => locF v p.2 :=
    continuous_pi fun a => (continuous_locF v a).comp continuous_snd
  have h1 := (measurableSet_prim v Λ σ J hSD hg hgv (r + 1)).preimage hc1.measurable
  have h2 := (measurableSet_prim v Λ σ J hSD hg hgv (r + 1)).preimage hc2.measurable
  have h3 := (isClosed_cong v Λ σ J hSD hg (r := r)
    (Z := TupV (E := E) v n (r + 1) × TupV (E := E) v n (r + 1)) Prod.fst Prod.snd continuous_fst continuous_snd).measurableSet
  exact h1.inter (h2.inter h3)

end Lat

section K1

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
  (Λ : Set (Fin n → E))

theorem isClosed_congruence_subgroup (hSD : IsSDLoc σ J v Λ) {g : ℕ} (hg : g.Prime) {r : ℕ} (P : Frame E n r) :
    IsClosed (K1 σ J v Λ g P) := by
  exact (LocMassOrdKv.isClosed_Kv (σ := σ) (J := J) (v := v) Λ hSD).inter
    (isClosed_cong v Λ σ J hSD hg (Z := HA (Fv F v) σ J) (fun _ => ratTup (Fv F v) (F0 P))
      (fun k => k • ratTup (Fv F v) (F0 P)) continuous_const (continuous_smulTup σ J v _))

end K1

end PI.LocMassTypM
