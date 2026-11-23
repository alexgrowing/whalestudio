import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.MassDataKppVolOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocBEOfNatCast
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.LatticeOfEntriesIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.CoordFin

noncomputable section

namespace PI.MassDataKppVolLemmas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Topology Filter
open scoped ENNReal TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst)

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

theorem Glob_measure_eq_relIndex_mul (μ : Measure G) [μ.IsMulLeftInvariant] (K H : Subgroup G)
    (hle : H ≤ K) (ho : IsOpen (H : Set G)) (hi : H.relIndex K ≠ 0) :
    μ K = (H.relIndex K : ℝ≥0∞) * μ H := by
  have hK : IsOpen (K : Set G) := Subgroup.isOpen_mono hle ho
  classical
  haveI : (H.subgroupOf K).FiniteIndex := ⟨hi⟩
  haveI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  have hc : H.relIndex K = Fintype.card (K ⧸ H.subgroupOf K) := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hU : (K : Set G) =
      ⋃ q : K ⧸ H.subgroupOf K, (fun y => (q.out : G)⁻¹ * y) ⁻¹' (H : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf K) (⟨x, hx⟩ : K)
      rw [hh]
      have h2 : ((h : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp h.2
      simpa [mul_assoc] using H.inv_mem h2
    · rintro ⟨q, hq⟩
      have h1 : (q.out : G) ∈ K := q.out.2
      have h2 : (q.out : G)⁻¹ * x ∈ K := hle hq
      simpa using K.mul_mem h1 h2
  have hD : Pairwise (Function.onFun Disjoint
      fun q : K ⧸ H.subgroupOf K => (fun y => (q.out : G)⁻¹ * y) ⁻¹' (H : Set G)) := by
    intro q q' hne
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    have h1 : (q.out : G)⁻¹ * x ∈ H := hx
    have h2 : (q'.out : G)⁻¹ * x ∈ H := hx'
    apply hne
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h3 := H.mul_mem h1 (H.inv_mem h2)
    simpa [mul_assoc] using h3
  have hM : ∀ q : K ⧸ H.subgroupOf K,
      MeasurableSet ((fun y => (q.out : G)⁻¹ * y) ⁻¹' (H : Set G)) :=
    fun q => (ho.preimage (continuous_const.mul continuous_id)).measurableSet
  rw [hc, hU, MeasureTheory.measure_iUnion hD hM, tsum_fintype]
  simp only [MeasureTheory.measure_preimage_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Haar

section Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem Glob_topRing : IsTopologicalRing (Af F ⊗[F] E) := by
  first
    | infer_instance
    | exact IsModuleTopology.isTopologicalRing (Af F) (Af F ⊗[F] E)

theorem Glob_topGroup (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsTopologicalGroup (HA (Af F) σ J) := by
  haveI : IsTopologicalRing (Af F ⊗[F] E) := Glob_topRing
  first
    | exact inferInstanceAs (IsTopologicalGroup (HR (Af F) σ J))
    | (unfold HA; infer_instance)
    | (show IsTopologicalGroup (HR (Af F) σ J); infer_instance)

end Top

variable (I : AutInst)

def Glob_basis : Module.Basis (Fin 2) (Af I.F) (Af I.F ⊗[I.F] I.E) :=
  Algebra.TensorProduct.basis (Af I.F) (PI.InvTopW.basisE I)

theorem Glob_swap_symm_tmul (a : Af I.F) (x : I.E) : (swapE I).symm (a ⊗ₜ[I.F] x) = x ⊗ₜ[I.F] a := by
  first
    | rfl
    | simp [swapE]
    | (rw [LinearEquiv.symm_apply_eq]; rfl)

theorem Glob_nhd_zero (N : ℕ) (hN : 1 ≤ N) :
    ∀ᶠ t in 𝓝 (0 : Af I.F ⊗[I.F] I.E), PI.InvTopW.InNInt I N ((swapE I).symm t) := by
  have : IsModuleTopology (Af I.F) (Af I.F ⊗[I.F] I.E) := ⟨rfl⟩
  have hA := PI.InvTopW.finite_neighbourhood_first I.F N hN
  have hev : ∀ k : Fin 2, ∀ᶠ t in 𝓝 (0 : Af I.F ⊗[I.F] I.E),
      (Glob_basis I).coord k t ∈ {a : FiniteAdeleRing (𝓞 I.F) I.F |
        ∃ z ∈ Formalism.UG.intAd I.F, a = (N : FiniteAdeleRing (𝓞 I.F) I.F) * z} := by
    intro k
    have hc : Continuous ((Glob_basis I).coord k) := IsModuleTopology.continuous_of_linearMap _
    refine hc.continuousAt.preimage_mem_nhds ?_
    rw [map_zero]
    exact hA
  filter_upwards [Filter.eventually_all.2 hev] with t ht
  choose z hz hzt using ht
  refine ⟨∑ k, PI.InvTopW.basisE I k ⊗ₜ[I.F] z k,
    Subring.sum_mem _ fun k _ => PI.InvTopW.tmul_mem_IntAf I (PI.InvTopW.basisE_mem I k) (hz k), ?_⟩
  have ht : t = ∑ k, ((Glob_basis I).coord k t) ⊗ₜ[I.F] PI.InvTopW.basisE I k := by
    conv_lhs => rw [← (Glob_basis I).sum_repr t]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Glob_basis, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  rw [ht, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Glob_swap_symm_tmul, hzt k]
  exact PI.InvTopW.tmul_natCast_mul I N _ _

abbrev Glob_m (h : HA (Af I.F) I.cm.sig I.J) : Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E) :=
  ((HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) _)

theorem Glob_m_one : Glob_m I 1 = 1 := rfl

theorem Glob_continuous_m : Continuous (Glob_m I) := by
  first
    | fun_prop
    | exact Units.continuous_val.comp continuous_subtype_val
    | exact Units.continuous_val.comp ((HA.mat (Af I.F) I.cm.sig I.J).continuous)

theorem Glob_nhd_one (hb : AdBridgeIso I) (g : ℕ) (hg : 1 ≤ g) :
    tf I hb '' I.Kg g ∈ 𝓝 (1 : HA (Af I.F) I.cm.sig I.J) := by
  have : FiniteDimensional I.F I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := Glob_topRing (F := I.F) (E := I.E)
  have := Glob_topGroup (F := I.F) (E := I.E) I.cm.sig I.J
  obtain ⟨N, hN, hE⟩ := PI.InvTopW.entries_integral_of_lattice I g hg
  have hm := Glob_continuous_m I
  have hev : ∀ i j, ∀ᶠ h in 𝓝 (1 : HA (Af I.F) I.cm.sig I.J),
      PI.InvTopW.InNInt I N ((swapE I).symm ((Glob_m I h - 1) i j)) ∧
        PI.InvTopW.InNInt I N ((swapE I).symm ((Glob_m I h⁻¹ - 1) i j)) := by
    intro i j
    refine Filter.Eventually.and ?_ ?_
    · have hc : Continuous fun h => (Glob_m I h - 1) i j :=
        (hm.sub continuous_const).matrix_elem i j
      have h0 : (Glob_m I 1 - 1) i j = 0 := by rw [Glob_m_one, sub_self]; rfl
      have ht := hc.tendsto 1
      rw [h0] at ht
      exact ht.eventually (Glob_nhd_zero I N hN)
    · have hc : Continuous fun h => (Glob_m I h⁻¹ - 1) i j :=
        ((hm.comp continuous_inv).sub continuous_const).matrix_elem i j
      have h0 : (Glob_m I (1 : HA (Af I.F) I.cm.sig I.J)⁻¹ - 1) i j = 0 := by
        rw [inv_one, Glob_m_one, sub_self]; rfl
      have ht := hc.tendsto 1
      rw [h0] at ht
      exact ht.eventually (Glob_nhd_zero I N hN)
  have hall : ∀ᶠ h in 𝓝 (1 : HA (Af I.F) I.cm.sig I.J), ∀ i j,
      PI.InvTopW.InNInt I N ((swapE I).symm ((Glob_m I h - 1) i j)) ∧
        PI.InvTopW.InNInt I N ((swapE I).symm ((Glob_m I h⁻¹ - 1) i j)) := by
    simp only [Filter.eventually_all]
    exact hev
  filter_upwards [hall] with h hh
  obtain ⟨x, rfl⟩ := Bridge_tf_surjective I hb h
  refine ⟨x, ?_, rfl⟩
  have hmx : ∀ y : I.Gf, I.fmat y = (Glob_m I (tf I hb y)).map (swapE I).symm := by
    intro y
    have := Bridge_mat I hb y
    rw [Glob_m, this]
    ext i j
    simp
  have hent : ∀ y : I.Gf, ∀ i j, (I.fmat y - 1) i j = (swapE I).symm ((Glob_m I (tf I hb y) - 1) i j) := by
    intro y i j
    rw [hmx y, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have hinv : tf I hb x⁻¹ = (tf I hb x)⁻¹ := map_inv (tfHom I hb) x
  have hMM : I.fmat x * I.fmat x⁻¹ = 1 := by
    rw [← LocB_fmat_mul I, mul_inv_cancel, LocB_fmat_one I]
  have hK := hE (I.fmat x) (I.fmat x⁻¹) hMM
    (fun i j => by rw [hent x i j]; exact (hh i j).1)
    (fun i j => by rw [hent x⁻¹ i j, hinv]; exact (hh i j).2)
  exact ⟨hK.1, hK.2⟩

section HidaSetting

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def Glob_K2Sub (hK : X.LevelSubgroupCharacter) : Subgroup X.B.I.Gf where
  carrier := X.K2
  one_mem' := hK.1
  mul_mem' := fun {a c} ha hc => hK.2.1 a ha c hc
  inv_mem' := fun {a} ha => hK.2.2.1 a ha

def Glob_KppH (hK : X.LevelSubgroupCharacter) : Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
  (Glob_K2Sub X hK).map (tfHom X.B.I hb)

theorem Glob_coe_KppH (hK : X.LevelSubgroupCharacter) : (Glob_KppH X hb hK : Set _) = levelUnitary X hb := by
  first
    | rfl
    | (ext h; simp [Glob_KppH, Glob_K2Sub, levelUnitary])
    | (unfold levelUnitary; ext h; simp [Glob_KppH, Glob_K2Sub])

theorem Glob_KppS_eq (hK : X.LevelSubgroupCharacter) : KppS X hb = Glob_KppH X hb hK := by
  unfold KppS
  rw [← Glob_coe_KppH X hb hK, Subgroup.closure_eq]

theorem Glob_KppH_le (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) : Glob_KppH X hb hK ≤ KfS X := by
  rintro _ ⟨x, hx, rfl⟩
  exact (Bridge_mem_Kf_iff X.B.I hb x).2 (hL.2.1 x hx)

theorem Glob_isOpen_KppH (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) :
    IsOpen (Glob_KppH X hb hK : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
  haveI := Glob_topGroup X.B.I.cm.sig X.B.I.J
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (Glob_nhd_one X.B.I hb X.B.g hg) ?_)
  rw [Glob_coe_KppH X hb hK]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, (hL.1 x hx).1, rfl⟩

theorem Glob_globIdx (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) : GlobIdx X hb := by
  intro hi
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := Glob_topGroup (F := X.B.I.F) (E := X.B.I.E) X.B.I.cm.sig X.B.I.J
  have : BorelSpace (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have : X.measG.μGf.IsHaarMeasure := X.measG_norm.2.2.1
  have hK2 : levelUnitary X hb = (KppS X hb : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
    rw [Glob_KppS_eq X hb hK, Glob_coe_KppH]
  rw [hK2]
  have hle : KppS X hb ≤ KfS X := by rw [Glob_KppS_eq X hb hK]; exact Glob_KppH_le X hb hK hL
  have ho : IsOpen (KppS X hb : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
    rw [Glob_KppS_eq X hb hK]; exact Glob_isOpen_KppH X hb hK hL
  exact Glob_measure_eq_relIndex_mul X.measG.μGf (KfS X) (KppS X hb) hle ho hi

end HidaSetting

theorem global_index_every_setting : GlobIdxAll := by
  intro D X hb hK _ hL
  exact Glob_globIdx X hb hK hL

end PI.MassDataKppVolLemmas
