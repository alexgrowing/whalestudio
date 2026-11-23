import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.Cover

open NumberField IsDedekindDomain Topology

theorem exists_finset_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (U : Subgroup H) (hU : IsOpen (U : Set H)) (K : Set G) (hK : IsCompact K)
    (Ω : Set H) (hΩ : ∀ k ∈ Ω, (k : G) ∈ K) :
    ∃ S : Finset H, (∀ x ∈ S, x ∈ Ω) ∧ ∀ k ∈ Ω, ∃ x ∈ S, x⁻¹ * k ∈ U := by
  classical
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.1 hU
  have h1 : (1 : G) ∈ W := by
    have : (1 : H) ∈ (U : Set H) := U.one_mem
    rw [← hWU] at this
    exact this
  have hc : Continuous fun p : G × G => p.1⁻¹ * p.2 := by fun_prop
  have h2 : (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' W ∈ 𝓝 ((1, 1) : G × G) :=
    (hW.preimage hc).mem_nhds (by simpa using h1)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 h2
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => (fun y => x⁻¹ * y) ⁻¹' (A ∩ B)) (fun x _ => by
    have : Continuous fun y : G => x⁻¹ * y := by fun_prop
    exact this.continuousAt.preimage_mem_nhds (by simpa using ⟨hA, hB⟩))
  have hch : ∀ x : G, (∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B) → ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B := fun _ h => h
  choose f hf hf' using hch
  refine ⟨(t.filter fun x => ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B).attach.image
    fun x => f x.1 (by have h := x.2; rw [Finset.mem_filter] at h; exact h.2), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hf _ _
  · intro k hk
    obtain ⟨x, hx, hxk⟩ := Set.mem_iUnion₂.1 (ht (hΩ k hk))
    have hex : ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B := ⟨k, hk, hxk⟩
    refine ⟨f x hex, Finset.mem_image.2 ⟨⟨x, Finset.mem_filter.2 ⟨hx, hex⟩⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have h3 := hAB (Set.mk_mem_prod (hf' x hex).1 hxk.2)
    have h4 : (x⁻¹ * (f x hex : G))⁻¹ * (x⁻¹ * (k : G)) = (((f x hex)⁻¹ * k : H) : G) := by
      push_cast; group
    change _ ∈ (U : Set H)
    rw [← hWU]
    change _ ∈ W
    rw [← h4]
    exact h3

theorem isCompact_GL {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {n : ℕ}
    (C : Fin n → Fin n → Set A) (hC : ∀ i j, IsCompact (C i j)) :
    IsCompact {g : GL (Fin n) A | ∀ i j, g.1 i j ∈ C i j ∧ (g⁻¹).1 i j ∈ C i j} := by
  have h1 : IsCompact {m : Matrix (Fin n) (Fin n) A | ∀ i j, m i j ∈ C i j} :=
    isCompact_pi_infinite fun i => isCompact_pi_infinite (hC i)
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) A)).isCompact_preimage
    (h1.prod (h1.image MulOpposite.continuous_op))
  convert h2 using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image,
    MulOpposite.op_inj, exists_eq_right, forall_and]

theorem exists_compact_denom (D : D7) (d : ℕ) (hd : 0 < d) :
    ∃ C : Set (Af D.host.F ⊗[D.host.F] D.host.E), IsCompact C ∧ ∀ y, d • y ∈ intAE D → y ∈ C := by
  classical
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  let b := RingOfIntegers.basis D.host.E
  let O : AddSubgroup (Af D.host.F) :=
    { carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers D.host.F}
      zero_mem' := fun v => zero_mem _
      add_mem' := fun ha hb v => add_mem (ha v) (hb v)
      neg_mem' := fun ha v => neg_mem (ha v) }
  let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) → Af D.host.F) →+
      Af D.host.F ⊗[D.host.F] D.host.E :=
    { toFun := fun a => ∑ i, a i • ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b i : D.host.E))
      map_zero' := by simp
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib] }
  have hφ : Continuous φ :=
    continuous_finset_sum _ fun i _ => (continuous_apply i).fun_smul continuous_const
  have hle : intAE D ≤ (AddSubgroup.pi Set.univ fun _ => O).map φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro y ⟨a, ha, x, rfl⟩
    refine ⟨fun i => b.repr x i • a, fun i _ => zsmul_mem (show a ∈ O from ha) _, ?_⟩
    change ∑ i, (b.repr x i • a) • ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b i : D.host.E)) = _
    conv_rhs => rw [← b.sum_repr x]
    change _ = a ⊗ₜ[D.host.F] (algebraMap (𝓞 D.host.E) D.host.E _)
    rw [map_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, smul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact (map_zsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E a) _ _).symm
  have hO : IsCompact (Set.pi Set.univ fun _ : Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) =>
      (O : Set (Af D.host.F))) :=
    isCompact_univ_pi fun _ => GlobalTheory.AdeleCocompact.isCompact_integral D.host.F
  let c : Af D.host.F := algebraMap D.host.F (Af D.host.F) (d : D.host.F)⁻¹
  have hcs : Continuous fun y : Af D.host.F ⊗[D.host.F] D.host.E => c • y :=
    (continuous_const (y := c)).fun_smul continuous_id
  refine ⟨(fun y => c • y) '' (φ '' _), (hO.image hφ).image hcs, fun y hy => ?_⟩
  refine ⟨d • y, hle hy, ?_⟩
  have : (d : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  change c • d • y = y
  rw [← Nat.cast_smul_eq_nsmul (Af D.host.F), smul_smul,
    ← map_natCast (algebraMap D.host.F (Af D.host.F)) d, ← map_mul, inv_mul_cancel₀ this, map_one, one_smul]

theorem exists_finset_cover : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ d : ℕ, 0 < d → ∃ S : Finset (GA D V), ∀ k ∈ GfC V, BddDen V d k → ∃ x ∈ S, x⁻¹ * k ∈ U ∧ x⁻¹ * k ∈ GfC V := by
  intro D V U hU d hd
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  haveI : T2Space (AE D) := e0.isEmbedding.t2Space
  obtain ⟨C, hC, hCd⟩ := exists_compact_denom D d hd
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let C' : Fin V.rank → Fin V.rank → Set (AE D) := fun i j =>
    e.symm '' ({(1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j} ×ˢ C)
  have hC' : ∀ i j, IsCompact (C' i j) := fun i j => (isCompact_singleton.prod hC).image hc
  have key : ∀ k ∈ GfC V, (∀ i j, d • finMat D.sp.cm.sig V.gram k i j ∈ intAE D) →
      ∀ i j, (matHom V k).1 i j ∈ C' i j := by
    intro k hk h i j
    refine ⟨e ((matHom V k).1 i j), ⟨?_, ?_⟩, e.symm_apply_apply _⟩
    · rw [(he _).1]
      have h1 : (infHom V k).1 i j = _ := congrArg (fun g => g.1 i j) (MonoidHom.mem_ker.1 hk)
      exact h1
    · rw [(he _).2]
      exact hCd _ (h i j)
  obtain ⟨S, hS, hS'⟩ := exists_finset_of_compact (HR (AF D.host.F) D.sp.cm.sig V.gram) U hU _
    (isCompact_GL C' hC') {k : GA D V | k ∈ GfC V ∧ BddDen V d k} (fun k hk i j =>
      ⟨key k hk.1 (fun i j => (hk.2 i j).1) i j, key k⁻¹ (inv_mem hk.1) (fun i j => (hk.2 i j).2) i j⟩)
  refine ⟨S, fun k hk hb => ?_⟩
  obtain ⟨x, hx, hxk⟩ := hS' k ⟨hk, hb⟩
  exact ⟨x, hx, hxk, mul_mem (inv_mem (hS x hx).1) hk⟩

end GlobalTheory.SmoothForms.Cover
