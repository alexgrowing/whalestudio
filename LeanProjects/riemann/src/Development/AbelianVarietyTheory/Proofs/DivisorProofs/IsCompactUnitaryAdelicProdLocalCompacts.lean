import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime]

theorem isCompact_box (K : ∀ v : AwayP p, Set (Qv v)) (hK : ∀ v, IsCompact (K v))
    (h : ∀ᶠ v in Filter.cofinite, K v ⊆ v.1.adicCompletionIntegers ℚ) :
    IsCompact {a : AfP p | ∀ v, AfP.eval v a ∈ K v} := by
  let S : Set (AwayP p) := {v | K v ⊆ v.1.adicCompletionIntegers ℚ}
  have hS : Filter.cofinite ≤ Filter.principal S := Filter.le_principal_iff.2 h
  let P := RestrictedProduct (fun v : AwayP p => v.1.adicCompletion ℚ)
      (fun v => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) (Filter.principal S)
  have h1 : IsCompact {x : P | ∀ v, x v ∈ K v} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    convert isCompact_univ_pi hK
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ v -
      exact hy v
    · intro hx
      exact ⟨⟨x, fun v hv => hv (hx v trivial)⟩, fun v => hx v trivial, rfl⟩
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hS)
  have e : {a : AfP p | ∀ v, AfP.eval v a ∈ K v} = RestrictedProduct.inclusion _ _ hS '' {x : P | ∀ v, x v ∈ K v} := by
    ext a
    constructor
    · intro ha
      exact ⟨⟨(LevelExists.rp a).1, fun v hv => hv (ha v)⟩, ha, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [e]
  exact h2

end GlobalTheory.OrbFinAf.CompactOrbitVectors

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

def basA : Module.Basis (Fin (Module.finrank ℚ G.C)) (AfP p) (AfP p ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)

def tv (v : AwayP p) : AfP p ⊗[ℚ] G.C →+* Qv v ⊗[ℚ] G.C :=
  (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)).toRingHom

theorem repr_tv (v : AwayP p) (y : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (tv G v y) i = AfP.eval v ((basA G).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp [tv, basV, basA, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem continuous_eval (v : AwayP p) : Continuous (AfP.eval (p := p) v) :=
  RestrictedProduct.continuous_eval v

end GlobalTheory.OrbFinAf.CompactOrbitVectors

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem tv_eq (v : AwayP p) (y : AfP p ⊗[ℚ] G.C) :
    tv G v y = (basV G v).equivFun.symm (fun i => AfP.eval v ((basA G).equivFun y i)) := by
  apply (basV G v).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  simp only [Module.Basis.equivFun_apply]
  exact repr_tv G v y i

theorem continuous_tv (v : AwayP p) :
    @Continuous _ _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)) (moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)) (tv G v) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : ContinuousAdd (Qv v ⊗[ℚ] G.C) := IsModuleTopology.toContinuousAdd (Qv v) _
  have h1 : Continuous (basA G).equivFun := IsModuleTopology.continuous_of_linearMap (basA G).equivFun.toLinearMap
  have h2 : Continuous (basV G v).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.symm.toLinearMap
  have : tv G v = fun y => (basV G v).equivFun.symm (fun i => AfP.eval v ((basA G).equivFun y i)) :=
    funext (tv_eq G v)
  rw [this]
  exact h2.comp (continuous_pi fun i => (continuous_eval v).comp ((continuous_apply i).comp h1))

theorem continuous_piV (v : AwayP p) : Continuous (piV G v) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  have ht := continuous_tv G v
  have hval : Continuous fun x : G.GAf => ((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have hinv : Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)
  have hval2 : Continuous fun x : G.GAf => ((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) :=
    Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
  have hinv2 : Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) :=
    Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · rw [Units.continuous_iff]
    exact ⟨ht.comp hval, ht.comp hinv⟩
  · rw [Units.continuous_iff]
    exact ⟨(continuous_eval v).comp hval2, (continuous_eval v).comp hinv2⟩

end GlobalTheory.OrbFinAf.CompactOrbitVectors

open scoped RestrictedProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

open CompactOrbitVectors in

theorem isCompact_prod_local : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (D : ∀ v : AwayP p, Set (Gv G v)),
    (∀ v, IsCompact (D v)) → (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D v ⊆ IntV G v) →
    IsCompact {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
  intro p _ G D hDc hDi
  haveI : T2Space (AfP p) := inferInstanceAs
    (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) _
  haveI : T2Space (AfP p ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (AfP p) G.C

  let c1 : ∀ v : AwayP p, Fin (Module.finrank ℚ G.C) → Gv G v → Qv v := fun v i h =>
    (basV G v).repr (((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) i
  let c2 : ∀ v : AwayP p, Fin (Module.finrank ℚ G.C) → Gv G v → Qv v := fun v i h =>
    (basV G v).repr ((((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) i
  let c3 : ∀ v : AwayP p, Gv G v → Qv v := fun v h => (((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v)
  let c4 : ∀ v : AwayP p, Gv G v → Qv v := fun v h =>
    ((((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v)
  have hc : ∀ v, (∀ i, Continuous (c1 v i)) ∧ (∀ i, Continuous (c2 v i)) ∧ Continuous (c3 v) ∧
      Continuous (c4 v) := by
    intro v
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
    have hr : Continuous (basV G v).equivFun :=
      IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.toLinearMap
    refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
    · exact (continuous_apply i).comp (hr.comp
        (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)))
    · exact (continuous_apply i).comp (hr.comp
        (Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)))
    · exact Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
    · exact Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  let K : ∀ v : AwayP p, Set (Qv v) := fun v =>
    ((⋃ i, c1 v i '' D v) ∪ (⋃ i, c2 v i '' D v)) ∪ (c3 v '' D v ∪ c4 v '' D v)
  have hKc : ∀ v, IsCompact (K v) := fun v =>
    ((isCompact_iUnion fun i => (hDc v).image ((hc v).1 i)).union
      (isCompact_iUnion fun i => (hDc v).image ((hc v).2.1 i))).union
      (((hDc v).image (hc v).2.2.1).union ((hDc v).image (hc v).2.2.2))
  have hKi : ∀ᶠ v in Filter.cofinite, K v ⊆ v.1.adicCompletionIntegers ℚ := by
    filter_upwards [hDi] with v hv
    rintro y ((hy | hy) | (hy | hy))
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, hh, rfl⟩ := hi
      exact (hv hh).1 i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, hh, rfl⟩ := hi
      exact (hv hh).2.1 i
    · obtain ⟨h, hh, rfl⟩ := hy
      exact (hv hh).2.2.1
    · obtain ⟨h, hh, rfl⟩ := hy
      exact (hv hh).2.2.2
  let E : Set (AfP p) := {a | ∀ v, AfP.eval v a ∈ K v}
  have hE : IsCompact E := isCompact_box K hKc hKi
  let Bm : Set (AfP p ⊗[ℚ] G.C) := (basA G).equivFun.symm '' Set.univ.pi fun _ => E
  have hBm : IsCompact Bm := (isCompact_univ_pi fun _ => hE).image
    (IsModuleTopology.continuous_of_linearMap (basA G).equivFun.symm.toLinearMap)
  let B : Set (((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ)) :=
    (Bm ×ˢ (MulOpposite.op '' Bm)) ×ˢ (E ×ˢ (MulOpposite.op '' E))
  have hB : IsCompact B := (hBm.prod (hBm.image MulOpposite.continuous_op)).prod
    (hE.prod (hE.image MulOpposite.continuous_op))

  have hσ : Continuous (fun y : AfP p ⊗[ℚ] G.C ↦ (starT G.star (AfP p) y).unop) := by
    let σl : (AfP p ⊗[ℚ] G.C) →ₗ[AfP p] (AfP p ⊗[ℚ] G.C) :=
      { toFun := fun y ↦ (starT G.star (AfP p) y).unop
        map_add' := fun x y ↦ by simp only [map_add, MulOpposite.unop_add]
        map_smul' := by
          intro r x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a y =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]
          | add x y hx hy => simp only [smul_add, map_add, MulOpposite.unop_add, hx, hy, RingHom.id_apply] }
    exact IsModuleTopology.continuous_of_linearMap σl
  have hj : Continuous (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AfP p) (AfP p ⊗[ℚ] G.C))
  have hGcl : IsClosed (UPts G.star (AfP p) : Set ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
    apply isClosed_eq
    · exact (Units.continuous_val.comp continuous_fst).mul
        (hσ.comp (Units.continuous_val.comp continuous_fst))
    · exact hj.comp (Units.continuous_val.comp continuous_snd)
  let emb : G.GAf → ((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ) :=
    fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)
  have hemb : Topology.IsClosedEmbedding emb :=
    (Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp
      hGcl.isClosedEmbedding_subtypeVal

  have hS : IsClosed {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
    have : {g : G.GAf | ∀ v, piV G v g ∈ D v} = ⋂ v, piV G v ⁻¹' D v := by
      ext g; simp
    rw [this]
    refine isClosed_iInter fun v => ?_
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
    haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
    haveI : T2Space (Qv v ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (Qv v) G.C
    haveI : T2Space (Gv G v) := inferInstance
    exact (hDc v).isClosed.preimage (continuous_piV G v)

  have hsub : emb '' {g : G.GAf | ∀ v, piV G v g ∈ D v} ⊆ B := by
    rintro _ ⟨x, hx, rfl⟩
    have hco : ∀ y : AfP p ⊗[ℚ] G.C,
        (∀ v i, (basV G v).repr (tv G v y) i ∈ K v) → y ∈ Bm := by
      intro y hy
      refine ⟨(basA G).equivFun y, fun i _ v => ?_, by simp⟩
      rw [Module.Basis.equivFun_apply, ← repr_tv]
      exact hy v i
    refine ⟨⟨hco _ fun v i => ?_, ⟨_, hco _ fun v i => ?_, rfl⟩⟩, ⟨fun v => ?_, ⟨_, fun v => ?_, rfl⟩⟩⟩
    · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, piV G v x, hx v, rfl⟩))
    · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, piV G v x, hx v, rfl⟩))
    · exact Or.inr (Or.inl ⟨piV G v x, hx v, rfl⟩)
    · exact Or.inr (Or.inr ⟨piV G v x, hx v, rfl⟩)
  exact hemb.isInducing.isCompact_iff.2 (hB.of_isClosed_subset (hemb.isClosedMap _ hS) hsub)

end GlobalTheory.OrbFinAf
