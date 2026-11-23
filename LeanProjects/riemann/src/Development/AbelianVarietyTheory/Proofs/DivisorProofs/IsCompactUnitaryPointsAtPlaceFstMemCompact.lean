import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem isCompact_setOf_fst_mem (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) :
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C);
    ∀ K : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K →
      IsCompact {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} := by
  letI tA : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  intro K hK
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  haveI : T2Space (Qv v ⊗[ℚ] G.C) := T2Space.of_injective_continuous (basV G v).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.toLinearMap)
  have hst1 : ∀ r : Qv v, (starT G.star (Qv v) (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r)).unop =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r := by
    intro r
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, starT_tmul, map_one,
      MulOpposite.unop_one]
  let sL : (Qv v ⊗[ℚ] G.C) →ₗ[Qv v] (Qv v ⊗[ℚ] G.C) :=
    { toFun := fun y => (starT G.star (Qv v) y).unop
      map_add' := fun x y => by simp
      map_smul' := fun r y => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, MulOpposite.unop_mul]
        rw [hst1]
        exact (Algebra.commutes r _).symm }
  have hsc : Continuous sL := IsModuleTopology.continuous_of_linearMap sL
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one (K := Qv v) (s := ({()} : Set Unit))
    (v := fun _ : Unit => (1 : Qv v ⊗[ℚ] G.C)) (by
      rw [linearIndepOn_singleton_iff]; exact one_ne_zero)
  have hf1 : f 1 = 1 := hf () rfl
  have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have key : ∀ d : Gv G v, f (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C) *
      sL ((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C)) =
      (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := by
    intro d
    have hd : (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) *
        (starT G.star (Qv v) ((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C)).unop =
        algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := d.2
    show f (_ * (starT G.star (Qv v) _).unop) = _
    rw [hd, Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_eq_mul, mul_one]
  set L1 : Set (Qv v) := (fun u : (Qv v ⊗[ℚ] G.C)ˣ => f ((u : Qv v ⊗[ℚ] G.C) * sL u)) '' K with hL1
  set L2 : Set (Qv v) := (fun u : (Qv v ⊗[ℚ] G.C)ˣ =>
    f (((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * sL ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C))) '' K with hL2
  have hL1c : IsCompact L1 := hK.image (hfc.comp (Units.continuous_val.mul (hsc.comp Units.continuous_val)))
  have hL2c : IsCompact L2 := hK.image (hfc.comp (Units.continuous_coe_inv.mul (hsc.comp Units.continuous_coe_inv)))
  set T : Set (Qv v)ˣ := Units.embedProduct (Qv v) ⁻¹' (L1 ×ˢ (MulOpposite.op '' L2)) with hT
  have hTc : IsCompact T :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hL1c.prod (hL2c.image MulOpposite.continuous_op))
  set Z : Set ((Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ) := {x | ((x.1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) *
      sL ((x.1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) ((x.2 : (Qv v)ˣ) : Qv v)} with hZ
  have hZc : IsClosed Z := isClosed_eq
    ((Units.continuous_val.comp continuous_fst).mul (hsc.comp (Units.continuous_val.comp continuous_fst)))
    ((continuous_algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)).comp (Units.continuous_val.comp continuous_snd))
  have himg : Subtype.val '' {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} = (K ×ˢ T) ∩ Z := by
    ext x
    constructor
    · rintro ⟨d, hdK, rfl⟩
      have k2 := key d⁻¹
      simp only [Subgroup.coe_inv, Prod.fst_inv, Prod.snd_inv] at k2
      refine ⟨⟨hdK, ?_⟩, d.2⟩
      show Units.embedProduct (Qv v) _ ∈ L1 ×ˢ (MulOpposite.op '' L2)
      rw [Units.embedProduct_apply]
      exact ⟨⟨_, hdK, key d⟩, ⟨_, ⟨_, hdK, k2⟩, rfl⟩⟩
    · rintro ⟨⟨hK1, -⟩, hZ1⟩
      exact ⟨⟨x, hZ1⟩, hK1, rfl⟩
  exact Subtype.isCompact_iff.2 (himg ▸ (hK.prod hTc).inter_right hZc)

end GlobalTheory.OrbFinAf
