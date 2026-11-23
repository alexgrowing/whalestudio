import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem eventually_int_of_isCompact {p : ℕ} (K : Set (AfP p)) (hK : IsCompact K) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a ∈ K, AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ := by
  obtain ⟨s, hs⟩ := hK.elim_directed_cover
    (fun s : Finset (AwayP p) => {z : AfP p | ∀ v ∉ s, AfP.eval v z ∈ v.1.adicCompletionIntegers ℚ})
    (fun s => RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ s))
    (fun y _ => by
      have h : {v : AwayP p | ¬ AfP.eval v y ∈ v.1.adicCompletionIntegers ℚ}.Finite := y.2
      refine Set.mem_iUnion.2 ⟨h.toFinset, fun v hv => ?_⟩
      by_contra hc
      exact hv ((Set.Finite.mem_toFinset _).2 hc))
    (fun s t => ⟨s ∪ t, fun y hy v hv => hy v fun h => hv (Finset.mem_union_left _ h),
      fun y hy v hv => hy v fun h => hv (Finset.mem_union_right _ h)⟩)
  rw [Filter.eventually_cofinite]
  refine (s.finite_toSet).subset fun v hv => ?_
  by_contra hvs
  exact hv fun a ha => hs ha v hvs

theorem repr_map_eval {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (y : AfP p ⊗[ℚ] G.C)
    (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) y) i =
      AfP.eval v ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    simp only [basV, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem cptInt : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω →
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), piV G v '' Ω ⊆ IntV G v := by
  intro p _ G Ω hΩ
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  set bA := Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C) with hbA
  have hrep : ∀ i, Continuous (fun y : AfP p ⊗[ℚ] G.C => bA.repr y i) := fun i => by
    have := IsModuleTopology.continuous_of_linearMap (R := AfP p) (bA.coord i)
    exact this
  have hg1 : Continuous (fun g : G.GAf => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have hg2 : Continuous (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)
  have hg3 : Continuous (fun g : G.GAf => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)) :=
    Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
  have hg4 : Continuous (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) :=
    Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  have h1 := Filter.eventually_all.2 fun i => eventually_int_of_isCompact _ (hΩ.image ((hrep i).comp hg1))
  have h2 := Filter.eventually_all.2 fun i => eventually_int_of_isCompact _ (hΩ.image ((hrep i).comp hg2))
  have h3 := eventually_int_of_isCompact _ (hΩ.image hg3)
  have h4 := eventually_int_of_isCompact _ (hΩ.image hg4)
  filter_upwards [h1, h2, h3, h4] with v hv1 hv2 hv3 hv4
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
  · have e : ((((piV G v g : Gv G v) : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
          (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := rfl
    rw [e, repr_map_eval]
    exact hv1 i _ ⟨g, hg, rfl⟩
  · have e : (((((piV G v g : Gv G v) : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
          ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := rfl
    rw [e, repr_map_eval]
    exact hv2 i _ ⟨g, hg, rfl⟩
  · exact hv3 _ ⟨g, hg, rfl⟩
  · exact hv4 _ ⟨g, hg, rfl⟩

end GlobalTheory.OrbFinAf

end
