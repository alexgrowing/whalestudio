import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AwayOrb.Cpt
open scoped RestrictedProduct
variable {p : ℕ} [Fact p.Prime]

theorem eventually_int_of_isCompact (K : Set (AfP p)) (hK : IsCompact K) :
    ∀ᶠ w in Filter.cofinite, ∀ x ∈ K, AfP.eval w x ∈ w.1.adicCompletionIntegers ℚ := by
  let U : Finset (AwayP p) → Set (AfP p) := fun F =>
    {f : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ] |
      ∀ i, i ∉ F → f.1 i ∈ (i.1.adicCompletionIntegers ℚ : Set (i.1.adicCompletion ℚ))}
  have hU : ∀ F, IsOpen (U F) := fun F =>
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun i => i ∉ F)
  have hcov : K ⊆ ⋃ F, U F := by
    intro x _
    have hx := x.2
    rw [Filter.eventually_cofinite] at hx
    refine Set.mem_iUnion.2 ⟨hx.toFinset, fun i hi => ?_⟩
    by_contra h
    exact hi (hx.mem_toFinset.2 h)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcov
  let S : Finset (AwayP p) := t.biUnion id
  rw [Filter.eventually_cofinite]
  refine S.finite_toSet.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hw
  obtain ⟨x, hxK, hxw⟩ := hw
  obtain ⟨F, hF, hxF⟩ := Set.mem_iUnion₂.1 (ht hxK)
  by_contra hwS
  exact hxw (hxF w fun hwF => hwS (Finset.mem_biUnion.2 ⟨F, hF, hwF⟩))

theorem repr_map_eval (G : HTGroup p) (w : AwayP p) (x : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) (Module.finBasis ℚ G.C)).repr
        (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) x) i =
      AfP.eval w ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r c =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]

theorem continuous_coord (G : HTGroup p) (i : Fin (Module.finrank ℚ G.C)) :
    Continuous fun x : G.GAf => (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
      (((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  exact (IsModuleTopology.continuous_of_linearMap
    ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).coord i)).comp
    (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val))

theorem continuous_coord_inv (G : HTGroup p) (i : Fin (Module.finrank ℚ G.C)) :
    Continuous fun x : G.GAf => (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
      ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) i := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) (AfP p ⊗[ℚ] G.C)
  exact (IsModuleTopology.continuous_of_linearMap
    ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).coord i)).comp
    (Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val))

theorem continuous_sim (G : HTGroup p) :
    Continuous fun x : G.GAf => (((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)

theorem continuous_sim_inv (G : HTGroup p) :
    Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)

theorem eventually_mem_intPts (G : HTGroup p) (Ω : Set G.GAf) (hΩ : IsCompact Ω) :
    ∀ᶠ w in Filter.cofinite, ∀ h ∈ Ω, compL G w h ∈ intPts G w := by
  have h1 : ∀ᶠ w in Filter.cofinite, ∀ i, ∀ h ∈ Ω, AfP.eval w
      ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
        (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i =>
      (eventually_int_of_isCompact _ (hΩ.image (continuous_coord G i))).mono fun w hw h hh =>
        hw _ (Set.mem_image_of_mem _ hh)
  have h2 : ∀ᶠ w in Filter.cofinite, ∀ i, ∀ h ∈ Ω, AfP.eval w
      ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
        ((((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) i) ∈
        w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i =>
      (eventually_int_of_isCompact _ (hΩ.image (continuous_coord_inv G i))).mono fun w hw h hh =>
        hw _ (Set.mem_image_of_mem _ hh)
  have h3 := eventually_int_of_isCompact _ (hΩ.image (continuous_sim G))
  have h4 := eventually_int_of_isCompact _ (hΩ.image (continuous_sim_inv G))
  filter_upwards [h1, h2, h3, h4] with w hw1 hw2 hw3 hw4 h hh
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
  · have e := repr_map_eval G w (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i
    have := hw1 i h hh
    rw [← e] at this
    exact this
  · have e := repr_map_eval G w ((((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) :
      AfP p ⊗[ℚ] G.C) i
    have := hw2 i h hh
    rw [← e] at this
    exact this
  · exact hw3 _ (Set.mem_image_of_mem _ hh)
  · exact hw4 _ (Set.mem_image_of_mem _ hh)

end GlobalTheory.AwayOrb.Cpt

theorem GlobalTheory.AwayOrb.eventually_compL_mem_intPts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf),
    IsCompact Ω → ∀ᶠ w in Filter.cofinite, ∀ h ∈ Ω, compL G w h ∈ intPts G w :=
  fun _ _ G Ω hΩ => GlobalTheory.AwayOrb.Cpt.eventually_mem_intPts G Ω hΩ

end
