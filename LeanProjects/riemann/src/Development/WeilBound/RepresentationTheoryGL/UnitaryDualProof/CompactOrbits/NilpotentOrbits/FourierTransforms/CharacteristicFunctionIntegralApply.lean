import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.DistribHaarCharAdU

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
  [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
  (hZ : CR Z) (h : Hyp Z)

include hZ h

def phi0 (f : Sp k n → ℂ) : Sp k n → ℂ :=
  fun p => GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ : Fin (d Z) => ν) (fun q => f (F1 hZ h q)) (Hb hZ h p)

theorem characteristic_function_integral_apply (f : Sp k n → ℂ) (p : Sp k n) :
    phi0 ψ ν hZ h f p = ∫ u, f (p.1 - Pr Z p.1 + E Z u, p.2) * (ψ (u ⬝ᵥ D Z p.1) : ℂ) ∂(Measure.pi fun _ => ν) := by
  have key : ∀ x : Fin (d Z) → k, ((G Z)⁻¹ * G Z) *ᵥ x = x := fun x => by
    rw [← Matrix.mulVec_mulVec]
    exact (Gm hZ h).symm_apply_apply x
  simp [phi0, GlobalTheory.SplitDict.pf, F1, Hb, Gm, key]

theorem test_vector_mem_schwartz_bruhat {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) :
    phi0 ψ ν hZ h f ∈ supportedIn (Set.univ : Set (Sp k n)) := by
  have hg : (fun q => f (F1 hZ h q)) ∈ SB (TT Z × (Fin (d Z) → k)) :=
    ⟨hf.1.1.comp_continuous (F1 hZ h).continuous, hf.1.2.comp_homeomorph (F1 hZ h)⟩
  have hpf := GlobalTheory.SplitDict.pf_mem_SB (Measure.pi fun _ : Fin (d Z) => ν) hc hg
  refine ⟨⟨?_, ?_⟩, Set.subset_univ _⟩
  · exact hpf.1.comp_continuous (Hb hZ h).continuous
  · exact hpf.2.comp_homeomorph (Hb hZ h)

theorem integrable_slice (hψ : Continuous ψ) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n)))
    (p : Sp k n) :
    Integrable (fun u => f (p.1 - Pr Z p.1 + E Z u, p.2) * (ψ (u ⬝ᵥ D Z p.1) : ℂ)) (Measure.pi fun _ => ν) := by
  have key : ∀ x : Fin (d Z) → k, ((G Z)⁻¹ * G Z) *ᵥ x = x := fun x => by
    rw [← Matrix.mulVec_mulVec]
    exact (Gm hZ h).symm_apply_apply x
  have hslice : (fun x => f (p.1 - Pr Z p.1 + E Z x, p.2)) = fun x => (f ∘ F1 hZ h) ((Hb hZ h p).1, x) := by
    funext x
    simp [F1, Hb, Gm, key]
  have hg : HasCompactSupport (f ∘ F1 hZ h) := hf.1.2.comp_homeomorph _
  have hfc : Continuous f := hf.1.1.continuous
  have hcs : HasCompactSupport (fun x => f (p.1 - Pr Z p.1 + E Z x, p.2)) := by
    refine HasCompactSupport.intro (hg.isCompact.image continuous_snd) ?_
    intro x hx
    rw [congrFun hslice x]
    by_contra hne
    exact hx ⟨((Hb hZ h p).1, x), subset_tsupport _ hne, rfl⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ (hcs.mul_right (f' := fun u => (ψ (u ⬝ᵥ D Z p.1) : ℂ)))
  have h1 : Continuous (fun x => f (p.1 - Pr Z p.1 + E Z x, p.2)) := by
    rw [hslice]
    exact (hfc.comp (F1 hZ h).continuous).comp (Continuous.prodMk_right _)
  have h2 : Continuous (fun u : Fin (d Z) → k => (ψ (u ⬝ᵥ D Z p.1) : ℂ)) := by
    fun_prop
  exact h1.mul h2

def phiS (hψ : Continuous ψ) : (supportedIn (Set.univ : Set (Sp k n))) →ₗ[ℂ] (Sp k n → ℂ) where
  toFun f := phi0 ψ ν hZ h f.1
  map_add' f g := by
    funext p
    simp only [Submodule.coe_add, Pi.add_apply, characteristic_function_integral_apply, add_mul]
    exact integral_add (integrable_slice ψ ν hZ h hψ f.2 p) (integrable_slice ψ ν hZ h hψ g.2 p)
  map_smul' c f := by
    funext p
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, characteristic_function_integral_apply, mul_assoc, RingHom.id_apply]
    exact integral_const_mul _ _

end PositivityTheory.RgUd.T.Nil.Four.Phi2
