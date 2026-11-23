import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.PropLoc

universe u

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

theorem smul_bij {O V : Type u} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (c : O) (hc : c ≠ 0) :
    Function.Bijective fun v : V => c • v := by
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
    simpa using hc
  constructor
  · intro v w h
    have h' : algebraMap O (FractionRing O) c • v = algebraMap O (FractionRing O) c • w := by
      simpa only [algebraMap_smul] using h
    exact smul_right_injective V hc' h'
  · intro v
    refine ⟨(algebraMap O (FractionRing O) c)⁻¹ • v, ?_⟩
    show c • _ = v
    rw [← algebraMap_smul (FractionRing O) c, smul_smul, mul_inv_cancel₀ hc', one_smul]

theorem h_one_torsion_free {O G V : Type u} [CommRing O] [IsDomain O] [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module O V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul O V] (ρ : Representation O G V)
    (hb : ∀ c : O, c ≠ 0 → Function.Bijective fun v : V => c • v) :
    Module.IsTorsionFree O (H1 ρ) := by
  refine ⟨fun r hr => ?_⟩
  have hr0 : r ≠ 0 := hr.ne_zero
  have key : ∀ x : H1 ρ, r • x = 0 → x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      intro h
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 h
      obtain ⟨m', hm'⟩ := (hb r hr0).2 m
      rw [Submodule.Quotient.mk_eq_zero]
      refine (mem_coboundaries1 ρ _).2 ⟨m', fun g => (hb r hr0).1 ?_⟩
      have h1 : r • z.1 g = ρ g m - m := hm g
      show r • z.1 g = r • (ρ g m' - m')
      have hm'' : r • m' = m := hm'
      rw [h1, smul_sub, ← map_smul, hm'']
  intro x y hxy
  have hxy' : r • x = r • y := hxy
  have : r • (x - y) = 0 := by rw [smul_sub, hxy', sub_self]
  exact sub_eq_zero.1 (key _ this)

theorem propLocCont_of (hConn : StatConnTors.{u}) (hEmb : StatQuotEmbeds.{u})
    (hDual : StatDualLattice.{u}) : StatPropLocCont.{u} := by
  intro O G VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D HfV HfV' ℓ e' ι₁ ι₂ P Q
    hT hperf hfin hc hBK hP hQ
  have h1 := hDual O G VT VT' D.ε D.ρT D.ρT' D.bT D.T hT D.stT hperf D.eqT
  have hT' : IsLatticeIn D.T' := h1.1
  have hrk : Module.finrank O D.T' = Module.finrank O D.T := h1.2.1
  obtain ⟨e, he⟩ : ∃ e : (VT' ⧸ D.T') →ₗ[O] (Fin (Module.finrank O D.T) → KO O),
      Function.Injective e := hrk ▸ (hEmb O VT' D.T' hT').2
  have htf : Module.IsTorsionFree O (H1 D.ρT') := h_one_torsion_free D.ρT' (fun c hc => smul_bij c hc)
  have a1 : ∀ a : VT' ⧸ D.T', ∃ c : O, c ≠ 0 ∧ c • a = 0 := by
    intro a
    obtain ⟨c, hc, h⟩ := pi_torsion (e a)
    refine ⟨c, hc, he ?_⟩
    rw [map_smul, h, map_zero]
  have a2 : LinearMap.ker D.T'.mkQ = LinearMap.range D.T'.subtype := by
    rw [Submodule.ker_mkQ, Submodule.range_subtype]
  have a3 : ∀ (g : G) (m : D.T'), D.T'.subtype (D.ρTl' g m) = D.ρT' g (D.T'.subtype m) :=
    fun _ _ => rfl
  have a4 : ∀ (g : G) (m : VT'), D.T'.mkQ (D.ρT' g m) = D.ρA' g (D.T'.mkQ m) := fun _ _ => rfl
  have a5 : Topology.IsEmbedding D.T'.subtype := Topology.IsEmbedding.subtypeVal
  have hC := hConn O G D.T' VT' (VT' ⧸ D.T') D.ρTl' D.ρT' D.ρA' D.T'.subtype D.T'.mkQ
    a5 a3 a4 (Submodule.mkQ_surjective _) a2 D.contT' (fun c hc => smul_bij c hc) a1
  obtain ⟨δ, hδ⟩ := hC
  let ι : H0 D.ρA' →ₗ[O] (Fin (Module.finrank O D.T) → KO O) := e ∘ₗ (H0 D.ρA').subtype
  have hι : Function.Injective ι := he.comp (Submodule.injective_subtype _)
  let δ' : LinearMap.range ι →ₗ[O] H1 D.ρTl' := δ ∘ₗ (LinearEquiv.ofInjective ι hι).symm.toLinearMap
  have hδ' : LinearMap.range δ' = Submodule.torsion O (H1 D.ρTl') := by
    rw [← hδ]
    exact LinearEquiv.range_comp _ _
  have main := propLoc O (H1 D.ρA) (H1 D.ρT) (H1 D.ρTl') (H1 D.ρT') D.q D.j' D.pr HfV HfV' ℓ e'
    (Module.finrank O D.T) (LinearMap.range ι) δ' ι₁ ι₂ (fun i => (P i).toDirect)
    (fun i => (Q i).toDual hc) hBK hδ' hP hQ
  refine ⟨main.1, main.2.1, ?_⟩
  exact main.2.2

end Formalism.RepresentationBoundsCohomology.LOC
