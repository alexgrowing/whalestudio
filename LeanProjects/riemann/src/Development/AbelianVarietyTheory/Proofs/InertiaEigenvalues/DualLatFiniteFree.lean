import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
open Formalism.RepresentationBoundsCohomology.LOC

namespace GlobalTheory

theorem dualLat_finite_free {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {V V' : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V']
    [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V) :
    IsLatticeIn T → PerfectRight b →
      Module.Finite O (dualLat b T) ∧ Module.Free O (dualLat b T) := by
  classical
  rintro ⟨⟨s, hs⟩, hspan⟩ hb
  have hsT : ∀ x ∈ s, x ∈ T := fun x hx => hs ▸ Submodule.subset_span hx
  have hmem : ∀ (f : dualLat b T) (x : s), ∃ o : O, algebraMap O (FractionRing O) o = b x f :=
    fun f x => Submodule.mem_one.mp (f.2 x (hsT x x.2))
  let g0 : dualLat b T → s → O := fun f x => Classical.choose (hmem f x)
  have hg0 : ∀ f x, algebraMap O (FractionRing O) (g0 f x) = b x f :=
    fun f x => Classical.choose_spec (hmem f x)
  have hinj : Function.Injective (algebraMap O (FractionRing O)) :=
    IsFractionRing.injective O (FractionRing O)
  let g : dualLat b T →ₗ[O] (s → O) :=
    { toFun := g0
      map_add' := fun f f' => by
        funext x; apply hinj
        rw [Pi.add_apply, map_add, hg0, hg0, hg0, Submodule.coe_add, map_add]
      map_smul' := fun c f => by
        funext x; apply hinj
        rw [Pi.smul_apply, smul_eq_mul, map_mul, hg0, hg0, Submodule.coe_smul, map_smul,
          RingHom.id_apply, Algebra.smul_def] }
  have ginj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have h0 : ∀ x ∈ s, b x f = 0 := fun x hx => by
      rw [← hg0 f ⟨x, hx⟩]
      have : g0 f ⟨x, hx⟩ = 0 := congrFun hf ⟨x, hx⟩
      rw [this, map_zero]
    have hT0 : T ≤ LinearMap.ker (b.flip (f : V')) := by
      intro x hx
      rw [← hs] at hx
      refine (Submodule.span_le.mpr ?_ : Submodule.span O (s : Set V) ≤ _) hx
      intro y hy
      simpa using h0 y hy
    let ψ : V →ₗ[FractionRing O] FractionRing O :=
      (b.flip (f : V')).extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O)
    have hψ : ψ = 0 := by
      have : Submodule.span (FractionRing O) (T : Set V) ≤ LinearMap.ker ψ := by
        rw [Submodule.span_le]
        intro x hx
        have := hT0 hx
        simpa [ψ] using this
      rw [hspan, top_le_iff, LinearMap.ker_eq_top] at this
      exact this
    obtain ⟨f0, _, huniq⟩ := hb 0
    have e1 : (f : V') = f0 := huniq _ (fun x => by
      have := congrArg (fun φ => φ x) hψ
      simpa [ψ] using this)
    have e2 : (0 : V') = f0 := huniq _ (fun x => by simp)
    exact Subtype.ext (e1.trans e2.symm)
  have hfin : Module.Finite O (dualLat b T) := Module.Finite.of_injective g ginj
  have htf : Module.IsTorsionFree O (dualLat b T) :=
    Function.Injective.moduleIsTorsionFree g ginj (fun c m => g.map_smul c m)
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

end GlobalTheory
