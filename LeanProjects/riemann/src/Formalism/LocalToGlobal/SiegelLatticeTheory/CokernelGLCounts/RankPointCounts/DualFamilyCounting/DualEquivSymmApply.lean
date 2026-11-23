import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExtensionIdentityOfMemCompl

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_dual {Y : Type} [AddCommGroup Y] [Module K Y] [Module (𝓞 K) Y] [IsScalarTower (𝓞 K) K Y]
    {B : Y →ₗ⋆[K] Y →ₗ[K] K} {L : Submodule (𝓞 K) Y} {x : Y} :
    x ∈ Formalism.HermitianLatticesTheory.dual B L ↔ ∀ y ∈ L, B y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}

theorem push_dualIn (L : Submodule (𝓞 K) ↥X) :
    push X (dualIn (formOn h X) ⊤ L) = dualIn h X (push X L) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, mem_dual.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact mem_dual.mp hx.2 y hy
  · rintro ⟨hvX, hv⟩
    refine ⟨⟨v, hvX⟩, ⟨by simp, mem_dual.mpr fun y hy => ?_⟩, rfl⟩
    exact mem_dual.mp hv _ (coe_mem_push.mpr hy)

variable {𝔭 : Ideal (𝓞 F)}

theorem map_incl_dual (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    (locF 𝔭 (dualIn (formOn h X) ⊤ L)).map (incl X) = locF 𝔭 (dualIn h X (push X L)) := by
  change push X _ = _
  rw [push_locF X hp, push_dualIn]

def dualEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L)) ≃ₗ[𝓞 K] ↥(locF 𝔭 (dualIn h X (push X L))) :=
  (Submodule.equivMapOfInjective (incl X) (incl_injective X) _).trans
    (LinearEquiv.ofEq _ _ (map_incl_dual hp L))

theorem dualEquiv_apply (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (x : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) :
    ((dualEquiv (h := h) hp L x : ↥(locF 𝔭 (dualIn h X (push X L)))) : V) = ((x : ↥X) : V) := rfl

theorem dualEquiv_symm_apply (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (y : ↥(locF 𝔭 (dualIn h X (push X L)))) :
    ((((dualEquiv (h := h) hp L).symm y : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) : ↥X) : V) = (y : V) := by
  have := dualEquiv_apply hp L ((dualEquiv (h := h) hp L).symm y)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem map_dualEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    ((locF 𝔭 L).comap (locF 𝔭 (dualIn (formOn h X) ⊤ L)).subtype).map
        (dualEquiv (h := h) hp L : _ →ₗ[𝓞 K] _) =
      (locF 𝔭 (push X L)).comap (locF 𝔭 (dualIn h X (push X L))).subtype := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext y
  simp only [Submodule.mem_comap, Submodule.subtype_apply]
  rw [← coe_mem_push (X := X), push_locF X hp]
  exact Iff.of_eq (congrArg (fun v => v ∈ locF 𝔭 (push X L)) (dualEquiv_symm_apply (h := h) hp L y))

def discEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    DiscMod (formOn h X) ⊤ L 𝔭 ≃ₗ[𝓞 K] DiscMod h X (push X L) 𝔭 :=
  Submodule.Quotient.equiv _ _ (dualEquiv (h := h) hp L) (map_dualEquiv (h := h) hp L)

theorem discEquiv_mk (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (x : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) :
    discEquiv (h := h) hp L (Submodule.Quotient.mk x) = Submodule.Quotient.mk (dualEquiv (h := h) hp L x) := rfl

theorem discEquiv_symm_mk (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (y : ↥(locF 𝔭 (dualIn h X (push X L)))) :
    (discEquiv (h := h) hp L).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y) := rfl

def endEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    Module.End (𝓞 K) (DiscMod (formOn h X) ⊤ L 𝔭) ≃ Module.End (𝓞 K) (DiscMod h X (push X L) 𝔭) where
  toFun P := (discEquiv (h := h) hp L : _ →ₗ[𝓞 K] _) ∘ₗ P ∘ₗ ((discEquiv (h := h) hp L).symm : _ →ₗ[𝓞 K] _)
  invFun P := ((discEquiv (h := h) hp L).symm : _ →ₗ[𝓞 K] _) ∘ₗ P ∘ₗ (discEquiv (h := h) hp L : _ →ₗ[𝓞 K] _)
  left_inv P := by
    apply LinearMap.ext
    intro z
    simp
  right_inv P := by
    apply LinearMap.ext
    intro z
    simp

theorem discAut_push (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    discAut h X (push X L) 𝔭 = discAut (formOn h X) ⊤ L 𝔭 := by
  unfold discAut
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv (endEquiv (h := h) hp L) ?_)
  intro P
  constructor
  · intro H x y x' y' hx hy
    have hx' : Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm x') =
        P (Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm x)) := by
      rw [← discEquiv_symm_mk, hx, ← discEquiv_symm_mk]
      change (discEquiv (h := h) hp L).symm ((discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm _))) = _
      rw [LinearEquiv.symm_apply_apply]
    have hy' : Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y') =
        P (Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y)) := by
      rw [← discEquiv_symm_mk, hy, ← discEquiv_symm_mk]
      change (discEquiv (h := h) hp L).symm ((discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm _))) = _
      rw [LinearEquiv.symm_apply_apply]
    have := H _ _ _ _ hx' hy'
    simpa only [formOn_apply, dualEquiv_symm_apply] using this
  · intro H x y x' y' hx hy
    have hx' : Submodule.Quotient.mk (dualEquiv (h := h) hp L x') =
        (endEquiv (h := h) hp L P) (Submodule.Quotient.mk (dualEquiv (h := h) hp L x)) := by
      change _ = (discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm (Submodule.Quotient.mk _)))
      rw [discEquiv_symm_mk, LinearEquiv.symm_apply_apply, ← hx, discEquiv_mk]
    have hy' : Submodule.Quotient.mk (dualEquiv (h := h) hp L y') =
        (endEquiv (h := h) hp L P) (Submodule.Quotient.mk (dualEquiv (h := h) hp L y)) := by
      change _ = (discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm (Submodule.Quotient.mk _)))
      rw [discEquiv_symm_mk, LinearEquiv.symm_apply_apply, ← hy, discEquiv_mk]
    have := H _ _ _ _ hx' hy'
    simpa only [formOn_apply, dualEquiv_apply] using this

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
