import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerVectorBlockTriangularFrameChangeStatement

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem spMap_comp_spMap_same {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (f : R →+* S) (g : S →+* U) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem cell_pt_eq_of_tri (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type)
    [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1))
    (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X)
    (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P))
    (hc : IsCover β s V α c D) (hp : IsPlk β s V α c p0 p h) (k : Type) [Field k] (b b' : B) (w w' : Pm m)
    (ψ : CR m (V b) →+* k) (ψ' : CR m (V b') →+* k) (d : Let m → k)
    (hb : spMap ψ ≫ cbase m (V b) = spMap ψ' ≫ cbase m (V b')) (hd : ∀ z, d z ≠ 0)
    (ht : Tri (fun z => ψ ∘ uvec (c b) w z) (fun z => ψ' ∘ uvec (c b') w' z) d) :
    spMap ψ ≫ h b w = spMap ψ' ≫ h b' w' := by
  have hO : ψ.comp ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) =
      ψ'.comp ((MvPolynomial.C : _ →+* CR m (V b')).comp ((α b').comp β)) := by
    have e := congrArg (· ≫ s) hb
    simp only [cbase, Category.assoc, hc.ovr, spMap_comp_spMap_same] at e
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  refine hp.ext _ _ _ ?_ fun en => ?_
  · rw [Category.assoc, Category.assoc, hp.base, hp.base, hb]
  · obtain ⟨hu, e⟩ := hp.plk b w en
    obtain ⟨hu', e'⟩ := hp.plk b' w' en
    rw [Category.assoc, Category.assoc, e, e', spMap_pt, spMap_pt]
    have hu2 := span_range_comp_eq_top _ hu' ψ'
    have key : ∀ (f g : O →+* k) (v v' : Fin (plN M en.1 + 1) → k) hv hv', f = g → (∃ u : kˣ, v' = u • v) →
        pt f v hv = pt g v' hv' := by
      rintro f g v v' hv hv' rfl hh
      exact (pt_eq_pt_iff f hv hv').2 hh
    refine key _ _ _ _ _ _ hO ⟨Units.mk0 (∏ l, d (en.2.1 l)) (Finset.prod_ne_zero_iff.2 fun l _ => hd _), ?_⟩
    rw [map_plk, map_plk, GlobalTheory.T.pluckerVector_blockTriangular_frame_change T m k M _ _ d en.1 en.2.1 ht en.2.2]
    rfl

end GlobalTheory.FlagEmb
