import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbDatum

open GlobalTheory.ConjSeq

theorem frobDR_primPull (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)
    {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (c : primDR B) :
    frobDR p R hR A (primPull (dp0 R) (𝟙 _) f c) = primPull (dp0 R) (𝟙 _) f (frobDR p R hR B c) := by
  have k := (frobMor p R hR B (cast_left p R hR B)).comp (homMor (dp0 R) (𝟙 _) f)
  exact (GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) f) (frobMor p R hR A (cast_left p R hR A)) k (fun _ ↦ rfl)
    (GlobalTheory.VB.frob_naturality p _ f.left _) c).trans
    (GrpMor.pull_pull (frobMor p R hR B (cast_left p R hR B)) (homMor (dp0 R) (𝟙 _) f) k (fun _ ↦ rfl) rfl c).symm

theorem linFrob_isEquivariant : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (A : Over T) [GrpObj A] (i : OAct O A) (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))
    (p : ℕ) [Fact p.Prime] (h0 : (p : Γ(T, ⊤)) = 0) (ρ : O →+* End H) (Ψ : (frobPull p h0).obj H ⟶ H),
    IsDRAct e i ρ → IsLinFrob e p h0 Ψ → IsEquivariant (pullAct ρ (frob T p h0)) ρ Ψ := by
  intro O _ T A _ i H e p _ h0 ρ Ψ hρ hΨ x
  refine frobPull_hom_ext_affine p h0 fun V hV s ↦ (e V hV).injective ?_
  have e1 : (VB.act (pullAct ρ (frob T p h0)) x ≫ Ψ).app V (QCoh.pullbackSections (frob T p h0) H (le_refl V) s) =
      Ψ.app V (QCoh.pullbackSections (frob T p h0) H (le_refl V) ((VB.act ρ x).app V s)) :=
    congrArg (Ψ.app V) (QCoh.pullback_map_app_pullbackSections (frob T p h0) (VB.act ρ x) (le_refl V) s)
  have e2 : (Ψ ≫ VB.act ρ x).app V (QCoh.pullbackSections (frob T p h0) H (le_refl V) s) =
      (VB.act ρ x).app V (Ψ.app V (QCoh.pullbackSections (frob T p h0) H (le_refl V) s)) := rfl
  refine (congrArg (e V hV) e1).trans (Eq.trans ?_ (congrArg (e V hV) e2).symm)
  rw [hΨ V hV, hρ x V hV, hρ x V hV, hΨ V hV]
  haveI := i.hom x
  exact frobDR_primPull p _ (A := onAff A hV) (B := onAff A hV) ((Over.pullback hV.fromSpec).map (i.act x)) _

end GlobalTheory.AbDatum
