import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatSLatAdIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLattices
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

open Formalism.MainNotions.G.KAat Matrix

namespace GlobalTheory.CompanLocal

theorem mem_latS_dual_of_mem_latCo : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) → IsUnit J.det →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fin N → E), u ∈ latCo sp J crd a x Lb →
    ∃ z : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)),
      z.1 = fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x) u l) := by
  intro R F E _ _ _ _ _ _ N sp J crd a x hx hJ Lb hfin hspan hint v u hu
  set y := bc (prV (E := E) v) x with hy_def
  simp only [latCo, mvL, Submodule.mem_map] at hu
  obtain ⟨w, hw, rfl⟩ := hu
  let locV : (Fin N → E) → (Fin N → E ⊗[F] v.adicCompletion F) := fun z i => inclE (F := F) (v.adicCompletion F) (z i)
  have hcomp : (fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x)
      (((toLE crd : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E) w) l)) =
      ((y⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ locV w := by
    have h1 : pullV (F := F) (ratA F crd * x)
        (((toLE crd : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E) w) =
        ((x⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _) *ᵥ
          (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (w i)) := by
      unfold pullV
      rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv]
      congr 1
      have := bc_mulVec (F := F) crd⁻¹ (toLE crd w)
      refine this.trans ?_
      funext i
      show inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (toLE crd⁻¹ (toLE crd w) i) = _
      rw [toLE_inv_apply']
    rw [h1, GlobalTheory.LocCarry.prV_mulVec, ← GlobalTheory.LocCarry.coe_bc_inv]
    congr 1
  have hlat : latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
  have hL : Submodule.IsLattice E (latAd x Lb) := by
    rw [hlat]; exact Formalism.UG.P.csGlob_lattice Lb hfin hspan x
  have hLb : Submodule.IsLattice E Lb := ⟨Module.Finite.iff_fg.mp hfin, hspan⟩
  have hyU : y ∈ UPts sp.cm.sig J (v.adicCompletion F) := Formalism.UG.P.afsplit_bc_mem _ J v x hx
  have hyl := fun z => GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v z
  have hdm := GlobalTheory.DualCompletion.dual_move F E sp.cm.sig N J v (latAd x Lb) Lb y hJ hL hLb hyU hyl
  have hsub : latS (F := F) (v.adicCompletion F) (intV E v) Lb ≤
      latS (F := F) (v.adicCompletion F) (intV E v) (Formalism.L2.Forms.dualL (sp.cm.sig : E →+* E) J Lb) :=
    Submodule.span_mono (Set.image_mono (fun z hz => Submodule.subset_span (hint z hz)))
  have hmem : ∀ (Λ : Submodule (𝓞 E) (Fin N → E)) z, z ∈ Λ → locV z ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ :=
    fun Λ z hz => Submodule.subset_span ⟨z, hz, rfl⟩
  simp only [compan] at hw
  obtain ⟨w1, hw1, w2, hw2, rfl⟩ := Submodule.mem_sup.1 hw
  have hw2' : w2 ∈ Formalism.L2.Forms.dualL (sp.cm.sig : E →+* E) J (latAd x Lb) := Submodule.smul_le_right hw2
  have hadd : locV (w1 + w2) = locV w1 + locV w2 := by funext i; simp [locV, map_add]
  have key : ((y⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ
      locV (w1 + w2) ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Formalism.L2.Forms.dualL (sp.cm.sig : E →+* E) J Lb) := by
    rw [hadd, Matrix.mulVec_add]
    exact add_mem (hsub ((hyl _).1 (hmem _ _ hw1))) ((hdm _).1 (hmem _ _ hw2'))
  exact ⟨⟨_, key⟩, hcomp.symm⟩

end GlobalTheory.CompanLocal
