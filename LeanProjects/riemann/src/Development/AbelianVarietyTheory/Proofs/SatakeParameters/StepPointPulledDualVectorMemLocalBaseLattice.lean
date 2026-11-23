import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatSLatAdIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

namespace GlobalTheory.ZDual

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}

theorem pullV_dual_mem_latS_gen (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : HeightOneSpectrum (𝓞 F)) (l : Fin N → E) (hl : l ∈ dualSet (σ : E →+* E) J (latAd x Lb)) :
    (fun k => prV (E := E) v (pullV (F := F) x l k)) ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Lb)) := by
  have hU : cT (sigR σ (v.adicCompletion F)) (bc (prV (E := E) v) x).val *
      J.map (inclE (F := F) (v.adicCompletion F)) * (bc (prV (E := E) v) x).val =
      J.map (inclE (F := F) (v.adicCompletion F)) := Formalism.UG.P.afsplit_bc_mem σ J v x hx
  have hy : (fun k => prV (E := E) v (pullV (F := F) x l k)) =
      ((bc (prV (E := E) v) x)⁻¹).val *ᵥ (fun k => inclE (F := F) (v.adicCompletion F) (l k)) := by
    rw [GlobalTheory.LocCarry.coe_bc_inv]
    funext k
    unfold pullV
    rw [RingHom.map_mulVec]
    rfl
  rw [hy]
  refine GlobalTheory.St.G.Dual.bwd_loc σ J hJ.ne_zero Lb ⟨hfin, hspan⟩ v _ fun b hb => ?_
  unfold GlobalTheory.St.G.hR
  have key := Formalism.UG.P.hform_mulVec (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
    (bc (prV (E := E) v) x).val (fun k => inclE (F := F) (v.adicCompletion F) (b k))
    (((bc (prV (E := E) v) x)⁻¹).val *ᵥ (fun k => inclE (F := F) (v.adicCompletion F) (l k)))
  rw [hU, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at key
  rw [← key]
  refine Formalism.L2.G.RelativeIndexFlags.pair_int v σ J (latAd x Lb) l hl _ ?_
  rw [GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v, Matrix.mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨b, hb, rfl⟩

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem pullV_dual_mem_latS : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (latAd x.1 lev.Lb) →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  intro D i hi T f bad lev x v l hl
  exact pullV_dual_mem_latS_gen (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) lev.Lb lev.Lb_fin
    lev.Lb_span x.1 x.2 v l hl

end GlobalTheory.ZDual
