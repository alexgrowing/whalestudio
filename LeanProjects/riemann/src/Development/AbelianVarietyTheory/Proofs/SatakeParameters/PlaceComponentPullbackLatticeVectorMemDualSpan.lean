import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

namespace GlobalTheory.AwayLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem prV_pullV_mem_latS_dual : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ latAd x.1 lev.Lb →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  intro D i hi T f bad lev x v l hl
  have hmono : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) lev.Lb ≤
      latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) :=
    Submodule.span_mono (Set.image_mono fun y hy => Submodule.subset_span (lev.Lb_int y hy))
  apply hmono
  induction hl using Submodule.span_induction with
  | mem y hy => exact Formalism.L2.Geo.Def.PN.prV_latS lev.Lb v hy
  | zero =>
    have : (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 (0 : Fin (D.R.N i) → D.host.E) k)) = 0 := by
      ext k
      have h0 : pullV (F := D.host.F) x.1 (0 : Fin (D.R.N i) → D.host.E) = 0 := by
        have := pullV_add (F := D.host.F) x.1 (0 : Fin (D.R.N i) → D.host.E) 0
        funext j
        have hj := this j
        rw [add_zero] at hj
        simpa using hj
      rw [h0, Pi.zero_apply, map_zero, Pi.zero_apply]
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 (a + b) k)) =
        (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 a k)) +
          (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 b k)) := by
      ext k
      rw [Pi.add_apply, pullV_add, map_add]
    rw [this]; exact add_mem ha hb
  | smul c a _ ha =>
    have hc : inclE (F := D.host.F) (v.adicCompletion D.host.F) (algebraMap (𝓞 D.host.E) D.host.E c) ∈ intV D.host.E v :=
      Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 D.host.E) D.host.E c, ⟨c, rfl⟩⟩, rfl⟩)
    have : (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 (c • a) k)) =
        (⟨_, hc⟩ : intV D.host.E v) • (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 a k)) := by
      ext k
      rw [pullV_osmul, map_mul]
      rfl
    rw [this]; exact Submodule.smul_mem _ _ ha

end GlobalTheory.AwayLat
