import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFrames

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LocWeil
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeConj

theorem continuous_cA (D : D7) : Continuous (cA D) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap
  exact this

theorem continuous_alg (D : D7) : Continuous (algebraMap (AF D.host.F) (AE D)) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))

theorem conj_arg (z : ℂ) (hz : z ≠ 0) :
    starRingEnd ℂ z / (‖starRingEnd ℂ z‖ : ℂ) = (z / (‖z‖ : ℂ))⁻¹ := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  rw [Complex.norm_conj, inv_div, div_eq_div_iff hn hz, Complex.conj_mul']
  ring

theorem hecke_conj_res : ∀ (D : D7) (χ : IdC D), IsHeckeChar D χ → IsHeckeChar D (χ.comp (conjId D)) ∧ (∀ τ a, HasInfExp D χ τ a → HasInfExp D (χ.comp (conjId D)) τ (-a)) ∧ IsHeckeCharF D (χ.comp (idF D)) := by
  intro D χ hχ
  refine ⟨⟨hχ.1.comp (Continuous.units_map _ (continuous_cA D)), fun x => ?_⟩, fun τ a h => ?_,
    hχ.1.comp (Continuous.units_map _ (continuous_alg D)), fun a => ?_⟩
  · have e : conjId D (Units.map (incA D).toMonoidHom x) =
        Units.map (incA D).toMonoidHom (Units.map (GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures.cE D).toMonoidHom x) :=
      Units.ext (GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures.cA_inc (x : D.host.E))
    exact (congrArg χ e).trans (hχ.2 _)
  · obtain ⟨n, hn, h0, h1⟩ := h
    refine ⟨-n, by push_cast; rw [hn]; ring, h0, fun θ hθ x hx hτ => ?_⟩
    have hv : ((conjId D x : (AE D)ˣ) : AE D) = cA D (x : AE D) := rfl
    have hi : ∀ τ', θ τ' (infPart D ((conjId D x : (AE D)ˣ) : AE D)) = starRingEnd ℂ (θ τ' (infPart D (x : AE D))) :=
      fun τ' => by rw [hv, GlobalTheory.LocWCompare.infPart_cA, GlobalTheory.LocWCompare.th_conj (hθ τ')]
    have h2 := h1 θ hθ (conjId D x) (by rw [hv, GlobalTheory.LocWCompare.finPart_cA, hx, RingHom.map_one])
      (fun τ' h' => by rw [hi, hτ τ' h', RingHom.map_one])
    have hz : θ τ (infPart D (x : AE D)) ≠ 0 := ((x.isUnit.map (infPart D)).map (θ τ)).ne_zero
    rw [MonoidHom.comp_apply, h2, hi, conj_arg _ hz, _root_.inv_zpow']
  · have e : idF D (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) =
        Units.map (incA D).toMonoidHom (Units.map (algebraMap D.host.F D.host.E).toMonoidHom a) := by
      apply Units.ext
      exact ((Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := AF D.host.F)
        (B := D.host.E)).commutes (a : D.host.F)).trans
        ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes (a : D.host.F)).symm
    exact (congrArg χ e).trans (hχ.2 _)

end GlobalTheory.HeckeConj
