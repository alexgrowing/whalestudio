import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices

noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem datLoc_of_move : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : HomE D.host.E a b → ℂ) (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E), e * star e = 1 → e' * star e' = 1 → DatLoc D cc SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) → DatLoc D cc SS cl N N' Ξ := by
  intro D cc a b SS cl N N' Ξ e e' he he' h x x' hx
  have hs : star e * e = 1 := mul_eq_one_comm.1 he
  have hs' : star e' * e' = 1 := mul_eq_one_comm.1 he'
  have hRR : ∀ y : HomE D.host.E a b, Matrix.toLin' (star e') ∘ₗ (KerMove.RR (star e) (star e') y) ∘ₗ Matrix.toLin' e = y := by
    intro y
    refine LinearMap.ext fun v => ?_
    simp only [KerMove.RR_apply, LinearMap.comp_apply, star_star]
    rw [← LinearMap.comp_apply (Matrix.toLin' (star e')) (Matrix.toLin' e'), ← Matrix.toLin'_mul, hs', Matrix.toLin'_one,
      LinearMap.id_apply, ← LinearMap.comp_apply (Matrix.toLin' (star e)) (Matrix.toLin' e), ← Matrix.toLin'_mul, hs,
      Matrix.toLin'_one, LinearMap.id_apply]
  have key := h (KerMove.RR (star e) (star e') x) (KerMove.RR (star e) (star e') x') (fun P hP => by
    have h1 := KerMove.localization_map₂ (D := D) (KerMove.RR (star e) (star e')) _ _
      (fun z hz => KerMove.perO_map (aaOf D cc) N (SDLat.smulLat e N) N' (SDLat.smulLat e' N') (KerMove.RR (star e) (star e'))
        (fun w hw => KerMove.homO_RR_inv e e' he N N' w hw) z hz) P _ (hx P hP)
    rwa [map_smul, map_sub] at h1)
  simpa only [hRR] using key

end GlobalTheory.TwV

end
