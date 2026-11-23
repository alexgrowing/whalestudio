import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesOfCompatibleSystem
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

theorem existsUnique_semiHom_ev (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e)
    (s : SemiHom σ G' G) :
    ∃! φ : Fin d → MvPowerSeries (Fin e) k', ∀ n j, c'.ev n (φ j) = s.app n (c.x n j) := by
  have h := fun j : Fin d => existsUnique_evA_eq_of_presents k' (Fin e) G'.A c'.x c'.nil
    (fun n => (G'.res n : G'.A (n + 1) →ₐ[k'] G'.A n)) c'.res c'.presents
    (fun n => s.app n (c.x n j)) (fun n => by
      change G'.res n (s.app (n + 1) (c.x (n + 1) j)) = _
      rw [s.res_app, c.res])
  choose φ hφ hu using h
  refine ⟨φ, fun n j => hφ j n, fun ψ hψ => funext fun j => hu j (ψ j) fun n => hψ n j⟩

end Katz

end GlobalTheory
