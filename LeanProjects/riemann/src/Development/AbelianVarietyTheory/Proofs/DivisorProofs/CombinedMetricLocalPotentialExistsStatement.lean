import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedMetricLocalPotentialExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.combined_metric_local_potential_exists : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (ι : Type) [Fintype ι] (Mb : Adl (cxSt F) Y) (ρ : ι → Adl (cxSt F) Y) (t : ι → ℝ) (g : ∀ σ, Pts Y σ → ℝ) (a : Fin (M.n + 1)) (Q : ι → LocPot (M.X a)), IsComb Mb ρ t g → (∀ i, IsPot (I.pt a) ((ρ i).m (I.ε a)) (Q i) ∧ IsPotential (M.A a) (Q i)) → (M.A a).Smooth (fun z => g (I.ε a) (I.pt a z)) → ∃ QM : LocPot (M.X a), IsPot (I.pt a) (Mb.m (I.ε a)) QM ∧ IsPotential (M.A a) QM ∧ ∀ j, ∀ y ∈ ((M.A a).chart j).target, ∀ w, leviAt (M.A a) QM j y w = ((Mb.n : ℕ) : ℝ) * (∑ i, t i / (((ρ i).n : ℕ) : ℝ) * leviAt (M.A a) (Q i) j y w + leviAt (M.A a) (LocPot.ofFun fun z => g (I.ε a) (I.pt a z)) j y w) := by
  first | exact @GlobalTheory.CombPot.exists_pot_comb | exact GlobalTheory.CombPot.exists_pot_comb | (intros; apply GlobalTheory.CombPot.exists_pot_comb <;> assumption)
