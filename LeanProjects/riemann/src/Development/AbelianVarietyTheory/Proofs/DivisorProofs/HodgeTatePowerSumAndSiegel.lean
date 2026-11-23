import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHodgeTateDifferenceKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticMixedVanishingDifferenceStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

open MvPolynomial Formalism.BasicNotions.DV

namespace GlobalTheory.WholeHT

variable {Tau : Type} [Fintype Tau] {N g : ℕ} {Comp : Type} [Fintype Comp]

theorem mixEv_false (I : GlobalTheory.ShFam.Pad.ArIn Tau N g Comp) (S : Finset ℕ) (R : ℝ) (q : ℕ) (c : Comp) (Q : MvPolynomial (Rt Tau N) ℝ) :
    I.mixEv S R q c (X (Sum.inr (false, 2)) * tagDR Tau N Q) =
      C ((Nat.factorial 2 : ℝ)⁻¹) * (∑ l, X (I.whole (Function.update (GlobalTheory.ShFam.Pad.ArIn.ind S) q false) R l c) ^ 2) *
        aeval (fun x => X (I.root (Function.update (GlobalTheory.ShFam.Pad.ArIn.ind S) q false) R x c)) Q := by
  rw [GlobalTheory.ShFam.Pad.ArIn.mixEv, map_mul, aeval_X, tagDR, aeval_rename]
  rfl

theorem mixEv_true (I : GlobalTheory.ShFam.Pad.ArIn Tau N g Comp) (S : Finset ℕ) (R : ℝ) (q : ℕ) (c : Comp) (Q : MvPolynomial (Rt Tau N) ℝ) :
    I.mixEv S R q c (X (Sum.inr (true, 2)) * tagHT Tau N Q) =
      C ((Nat.factorial 2 : ℝ)⁻¹) * (∑ l, X (I.whole (Function.update (GlobalTheory.ShFam.Pad.ArIn.ind S) q true) R l c) ^ 2) *
        aeval (fun x => X (I.root (Function.update (GlobalTheory.ShFam.Pad.ArIn.ind S) q true) R x c)) Q := by
  rw [GlobalTheory.ShFam.Pad.ArIn.mixEv, map_mul, aeval_X, tagHT, aeval_rename]
  rfl

theorem arMix_congr (I : GlobalTheory.ShFam.Pad.ArIn Tau N g Comp) (S S' : Finset ℕ) (R : ℝ) (q q' : ℕ)
    (P P' : MvPolynomial (Vm Tau N) ℝ) (h : ∀ c, I.mixEv S R q c P = I.mixEv S' R q' c P') :
    I.arMix S R q P = I.arMix S' R q' P' := by
  rw [GlobalTheory.ShFam.Pad.ArIn.arMix, GlobalTheory.ShFam.Pad.ArIn.arMix, LinearMap.sum_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun c _ => congrArg (GlobalTheory.ShFam.Pad.numL _ _) (h c)

theorem update_ind_of_not_mem (S : Finset ℕ) (q : ℕ) (h : q ∉ S) : Function.update (GlobalTheory.ShFam.Pad.ArIn.ind S) q false = GlobalTheory.ShFam.Pad.ArIn.ind S := by
  funext r; by_cases hr : r = q
  · subst hr; simp [GlobalTheory.ShFam.Pad.ArIn.ind, h]
  · simp [hr]

theorem update_ind_true (S : Finset ℕ) (q : ℕ) : Function.update (GlobalTheory.ShFam.Pad.ArIn.ind S) q true = GlobalTheory.ShFam.Pad.ArIn.ind (insert q S) := by
  funext r; by_cases hr : r = q
  · subst hr; simp [GlobalTheory.ShFam.Pad.ArIn.ind]
  · simp [GlobalTheory.ShFam.Pad.ArIn.ind, hr]

end GlobalTheory.WholeHT

open GlobalTheory.WholeHT in

theorem GlobalTheory.WholeHT.siegRead {D : D7} (O : Setup D) : SiegRead O.Y := by
  intro T R p hp hpT hT
  have h1T : 1 ∉ T := fun h => Nat.not_prime_one (hT 1 h)
  have h1pT : 1 ∉ insert p T := by
    rw [Finset.mem_insert, not_or]; exact ⟨fun h => Nat.not_prime_one (h ▸ hp), h1T⟩
  have e1 := update_ind_of_not_mem T 1 h1T
  have e2 := update_ind_of_not_mem T p hpT
  have e3 := update_ind_of_not_mem (insert p T) 1 h1pT
  have e4 := update_ind_true T p
  refine ⟨arMix_congr (GlobalTheory.ShFam.Pad.arIn O.s O.Φ O.met.hm) _ _ _ _ _ _ _ fun c => ?_,
    arMix_congr (GlobalTheory.ShFam.Pad.arIn O.s O.Φ O.met.hm) _ _ _ _ _ _ _ fun c => ?_⟩
  · refine (mixEv_false _ _ _ _ _ _).trans ((?_ : _ = _).trans (mixEv_false _ _ _ _ _ _).symm)
    rw [e1, e2]
  · refine (mixEv_false _ _ _ _ _ _).trans ((?_ : _ = _).trans (mixEv_true _ _ _ _ _ _).symm)
    rw [e3, e4]

theorem GlobalTheory.WholeHT.hodge_tate_power_sum_siegel_read :
    Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → OnObj fun _ O _ _ _ _ => PrimeLocalSplitCondition O.Y ∧ SiegRead O.Y := by
  intro h2 hH hR hS D O hO _ A T H h
  refine ⟨fun Sx R hR2 p hp Q => ?_, GlobalTheory.WholeHT.siegRead O⟩
  obtain ⟨c, hc⟩ := GlobalTheory.HTVert.tagDR_sub_tagHT D.what₂.Tau O.Y.N Q
  rw [hc, Finset.mul_sum, map_sum]
  exact Finset.sum_eq_zero fun y _ => GlobalTheory.T.arithmetic_mixed_vanishing_difference h2 hH hR hS D O hO Sx R hR2 p hp y (c y)
