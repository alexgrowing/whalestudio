import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LeadMinorSmulOne
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.RA

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}

theorem rpow_of_sq {n d : ℝ} (hn : 0 < n) (h : n ^ 2 = d) (a : ℤ) : d ^ (-(a : ℝ) / 2) = n ^ (-a) := by
  rw [← h, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_intCast]
  congr 1
  push_cast
  ring

theorem move_pnorm (hσ : GoodEmb c σ) (hU : IsUnf U) {k : U.Comp} (x : (U.X k).dom) :
    ∃ (x₀ : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), (U.X k).IsOrtho x₀.1 ∧ FrBor t (U.un k x₀) (U.un k x) ∧
      ∀ a : WZ E, (U.X k).pnorm (laZ U a k) (fun _ => 1) x.1 =
        ∏ s : Σ τ, Fin (Dw.mult τ), ‖toC (t (some s) : CAt σ)‖ ^ (-a (s.1, s.2)) := by
  obtain ⟨x₀, t, ho, hb, hn⟩ := GF.move hσ hU x
  obtain ⟨f, hf, -⟩ := GF.letters hσ hU k
  obtain ⟨hbij, -, hconj, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  refine ⟨x₀, t, ho, hb, fun a => ?_⟩
  unfold Data.pnorm
  rw [norm_one, one_mul, ← Fintype.prod_prod_type']
  refine (Fintype.prod_equiv f _ _ fun s => ?_).symm
  have hpos : 0 < ‖toC (t (some s) : CAt σ)‖ := norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) (t (some s)))
  have hinv : Function.invFun (relab c σ) (relab c σ s.1) = s.1 := Function.leftInverse_invFun hbij.1 _
  rcases hf s with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4⟩
  · have h1 := (hn s (f s).1 (f s).2).1 a2 a3
    have h2 : laZ U a k (f s).1 (f s).2 = a (s.1, s.2) := by
      unfold laZ
      rw [if_pos (by omega), a2, hinv, a3, Nat.add_sub_cancel_left]
    rw [h2]
    exact (rpow_of_sq hpos h1 _).symm
  · have e1 : conjEmb (f s).1.1 = relab c σ s.1 := by
      rw [a2]; exact ComplexEmbedding.involutive_conjugate E _
    have h1 := (hn s (f s).1 (f s).2).2 e1 (by omega)
    have h2 : laZ U a k (f s).1 (f s).2 = -a (s.1, s.2) := by
      unfold laZ
      rw [if_neg (by omega), e1, hinv, a3]
      congr 3
      omega
    rw [h2]
    have h3 := (inv_pow _ 2).trans ((congrArg (·⁻¹) h1).trans (inv_inv _))
    rw [rpow_of_sq (inv_pos.2 hpos) h3, neg_neg, inv_zpow, zpow_neg]

theorem lieFacZ_eq (Dw : Datum H) {x : ℝ} (hx : 0 < x) (a : WZ E) :
    lieFacZ Dw x a = ∏ s : Σ τ, Fin (Dw.mult τ), Real.sqrt (Real.pi * (2 * x)) ^ (-a (s.1, s.2)) := by
  have hp : 0 < Real.pi * (2 * x) := mul_pos Real.pi_pos (by linarith)
  have e : ∀ s : Σ τ, Fin (Dw.mult τ), Real.sqrt (Real.pi * (2 * x)) ^ (-a (s.1, s.2)) =
      Real.exp (-(a (s.1, s.2) : ℝ) / 2 * Real.log (2 * Real.pi * x)) := fun s => by
    rw [← rpow_of_sq (Real.sqrt_pos.2 hp) (Real.sq_sqrt hp.le), Real.rpow_def_of_pos hp, mul_comm]
    congr 3
    ring
  simp only [e]
  rw [← Real.exp_sum, lieFacZ, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_neg_distrib, Fintype.sum_sigma, neg_div]

theorem prod_root {M : Type} [CommMonoid M] (F : (Σ τ, Fin (Dw.mult τ)) → M) :
    ∏ s, F s = ∏ ρ : RootIx Dw, F (FinRd.labelSig Dw (HodgeCpt.rootIdx Dw ρ)) :=
  (Fintype.prod_bijective _ ((FinRd.labelSig_bijective Dw).comp (FinRd.rootIdx_bijective Dw)) _ _ fun _ => rfl).symm

end PositivityTheory.UnitarySelfGeneration.RA
