import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsSumToVolumeProportionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqOfLeviEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyRegularityCauchyEstimate
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesA
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.GenDeg

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

theorem mInt_const_shift {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (θ : LocPot X) (hθ : IsPotential A θ) (f : X → ℝ) (hf : A.Smooth f) (a : ℝ) :
    mInt A (fun _ => θ + LocPot.ofFun f) (fun _ => a) = a * mInt A (fun _ => θ) (fun _ => 1) := by
  have hp : IsPotential A (θ + LocPot.ofFun f) := isPotentialAdd A _ _ hθ (isPotential_ofFun A f hf)
  have h1 := mIntLinear A (fun _ => θ + LocPot.ofFun f) (fun _ => hp) a (fun _ => 1) (fun _ => 0)
    (mIntegrableCont A _ (fun _ => hp) _ continuous_const) (mIntegrableCont A _ (fun _ => hp) _ continuous_const)
  simp only [mul_one, add_zero, st_mInt_zero] at h1
  rw [h1, massIndep A (fun _ => θ) (fun _ => f) (fun _ => hθ) (fun _ => hf)]

theorem c1_add_ar_leviEq {e : ℕ} {M : Man e} (K : Calc M) (v : K.V) (f : M.Fun) (hf : M.Smooth f) (σ : Fin (M.n + 1))
    {P : LocPot (M.X σ)} (hP : IsPotential (M.A σ) P) (hv : LeviEq (M.A σ) (K.c1 v σ) P) :
    LeviEq (M.A σ) (K.c1 (v + K.ar f) σ) (P + LocPot.ofFun (f σ)) := by
  intro j y hy w
  have l := fun x => Cauchy.loc_pot (K.firstChern_isPotential x σ)
  rw [K.isOneCochain_add _ _ σ j y hy w, Cauchy.leviAt_add (l _) (l _) j hy, K.c1_ar f hf σ j y hy w, hv j y hy w,
    Cauchy.leviAt_add (Cauchy.loc_pot hP) (Cauchy.loc_fun (hf σ)) j hy]

theorem main : Hypotheses2 → HypothesesH → OnObj fun D O A T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ c (u : Wt O.Y) (f : (T.M c).Fun),
    (T.M c).Smooth f → ∀ a : ℝ,
      (T.M c).int (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar f)) (fun _ _ => a) =
        a * (A.w c * Formalism.DegreeFormula.flagDeg D.what₂.Tau O.Y.N u) := by
  intro h2 hH D O hc hf A T H hR B _ c u f hfs a
  have h4 := ((GlobalTheory.T.weights_sum_to_volume_proportional h2 hH D O hc hf A T H hR).1 c).2 u
  rw [← h4]
  have hσ : ∀ σ, mInt ((T.M c).A σ) (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar f) σ) (fun _ => a) =
      a * mInt ((T.M c).A σ) (fun _ => (T.F c).th u σ) (fun _ => 1) := by
    intro σ
    have hθ := T.th_pot c u σ
    have hp : IsPotential ((T.M c).A σ) ((T.F c).th u σ + LocPot.ofFun (f σ)) :=
      isPotentialAdd _ _ _ hθ (isPotential_ofFun _ _ (hfs σ))
    rw [(GlobalTheory.LeviOnly.mInt_eq_of_leviEq _ _ _ _ _ _ (fun _ => (T.K B c).firstChern_isPotential _ σ) (fun _ => hp)
      (fun _ => c1_add_ar_leviEq (T.K B c) _ f hfs σ hθ (T.c1_L B c u σ))).1]
    exact mInt_const_shift _ _ hθ _ (hfs σ) a
  simp only [Man.int, hσ, ← Finset.mul_sum]
  ring

end GlobalTheory.GenDeg
