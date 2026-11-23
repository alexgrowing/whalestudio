import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralCutoffLogDecay
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormPotentialSumSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorRelationIntegralScalingStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.BdClass.bd_form_eq : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D) (x : GlobalTheory.ShFam.ToroidalCompactificationData O.s) (P : PolOf x O.Φ),
    O.CoreWith x P → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (R : O.Reads A T H) (c : O.s.Comp)
    (σ : Fin ((T.M c).n + 1)) (m : (GlobalTheory.TrueGeo.cxSt D.what₂.LL).Met (O.var c) ((R.man c).ε σ) (P.bd c))
    (L : ReciprocityTheory.AnForm.M.LocPot ((T.M c).X σ)), IsPot ((R.man c).pt σ) m L →
    ReciprocityTheory.AnForm.M.IsPotential ((T.M c).A σ) L → ∃ g : (T.M c).X σ → ℝ, ((T.M c).A σ).Smooth g ∧
      LeviEq ((T.M c).A σ) L ((T.F c).th A.dir σ + ((T.F c).a σ).rsmul (-1) + ReciprocityTheory.AnForm.M.LocPot.ofFun g) := by
  intro _ _ D O x P hC A T H R c σ m L hL hLp
  obtain ⟨Qx, hQx, hlx⟩ := (R.an c).th A.dir σ
  obtain ⟨Qa, hQa, hla⟩ := (R.an c).a σ
  obtain ⟨d, kb, ka, kx, hd, hkb, hka, hkx, hrel⟩ := GlobalTheory.T.divisor_relation_integral_scaling P c
  have hdir : A.dir = P.dir := R.aux.dir.trans hC.dir_eq
  have hab : O.met.ab = P.ab := hC.ab_eq
  let Δ : Option (Option (DV.Rt D.what₂.Tau O.N)) → (O.var c).Dv := fun o =>
    o.elim (P.bd c) fun o' => o'.elim (O.met.ab c).D fun x => divOf (O.Φ.C c) (O.ex x)
  let mm : ∀ o, (cxSt D.what₂.LL).Met (O.var c) ((R.man c).ε σ) (Δ o) := fun o => match o with
    | none => m
    | some none => (O.met.ab c).m _
    | some (some x) => O.met.h0 c _ (O.ex x)
  let QQ : Option (Option (DV.Rt D.what₂.Tau O.N)) → LocPot ((T.M c).X σ) := fun o => o.elim L fun o' => o'.elim (Qa ()) Qx
  let kk : Option (Option (DV.Rt D.what₂.Tau O.N)) → ℤ := fun o => o.elim kb fun o' => o'.elim ka kx
  have hrel' : ∑ o, kk o • Δ o = 0 := by
    simp only [Fintype.sum_option, kk, Δ, Option.elim]
    rw [hab, ← add_assoc]
    exact hrel
  have hpot : ∀ o, IsPot ((R.man c).pt σ) (mm o) (QQ o) := by
    intro o; rcases o with _ | _ | x
    exacts [hL, (hQa ()).1, (hQx x).1]
  have hpot' : ∀ o, IsPotential ((T.M c).A σ) (QQ o) := by
    intro o; rcases o with _ | _ | x
    exacts [hLp, (hQa ()).2, (hQx x).2]
  obtain ⟨g0, hg0, hlev⟩ := GlobalTheory.T.levi_form_potential_sum_smooth (R.man c) σ Δ mm QQ kk hpot hpot' hrel'
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  refine ⟨fun z => (d : ℝ)⁻¹ * g0 z, fun j => ?_, fun j y hy w => ?_⟩
  · exact contDiffOn_const.mul (hg0 j)
  have hcd : ContDiffAt ℝ 2 (g0 ∘ ((T.M c).A σ |>.chart j).symm) y :=
    GlobalTheory.ShellMass.smoothOn_contDiffAt isOpen_univ hg0 j hy trivial
  have key := hlev j y hy w
  simp only [Fintype.sum_option, kk, QQ, Option.elim] at key
  have hpa : IsPotential ((T.M c).A σ) (((T.F c).a σ).rsmul (-1)) := isPotentialRsmul _ _ _ (T.a_pot c σ)
  have hpth := T.th_pot c A.dir σ
  rw [GlobalTheory.ShellMass.leviAt_add_ofFun (isPotentialAdd _ _ _ hpth hpa) j hy
      (by simpa [Function.comp_def] using hcd.const_smul ((d : ℝ)⁻¹)) w,
    GlobalTheory.ShellMass.leviAt_add hpth hpa j hy w, GlobalTheory.ShellMass.leviAt_rsmul, hlx j y hy w, hla j y hy w]
  have e1 : levi ((fun z => (d : ℝ)⁻¹ * g0 z) ∘ (((T.M c).A σ).chart j).symm) y w =
      (d : ℝ)⁻¹ * levi (g0 ∘ (((T.M c).A σ).chart j).symm) y w :=
    ReciprocityTheory.AnForm.P.TailChernBound.levi_smul' _ hcd w
  rw [e1, ← key, hkb, hka]
  simp only [hkx, hdir, Finset.univ_unique, Finset.sum_singleton, neg_mul, Finset.sum_neg_distrib, mul_assoc,
    ← Finset.mul_sum, hab]
  field_simp
  ring

end
