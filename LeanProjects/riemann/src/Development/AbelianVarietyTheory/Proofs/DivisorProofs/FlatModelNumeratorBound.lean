import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPhaseSmoothUnitBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPhaseSmoothUnitSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfIntersectionBaseChangeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

namespace GlobalTheory.FlatDetModelNum

theorem lin_single_int {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι) :
    lin (fun i => (((Pi.single j (1 : ℤ) : ι → ℤ) i : ℤ) : ℝ)) = MvPolynomial.X j := by
  simp [lin, Pi.single_apply]

theorem lin_option_elim_int {ι : Type} [Fintype ι] (n : ι → ℤ) :
    lin (fun o : Option ι => (((o.elim 0 n : ℤ)) : ℝ)) = rename some (lin fun i => (n i : ℝ)) := by
  simp [lin, map_sum, Fintype.sum_option]

theorem aeval_single_rename {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℤ) (n : ι → ℤ) :
    (aeval fun j : Option ι => lin fun i => (((j.elim a fun i' => Pi.single i' 1 : ι → ℤ) i : ℤ) : ℝ))
      (rename some (lin fun i => (n i : ℝ))) = lin fun i => (n i : ℝ) := by
  rw [aeval_rename]
  have e : (fun j : Option ι => lin fun i => (((j.elim a fun i' => Pi.single i' 1 : ι → ℤ) i : ℤ) : ℝ)) ∘ some =
      MvPolynomial.X := by
    funext j
    simp only [Function.comp_apply, Option.elim_some]
    exact lin_single_int j
  rw [e, aeval_X_left_apply]

theorem lin_natMul {ι : Type} [Fintype ι] (m : ℕ) (a : ι → ℤ) :
    lin (fun i => (((m : ℤ) * a i : ℤ) : ℝ)) = (m : ℝ) • lin fun i => (a i : ℝ) := by
  simp only [lin, Finset.smul_sum, Int.cast_mul, Int.cast_natCast, map_mul, smul_eq_C_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem flat_model_numerator : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) →
    ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H) (B : ℝ), 2 ≤ B → ∀ (τ : D.what₂.Tau) (c : O.s.Comp)
    (g : (T.M c).Fun), (T.M c).Smooth g →
    (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) →
    ∀ (ε : (𝓞 D.what₂.LL →+* ℂ) → Fin ((T.M c).n + 1))
      (π : ∀ σ, GlobalTheory.CxPts (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p σ → (T.M c).X (ε σ)),
    (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.IsDown (h.man c) ε π →
    ∀ (hu : ∀ σ y, GlobalTheory.CxPts.CInfAt ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ) y)
      (hc : ∀ σ σ', (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ)).IsConj
        (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ')))
      (Φ : MvPolynomial (Option (Option (D.what₂.Tau × Fin O.N))) ℝ →ₗ[ℝ] ℝ),
    IsArFun (fun o => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))) hu hc)
      ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) Φ →
    ∀ n : Option (D.what₂.Tau × Fin O.N) → ℤ,
      Φ (lin (fun o => o.elim 1 fun o' => o'.elim 0 fun x => if x.1 = τ then (-1 : ℝ) else 0) *
        rename some (lin fun i => (n i : ℝ)) ^ Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) = 0 := by
  intro hXH hP hH hS D O hO hf A T H h B hB τ c g hg hgph ε π hd hu hc Φ hΦ n
  have hdim : (O.var c).dim = Formalism.MainNotions.WeightThresholdDefs.dimY O.Y := (O.dim_eq c).trans rfl
  have hX : IsArithVar (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) :=
    hdim ▸ (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.ar
  obtain ⟨m, k', _, _, _, ρ, hρ, M, hm, hM, hiso⟩ := GlobalTheory.T.real_phase_smooth_unit_bound hXH hP hH hS D O hO hf A T H h B hB τ c g hg hgph ε π hd hu hc
  have h0 := GlobalTheory.T.real_phase_smooth_unit_sum hP hH hS D O hO hf A T H h B hB τ c g hg hgph ε π hd hu hc m k' ρ hρ M hm hM hiso
  set L := (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))) hu hc)
      ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) with hL
  set αZ := (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (1 : ℤ) fun o' => o'.elim 0 fun x => if x.1 = τ then (-1 : ℤ) else 0) with hα
  have hΦ' := ((hP.p4.arIso _ _ _ _ hX).2 _ L Φ hΦ).2.2 _
    (fun j : Option (Option (Option (D.what₂.Tau × Fin O.N))) => j.elim (M.pull ρ hρ) fun i => comb L (Pi.single i 1))
    (fun j : Option (Option (Option (D.what₂.Tau × Fin O.N))) => j.elim (fun i => (m : ℤ) * αZ i) fun i => Pi.single i 1)
    (by
      rintro (_ | i)
      · exact hiso
      · exact Isometric.refl _)
  have key := GlobalTheory.T.arith_self_intersection_base_change hP.p4 hH.deg _ _ _ _ hX k' ρ hρ M hM h0 _ (fun i => comb L (Pi.single i 1)) _ hΦ'
    (fun o => o.elim 0 n)
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, map_pow, aeval_X, aeval_single_rename, lin_option_elim_int] at key
  simp only [Option.elim_none] at key
  rw [lin_natMul, smul_mul_assoc, map_smul, smul_eq_mul] at key
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  convert (mul_eq_zero.1 key).resolve_left hm' using 3
  simp only [αZ, lin]
  refine Finset.sum_congr rfl fun o _ => ?_
  rcases o with _ | _ | x <;> simp

end GlobalTheory.FlatDetModelNum
