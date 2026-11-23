import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinAddSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishRealOfVanishInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatModelNumeratorBoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt

namespace GlobalTheory.FlatDetModel

theorem sum_gen {D : D7} {Y : Formalism.BasicNotions.DV.ShimX D.what₂.Tau} (T : Real0 Y) (B : ℝ) (c : Y.Comp) (m : ℕ) (w : Wt Y) :
    ∑ i : Option (D.what₂.Tau × Fin Y.N), (i.elim 0 fun x => w x.1 x.2) • T.gen B c m i = T.L B c w := by
  rw [Fintype.sum_option]
  simp only [Option.elim, zero_smul, zero_add, Real0.gen]
  simp_rw [← map_smul]
  rw [← map_sum]
  · congr 1
    ext σ i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single σ, Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb.symm]
    · simp
    · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
    · simp

theorem lin_elim {ι : Type} [Fintype ι] (b : ι → ℝ) :
    lin (fun o : Option ι => o.elim 0 b) = rename some (lin b) := by
  simp [lin, map_sum, Fintype.sum_option]

theorem num_eq_htDetT_mul_int : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → OnObj fun D O _ T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ (τ : D.what₂.Tau) c (g : (T.M c).Fun),
    (T.M c).Smooth g →
    (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) →
    ∀ u : Wt O.Y, (T.K B c).num (Fin.cons (T.L B c (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) + (T.K B c).ar g)
        fun _ => T.L B c u) =
      (T.M c).int (fun _ => (T.K B c).c1 (T.L B c u)) (fun _ _ => O.Y.htDetT B c τ) := by
  intro hXH hP hH hS D O hO hf A T H h B hB τ c g hg hgph u
  obtain ⟨ε, π, hd⟩ := (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.exists_isDown (h.man c)
  set t := O.Y.htDetT B c τ with ht
  set f : (T.M c).Fun := g - (fun _ _ => t : (T.M c).Fun) with hfdef
  have hfs : (T.M c).Smooth f := fun σ j => (hg σ j).sub contDiffOn_const
  have hfs2 : (T.M c).Smooth ((2 : ℝ) • f) := fun σ j => (hfs σ j).const_smul (2 : ℝ)
  have hu := GlobalTheory.Mean4O.OnModelCInf.cInfAt_pull _ _ _ _ _ (h.man c) ε π hd _ hfs2
  have hc := GlobalTheory.HomChgConj.isConj_pull D O hO A T H h c _ g hg hgph _ ε π hd t
  have hdim : (O.var c).dim = Formalism.MainNotions.WeightThresholdDefs.dimY O.Y := (O.dim_eq c).trans rfl
  have hX : IsArithVar (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) :=
    hdim ▸ (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.ar
  obtain ⟨Φ, hΦ⟩ := ((hP.p4.arExists _ _ _ _ hX).2 _
    (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • f)) hu hc)
      ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B)))).1
  have hN := h.num B hB c ε π hd f hfs hu hc Φ hΦ
  have hpol := GlobalTheory.PolarNum.num_cons_eq (T.K B c) _ ((T.K B c).ar f) Φ _ (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.ν_pos.ne' hN
    (fun o => o.elim 1 fun o' => o'.elim 0 fun x => (fun σ' (_ : Fin O.N) => if σ' = τ then (-1 : ℝ) else 0) x.1 x.2)
    (fun o => o.elim 0 fun o' => o'.elim 0 fun x => u x.1 x.2)
  simp only [Option.elim_some, Option.elim_none] at hpol
  erw [sum_gen T B c (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).mult (fun σ' (_ : Fin O.N) => if σ' = τ then (-1 : ℝ) else 0),
    sum_gen T B c (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).mult u] at hpol
  rw [one_smul, zero_smul, add_zero] at hpol
  have h0 : Φ (lin (fun o => o.elim 1 fun o' => o'.elim 0 fun x => (fun σ' (_ : Fin O.N) => if σ' = τ then (-1 : ℝ) else 0) x.1 x.2) *
      lin (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim 0 fun o' => o'.elim 0 fun x => u x.1 x.2) ^ Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) = 0 := by
    rw [lin_elim]
    exact GlobalTheory.IntRealPow.vanish_real_of_vanish_int Φ _ _ (GlobalTheory.T.flat_model_numerator_bound hXH hP hH hS D O hO hf A T H h B hB τ c g hg hgph ε π hd hu hc Φ hΦ) _
  rw [h0, zero_div] at hpol
  have har : (T.K B c).ar g = (T.K B c).ar f + (T.K B c).ar (fun _ _ => t : (T.M c).Fun) := by
    rw [← map_add, hfdef, sub_add_cancel]
  rw [har, ← add_assoc, MultilinearMap.cons_add]
  erw [hpol]
  rw [zero_add]
  exact (T.K B c).num_ar _ (fun σ => st_smooth_const _ t) _

end GlobalTheory.FlatDetModel
