import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSelfIntersectionFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChgEqChgWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenPotentialSmoothPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPotentialTruncation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithClassFormProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelMapSurjectiveBirational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RadicalRootComparison

open GlobalTheory.VertForm GlobalTheory.CoverNorm GlobalTheory.ProjVar

section Calculus

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem fnB_sub_sum_mem_rad (hA : GlobalTheory.Published.ArCalc) (hX : GlobalTheory.IsArithVar p D) {num : VertForm.Form (Cl p) D}
    (hnum : IsArForm D num) {ι : Type} [Fintype ι] (t : ι → ℝ)
    (w : Option ι → ∀ σ : k →+* ℂ, GlobalTheory.CxPts p σ → ℝ) (hu : ∀ o σ y, GlobalTheory.CxPts.CInfAt (w o σ) y)
    (hc : ∀ o σ σ', (GlobalTheory.Weight.ofFun (w o σ)).IsConj (GlobalTheory.Weight.ofFun (w o σ')))
    (hw : ∀ σ y, w none σ y = ∑ i, t i * w (some i) σ y) :
    cl (fnB (w none) (hu none) (hc none)) - ∑ i, t i • cl (fnB (w (some i)) (hu _) (hc _)) ∈ rad num := by
  intro v j
  obtain ⟨N, e, b, hv⟩ := exists_finite_family v
  choose Φ hΦ using fun o : Option ι => ((hA.arExists k X p D hX).2 (Option (Fin N))
    (fun o' : Option (Fin N) => o'.elim (fnB (w o) (hu o) (hc o)) e)).1
  let Λ : Option ι → MvPolynomial (Fin N) ℝ →ₗ[ℝ] ℝ := fun o =>
    Φ o ∘ₗ LinearMap.mulLeft ℝ (MvPolynomial.X none) ∘ₗ (MvPolynomial.rename some).toLinearMap
  have hΛ : ∀ o Q, Λ o Q = Φ o (MvPolynomial.X none * MvPolynomial.rename some Q) := fun _ _ => rfl
  have h₁ : ∀ o, num (Function.update v j (cl (fnB (w o) (hu o) (hc o)))) =
      Λ o (∏ i ∈ Finset.univ.erase j, lin (b i)) := by
    intro o
    let a : Fin (D + 1) → Option (Fin N) → ℝ := fun i o' => if i = j then o'.elim 1 0 else o'.elim 0 (b i)
    have e₁ := hnum _ _ _ (hΦ o) a
    have e₂ : (fun i => ∑ o', a i o' • cl ((fun o' : Option (Fin N) => o'.elim (fnB (w o) (hu o) (hc o)) e) o')) =
        Function.update v j (cl (fnB (w o) (hu o) (hc o))) := by
      funext i
      by_cases hi : i = j
      · subst hi
        simp [a, Fintype.sum_option]
      · simp [a, hi, Fintype.sum_option, hv i]
    rw [← e₂, ← e₁, hΛ, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), map_prod]
    congr 2
    · simp [a, lin, Fintype.sum_option]
    · refine Finset.prod_congr rfl fun i hi => ?_
      simp [a, lin, Fintype.sum_option, Finset.ne_of_mem_erase hi]
  have h₂ : Λ none - ∑ i, t i • Λ (some i) = 0 := by
    refine GlobalTheory.ArInt.Model.eq_zero_of_pow D _ (fun n => ?_) fun P d hd hP => ?_
    · have key := fun o => hA.arMix.fnB hA.arExists hX (hΦ o) n
      have := hX.finite_emb
      let := Fintype.ofFinite (k →+* ℂ)
      simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, hΛ, map_pow, (key _).2, chInt,
        finsum_eq_sum_of_fintype, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [show w none σ = fun y => ∑ i, t i * w (some i) σ y from funext (hw σ)]
      simp only [GlobalTheory.Weight.chernInt]
      rw [MeasureTheory.integral_finsetSum _ fun i _ => ((key (some i)).1 σ).1.const_mul _,
        MeasureTheory.integral_finsetSum _ fun i _ => ((key (some i)).1 σ).2.const_mul _,
        ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      ring
    · have hz : ∀ o, Λ o P = 0 := fun o => (hΦ o).2 _ (1 + d) (by omega)
        ((isHomogeneous_X ℝ none).mul hP.rename_isHomogeneous)
      simp [hz]
  have h₃ := LinearMap.congr_fun h₂ (∏ i ∈ Finset.univ.erase j, lin (b i))
  rw [num.map_update_sub, num.map_update_sum]
  simp only [num.map_update_smul, h₁]
  simpa using h₃

end Calculus

section Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem smul_eq_smul_of_norms (hA : GlobalTheory.Published.ArCalc) {C : CxSt F} (V : Cover Y) (M : GlobalTheory.TrueGeo.Model Y) {ι : Type}
    [Fintype ι] (A : ι → Adl C Y) (L : ι → GlobalTheory.HermLB M.p) (m : ℕ+) (hL : ∀ i, (A i).Induced M (L i) m 0)
    {Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (hΨ : haveI := M.ar.isIntegral; IsArFun L Y.dim Ψ) (N : ι → GlobalTheory.HermLB V.p)
    (hN : ∀ i, Norms V (N i) (fun x => genAt (A i).D x) (fun σ y => lnAdl (A i) σ y) fun v e y => (A i).lg v e y)
    {d : ℕ} (hdim : Y.dim = d) {Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun N d Φ) :
    ((m : ℕ) : ℝ) ^ (d + 1) • Φ = (V.deg : ℝ) • Ψ := by
  subst hdim
  obtain ⟨P, π, -, hP, hπ, -, hj, -, -, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M
  have := M.ar.isIntegral
  have := P.ar.isIntegral
  have hd := (GlobalTheory.ModelBirational.main F Y P M π hπ hj).2
  have hg : π (genericPoint P.X) = genericPoint M.X := by
    rw [← GlobalTheory.ModelBirational.j_genericPoint P, ← GlobalTheory.ModelBirational.j_genericPoint M, ← hj, Scheme.Hom.comp_apply]
  have hΨ' := (hA.arProj _ M.X P.X M.p P.p _ M.ar P.ar π hπ hg (by rw [hd]; exact one_ne_zero)).2 _ L Ψ hΨ
  rw [hd, Nat.cast_one, one_smul] at hΨ'
  have n₀ := fun i => norms_of_induces (Cover.induces_ofModel hP
    (InducedPull.induced_pull F C Y (A i) M P π hπ hj (L i) m 0 (hL i)))
  refine sub_eq_zero.1 (GlobalTheory.ArInt.Model.eq_zero_of_pow (Y.dim + 1) _ (fun n => ?_) fun Q d hd hQ => ?_)
  · have n₁ := (norms_comb hN fun i => ((m : ℕ) : ℤ) * n i).congr
      (f' := fun x => ∏ i, (genAt (A i).D x ^ (m : ℕ)) ^ n i)
      (a' := fun σ y => ∑ i, (n i : ℝ) * ((m : ℕ) * lnAdl (A i) σ y))
      (l' := fun v e y => ∑ i, (n i : ℝ) * ((m : ℕ) * (A i).lg v e y))
      (fun x => Finset.prod_congr rfl fun i _ => by rw [zpow_mul, zpow_natCast])
      (fun σ y => Finset.sum_congr rfl fun i _ => by push_cast; ring)
      (fun v e y => Finset.sum_congr rfl fun i _ => by push_cast; ring)
    have key := GlobalTheory.ArSelfObj.selfInter_eq hA V P hP n₁ (norms_comb n₀ n) (hΦ.1 _) (hΨ'.1 n)
    have e : lin (fun i => ((((m : ℕ) : ℤ) * n i : ℤ) : ℝ)) = ((m : ℕ) : ℝ) • lin fun i => (n i : ℝ) := by
      simp [lin, Finset.smul_sum, smul_eq_C_mul, mul_assoc]
    rw [e, smul_pow, map_smul] at key
    simpa [sub_eq_zero] using key
  · simp [hΦ.2 Q d hd hQ, hΨ.2 Q d hd hQ]

end Cover

section Absorb

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem absorb (hA : GlobalTheory.Published.ArCalc) (hX : GlobalTheory.IsArithVar p D) {ι : Type} [Fintype ι] (t : ι → ℝ)
    (w : Option ι → ∀ σ : k →+* ℂ, GlobalTheory.CxPts p σ → ℝ) (hu : ∀ o σ y, GlobalTheory.CxPts.CInfAt (w o σ) y)
    (hc : ∀ o σ σ', (GlobalTheory.Weight.ofFun (w o σ)).IsConj (GlobalTheory.Weight.ofFun (w o σ')))
    (hw : ∀ σ y, w none σ y = ∑ i, t i * w (some i) σ y) (ρ : ι → GlobalTheory.HermLB p) (E : GlobalTheory.HermLB p)
    {Φ : MvPolynomial (Option (Option ι)) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option (Option ι) => o.elim (fnB (w none) (hu none) (hc none))
      fun o' => o'.elim E fun i => (ρ i).dual) D Φ) {Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ}
    (hΨ : IsArFun (fun i => (ρ i).tens (fnB (w (some i)) (hu _) (hc _)).dual) D Ψ) :
    Φ (lin (fun o => o.elim 1 fun o' => o'.elim 0 t) ^ (D + 1)) = Ψ (lin (fun i => -t i) ^ (D + 1)) := by
  obtain ⟨num, hnum, -⟩ := exists_symm_arForm hA k X p D hX
  obtain ⟨r₁, r₂, -, -⟩ := arForm_rad_rules hA k X p D hX num hnum
  have e₁ := hnum _ _ _ hΦ fun _ o => o.elim 1 fun o' => o'.elim 0 t
  have e₂ := hnum _ _ _ hΨ fun _ i => -t i
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at e₁ e₂
  rw [e₁, e₂]
  refine map_congr_rad num fun _ => ?_
  have h := add_mem (fnB_sub_sum_mem_rad hA hX hnum t w hu hc hw) (sum_mem fun i (_ : i ∈ Finset.univ) =>
    Submodule.smul_mem _ (t i) (add_mem (add_mem (r₂ (ρ i)) (r₂ (fnB (w (some i)) (hu _) (hc _))))
      (r₁ (ρ i) (fnB (w (some i)) (hu _) (hc _)).dual)))
  convert h using 1
  simp only [Fintype.sum_option, Option.elim, one_smul, zero_smul, smul_add, smul_sub, neg_smul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  abel

end Absorb

section Roots

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Hs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum Hs}

theorem parOf_rootSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) : Pad.parOf (rootSym Dw a R τ i) = R := by
  have key (st) (n : ℤ) (hn : n ≠ 0) : Pad.parOf (Finsupp.single (a, R, st) n : Pad.Sym E →₀ ℤ) = R := by
    have h : (Finsupp.single (a, R, st) n : Pad.Sym E →₀ ℤ).support.Nonempty :=
      Finsupp.support_nonempty_iff.2 (Finsupp.single_ne_zero.2 hn)
    rw [Pad.parOf, dif_pos h, Finset.mem_singleton.1 (Finsupp.support_single_subset h.choose_spec)]
  unfold rootSym
  split_ifs <;> exact key _ _ (by norm_num)

theorem sum_rootSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) (f : Pad.Sym E → ℤ → ℝ) (h₀ : ∀ s, f s 0 = 0)
    (h : ∀ st n, f (a, R, st) n = f (a, none, st) n) : (rootSym Dw a R τ i).sum f = (rootSym Dw a none τ i).sum f := by
  unfold rootSym
  split_ifs <;> rw [Finsupp.sum_single_index (h₀ _), Finsupp.sum_single_index (h₀ _), h]

end Roots

open GlobalTheory.ArDegIndep

section Objects

variable {D : D7} {O : Setup D} (hm : ∀ k, Mets (O.Φ.C k) (cxSt D.what₂.LL)) (c : O.s.Comp) (P : Finset ℕ) (R : Option ℝ)
  (x : D.what₂.Tau × Fin O.N)

theorem root_D : (adlOf (O.Φ.C c) (hm c) (rootSym O.S.Dw (ArIn.ind P) R (DV.tauEmb D x.1) x.2)).D = (O.root0 c P x).D := by
  simp only [Setup.root0, Setup.adl0, adlOf, expo_rootSym]

theorem root_lg : (adlOf (O.Φ.C c) (hm c) (rootSym O.S.Dw (ArIn.ind P) R (DV.tauEmb D x.1) x.2)).lg = (O.root0 c P x).lg := by
  funext v e y
  simp only [Setup.root0, Setup.adl0, adlOf, lgOf, expo_rootSym]
  split_ifs
  · congr 2
    exact sum_rootSym _ _ _ _ _ (fun _ => (congrArg (· * _) Int.cast_zero).trans (zero_mul _)) fun _ _ => rfl
  · rfl

theorem root_lnAdl (σ : D.what₂.LL →+* ℂ) (y : Pts (O.var c) σ) :
    lnAdl (adlOf (O.Φ.C c) (hm c) (rootSym O.S.Dw (ArIn.ind P) R (DV.tauEmb D x.1) x.2)) σ y =
      lnAdl (O.root0 c P x) σ y + lnRatio (hm c R σ (O.ex x)) (O.met.h0 c σ (O.ex x)) y := by
  have key (g : Mets (O.Φ.C c) (cxSt D.what₂.LL)) (S : Option ℝ) :
      lnAdl (adlOf (O.Φ.C c) g (rootSym O.S.Dw (ArIn.ind P) S (DV.tauEmb D x.1) x.2)) σ y =
        lnN (g S σ (O.ex x)) (genAt (divOf (O.Φ.C c) (O.ex x)) (under y)) y := by
    have e (n : Pad.Letter O.S.Dw → ℤ) (hn : n = O.ex x) (S' : Option ℝ) (hS : S' = S) :
        lnN (g S' σ n) (genAt (divOf (O.Φ.C c) n) (under y)) y =
          lnN (g S σ (O.ex x)) (genAt (divOf (O.Φ.C c) (O.ex x)) (under y)) y := by
      subst hn hS
      rfl
    refine Eq.trans ?_ (e _ (expo_rootSym O.S.Dw (ArIn.ind P) S _ _) _ (parOf_rootSym (Dw := O.S.Dw) (ArIn.ind P) S (DV.tauEmb D x.1) x.2))
    simp only [lnAdl, adlOf, Pi.zero_apply, mul_zero, sub_zero]
  rw [key, Setup.root0, Setup.adl0, key, lnRatio]
  ring

theorem chgWith_conj (hO : O.Core) (x' : ToroidalCompactificationData O.s) (u : D.what₂.Tau → Fin O.N → ℝ)
    (σ σ' : D.what₂.LL →+* ℂ) (p : Pts (O.var c) σ) (p' : Pts (O.var c) σ') (e : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) :
    chgWith O (metsOf x' O.Φ) c R u σ' p' = chgWith O (metsOf x' O.Φ) c R u σ p := by
  obtain ⟨x₀, P₀, hc⟩ := hO
  have hu : under p' = under p := by
    rw [under, e]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg p.1 (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _))
  refine Finset.sum_congr rfl fun r _ => congrArg _ ?_
  have h₁ : p ∈ GlobalTheory.ProjVar.Var.eqnSet σ (divOf (O.Φ.C c) (O.ex r)) (eqn _ (under p)) := Base.isEqn_eqn _ _
  obtain ⟨k₁, -, -⟩ := GlobalTheory.ShFam.mets_conj _ _ _ _ _ _ _ x' O.Φ c σ σ' (O.ex r) p p' _ e h₁
  obtain ⟨-, k₂, -⟩ := GlobalTheory.ShFam.mets_conj _ _ _ _ _ _ _ x₀ O.Φ c σ σ' (O.ex r) p p' _ e h₁
  rw [hc.h0_eq]
  refine (InterpChgCover.lnRatio_eq_h _ _ p' hu).trans (Eq.trans ?_ (InterpChgCover.lnRatio_eq_h _ _ p rfl).symm)
  exact congrArg₂ (fun a b => Real.log a / 2 - Real.log b / 2) (k₁ R) k₂

theorem smooth_psiOf (hO : O.Core) {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y} (h : O.Reads A T H) (x' : ToroidalCompactificationData O.s) {r : ℝ}
    (hr : 2 ≤ r) (u : D.what₂.Tau → Fin O.N → ℝ) : (T.M c).Smooth (psiOf h x' r u c) := by
  intro a
  obtain ⟨x₀, P₀, hc⟩ := hO
  let I := h.man c
  have h₁ : ∀ n, (metsOf x' O.Φ c (some r) (I.ε a) n).SmoothOn Set.univ := fun n =>
    (GlobalTheory.metsOf_smooth _ _ _ _ _ _ _ x' O.Φ c (I.ε a) n).1 r hr
  have h₀ : ∀ n, (O.met.h0 c (I.ε a) n).SmoothOn Set.univ := fun n => by
    rw [hc.h0_eq]
    exact (GlobalTheory.metsOf_smooth _ _ _ _ _ _ _ x₀ O.Φ c (I.ε a) n).2.1
  have hg : ((O.var c).an (I.ε a)).SmoothOn Set.univ (chgWith O (metsOf x' O.Φ) c (some r) u (I.ε a)) := by
    intro i
    refine (ContDiffOn.sum (s := Finset.univ) fun z _ => (contDiffOn_const (c := u z.1 z.2)).mul
      (GlobalTheory.HodgeChgSmooth.smoothOn_lnRatio (h₁ (O.ex z)) (h₀ (O.ex z)) i)).congr fun v _ => ?_
    simp [chgWith]
  have key := GlobalTheory.HodgeChgSmooth.smoothOn_of_manIs I (O.dim_eq c) a isOpen_univ hg
    (f := psiOf h x' r u c a) fun z _ => rfl
  intro j
  simpa using key j

end Objects

theorem degree_comparison_normalized : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H) (x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s) (B : ℝ), 2 ≤ B → ∀ R : ℝ, Real.exp 2 ≤ R → ∀ (c : O.s.Comp) (u : D.what₂.Tau → Fin O.N → ℝ) (M : GlobalTheory.TrueGeo.Model (O.var c)) (L : D.what₂.Tau × Fin O.N → GlobalTheory.HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial (D.what₂.Tau × Fin O.N) ℝ →ₗ[ℝ] ℝ), (∀ x, (adlOf (O.Φ.C c) (GlobalTheory.ShFam.metsOf x' O.Φ c) (rootSym O.S.Dw (ArIn.ind (GlobalTheory.FlagAr.setB O.Y B)) (some R) (DV.tauEmb D x.1) x.2)).Induced M (L x) m 0) → (haveI := M.ar.isIntegral; IsArFun L (O.var c).dim Ψ) → ∀ (ε : (𝓞 D.what₂.LL →+* ℂ) → Fin ((T.M c).n + 1)) (π : ∀ σ, GlobalTheory.CxPts (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p σ → (T.M c).X (ε σ)), (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.IsDown (h.man c) ε π → ∀ (hu : ∀ σ y, GlobalTheory.CxPts.CInfAt ((T.M c).pull ε π ((2 : ℝ) • psiOf h x' R u c) σ) y) (hc : ∀ σ σ', (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • psiOf h x' R u c) σ)).IsConj (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • psiOf h x' R u c) σ'))) (Φ : MvPolynomial (Option (Option (D.what₂.Tau × Fin O.N))) ℝ →ₗ[ℝ] ℝ), IsArFun (fun o => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • psiOf h x' R u c)) hu hc) ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) (dimY O.Y) Φ → Ψ (linRoot u ^ (dimY O.Y + 1)) / (((m : ℕ) : ℝ) ^ (dimY O.Y + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) = Φ (lin (fun o => o.elim 1 fun o' => o'.elim 0 fun x => u x.1 x.2) ^ (dimY O.Y + 1)) / (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.ν := by
  intro p2 ph D O hO A T H h x' B hB R hR c u M L m Ψ hL hΨ ε π hd hu hc Φ hΦ
  have hA := p2.p4
  have hR2 : (2 : ℝ) ≤ R := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hdim : (O.var c).dim = dimY O.Y := O.dim_eq c
  let W := h.mdl (GlobalTheory.FlagAr.setB O.Y B) c
  have hW : GlobalTheory.IsArithVar W.V.p (dimY O.Y) := hdim ▸ W.V.ar
  let s : D.what₂.Tau × Fin O.N → D.what₂.Tau → Fin O.N → ℝ := fun x τ i => if (τ, i) = x then 1 else 0
  have hs (x σ y) : chgWith O (metsOf x' O.Φ) c (some R) (s x) σ y =
      lnRatio (metsOf x' O.Φ c (some R) σ (O.ex x)) (O.met.h0 c σ (O.ex x)) y := by
    simp [chgWith, s]
  let w : Option (D.what₂.Tau × Fin O.N) → ∀ σ : 𝓞 D.what₂.LL →+* ℂ, GlobalTheory.CxPts W.V.p σ → ℝ := fun o =>
    (T.M c).pull ε π ((2 : ℝ) • psiOf h x' R (o.elim u s) c)
  have hwu : ∀ o σ y, GlobalTheory.CxPts.CInfAt (w o σ) y := fun o =>
    OnModelCInf.cInfAt_pull _ _ _ _ _ (h.man c) ε π hd _ fun σ j =>
      (smooth_psiOf c hO h x' hR2 (o.elim u s) σ j).const_smul (2 : ℝ)
  have hwc : ∀ o σ σ', (GlobalTheory.Weight.ofFun (w o σ)).IsConj (GlobalTheory.Weight.ofFun (w o σ')) := fun o =>
    ArSelfObj.pull_conj hd (g := chgWith O (metsOf x' O.Φ) c (some R) (o.elim u s)) (fun _ _ => rfl)
      (chgWith_conj c (some R) hO x' _)
  have hw : ∀ σ y, w none σ y = ∑ x, u x.1 x.2 * w (some x) σ y := by
    intro σ y
    change 2 * chgWith O _ c _ u _ _ = ∑ x, u x.1 x.2 * (2 * chgWith O _ c _ (s x) _ _)
    simp only [hs]
    rw [chgWith, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  obtain ⟨Θ, hΘ⟩ := ((hA.arExists _ W.V.X W.V.p _ hW).2 _ fun x =>
    (W.root (GlobalTheory.FlagAr.setB O.Y B) x).tens (fnB (w (some x)) (hwu _) (hwc _)).dual).1
  have e₁ := absorb hA hW (fun x => u x.1 x.2) w hwu hwc hw (W.root (GlobalTheory.FlagAr.setB O.Y B)) W.amp hΦ hΘ
  have e₂ := smul_eq_smul_of_norms hA W.V M _ L m hL hΨ _ (fun x => (norms_tens _ _ W.V _ _ _ _ _ _ _ _
    (norms_of_induces (Setup.induces_root0 D O hO.dualRef _ c W _ subset_rfl x))
    (Norms.dual _ _ W.V _ _ _ _ ((norms_triv_fnB _ _ W.V).2 _ (hwu (some x)) (hwc (some x))
      (fun σ y => -chgWith O (metsOf x' O.Φ) c (some R) (s x) σ y) fun σ z y y' h₁ h₂ => by
        rw [show w (some x) _ y' = _ from ArSelfObj.pull_eq hd (g := chgWith O (metsOf x' O.Φ) c (some R) (s x))
          (fun _ _ => rfl) σ z y y' h₁ h₂]
        ring))).congr (fun y => by rw [root_D]; simp) (fun σ y => by rw [root_lnAdl, hs]; simp)
      fun v e y => by rw [root_lg]; simp) hdim hΘ
  have e₃ := LinearMap.congr_fun e₂ (linRoot u ^ (dimY O.Y + 1))
  have e₄ : (lin fun x : D.what₂.Tau × Fin O.N => -u x.1 x.2) = linRoot u := by simp [lin, linRoot]
  rw [e₄] at e₁
  simp only [LinearMap.smul_apply, smul_eq_mul] at e₃
  have hn : (0 : ℝ) < (Module.finrank ℚ D.what₂.LL : ℝ) := Nat.cast_pos.2 Module.finrank_pos
  have hm : (0 : ℝ) < ((m : ℕ) : ℝ) ^ (dimY O.Y + 1) := pow_pos (Nat.cast_pos.2 m.2) _
  have hV : (0 : ℝ) < (W.V.deg : ℝ) := Nat.cast_pos.2 W.V.deg_pos
  refine Eq.trans ?_ (congrArg (· / W.V.ν) e₁.symm)
  rw [Cover.ν, div_eq_div_iff (mul_pos hm hn).ne' (mul_pos hn hV).ne']
  linear_combination -(Module.finrank ℚ D.what₂.LL : ℝ) * e₃

theorem compare_main : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H) (B : ℝ), 2 ≤ B → ∀ R : ℝ, Real.exp 2 ≤ R → ∀ (c : O.s.Comp) (u : D.what₂.Tau → Fin O.N → ℝ) (M : GlobalTheory.TrueGeo.Model (O.var c)) (L : D.what₂.Tau × Fin O.N → GlobalTheory.HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial (D.what₂.Tau × Fin O.N) ℝ →ₗ[ℝ] ℝ), (∀ x, (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind (GlobalTheory.FlagAr.setB O.Y B)) (some R) (DV.tauEmb D x.1) x.2)).Induced M (L x) m 0) → (haveI := M.ar.isIntegral; IsArFun L (O.var c).dim Ψ) → ∀ (ε : (𝓞 D.what₂.LL →+* ℂ) → Fin ((T.M c).n + 1)) (π : ∀ σ, GlobalTheory.CxPts (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p σ → (T.M c).X (ε σ)), (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.IsDown (h.man c) ε π → ∀ (hu : ∀ σ y, GlobalTheory.CxPts.CInfAt ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u) σ) y) (hc : ∀ σ σ', (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u) σ)).IsConj (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u) σ'))) (Φ : MvPolynomial (Option (Option (D.what₂.Tau × Fin O.N))) ℝ →ₗ[ℝ] ℝ), IsArFun (fun o => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u)) hu hc) ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) (dimY O.Y) Φ → Ψ (linRoot u ^ (dimY O.Y + 1)) / (((m : ℕ) : ℝ) ^ (dimY O.Y + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) = Φ (lin (fun o => o.elim 1 fun o' => o'.elim 0 fun x => u x.1 x.2) ^ (dimY O.Y + 1)) / (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.ν := by
  intro p2 ph D O hO A T H h B hB R hR c u M L m Ψ hL hΨ ε π hd
  obtain ⟨x', P, hC⟩ := id hO
  have hR2 : (2 : ℝ) ≤ R := by linarith [Real.add_one_le_exp (2 : ℝ)]
  rw [phR_eq_psiOf h hC hR2 u c]
  rw [hC.hm_eq] at hL
  exact degree_comparison_normalized p2 ph D O hO A T H h x' B hB R hR c u M L m Ψ hL hΨ ε π hd

end GlobalTheory.RadicalRootComparison
