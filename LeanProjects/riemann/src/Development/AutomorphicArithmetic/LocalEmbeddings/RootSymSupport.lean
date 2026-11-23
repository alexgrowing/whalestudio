import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ImaginaryRootNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousLinPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeComparisonRootMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeOfInducedBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsSumToVolumeProportional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedLinearStatement
import Formalism.DegreeFormula.PointDegree.PowSum

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.SwapTrue GlobalTheory.CoverNorm GlobalTheory.ProjVar

namespace GlobalTheory.BcRead

section Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem norms_shift {V : Cover Y} {N : HermLB V.p} {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V N f a l) (t : ℝ) :
    Norms V (N.shift (fun _ => t) fun _ => rfl) f (fun σ y => a σ y - t) l := by
  obtain ⟨r, h₁, h₂, h₃, h₄⟩ := h
  refine ⟨r, h₁, h₂, fun σ z y y' i e₁ e₂ hi => ?_, h₄⟩
  have := h₃ σ z y y' i e₁ e₂ hi
  change a σ y - t = _ - ((N.φ _).φ (i PUnit.unit) y' + 2 * t) / 2
  rw [this]
  ring

theorem gdeg_eq (hA : ArCalc) (V : Cover Y) (M : TrueGeo.Model Y)
    (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) {N : HermLB V.p} {N₀ : HermLB M.p} {f : Y.X → Y.Fn}
    {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ} {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ}
    (h : Norms V N f a l) (h₀ : Norms (Cover.ofModel M hM) N₀ f a l) : gdeg N Y.dim = V.deg * gdeg N₀ Y.dim := by
  have := M.ar.isIntegral
  obtain ⟨η, hη⟩ := (hA.arExists _ V.X V.p Y.dim V.ar).1 N
  obtain ⟨η₀, hη₀⟩ := (hA.arExists _ M.X M.p Y.dim M.ar).1 N₀
  have e₁ := GlobalTheory.ArSelfObj.selfInter_eq hA V M hM h h₀ ⟨η, hη, rfl⟩ ⟨η₀, hη₀, rfl⟩
  have e₂ := GlobalTheory.ArSelfObj.selfInter_eq hA V M hM (norms_shift h 1) (norms_shift h₀ 1)
    (hA.arShift _ V.X V.p Y.dim V.ar N _ 1 ⟨η, hη, rfl⟩) (hA.arShift _ M.X M.p Y.dim M.ar N₀ _ 1 ⟨η₀, hη₀, rfl⟩)
  have hd : ((Y.dim : ℝ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hd
  linear_combination e₂ - e₁

theorem gdeg_comb (hA : ArCalc) {C : CxSt F} (V : Cover Y) (P : TrueGeo.Model Y)
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme P.X) {ι : Type} [Fintype ι] (A : ι → Adl C Y) (L : ι → HermLB P.p) (m : ℕ+)
    (hL : ∀ i, (A i).Induced P (L i) m 0) (N : ι → HermLB V.p) (hN : ∀ i, V.Induces (A i) (N i) 1) (n : ι → ℤ) :
    gdeg (comb N fun i => ((m : ℕ) : ℤ) * n i) Y.dim = V.deg * gdeg (comb L n) Y.dim := by
  have hN' : ∀ i, Norms V (N i) (fun x => genAt (A i).D x) (fun σ y => lnAdl (A i) σ y) fun v e' y => (A i).lg v e' y :=
    fun i => (norms_of_induces (hN i)).congr (fun x => pow_one _) (fun σ y => by simp) fun v e' y => by simp
  have n₀ := fun i => norms_of_induces (Cover.induces_ofModel hP (hL i))
  have n₁ := (norms_comb hN' fun i => ((m : ℕ) : ℤ) * n i).congr
      (f' := fun x => ∏ i, (genAt (A i).D x ^ (m : ℕ)) ^ n i)
      (a' := fun σ y => ∑ i, (n i : ℝ) * ((m : ℕ) * lnAdl (A i) σ y))
      (l' := fun v e y => ∑ i, (n i : ℝ) * ((m : ℕ) * (A i).lg v e y))
      (fun x => Finset.prod_congr rfl fun i _ => by rw [zpow_mul, zpow_natCast])
      (fun σ y => Finset.sum_congr rfl fun i _ => by push_cast; ring)
      (fun v e y => Finset.sum_congr rfl fun i _ => by push_cast; ring)
  exact gdeg_eq hA V P hP n₁ (norms_comb n₀ n)

end Cover

section Expo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def expoHom (Dw : Datum H) : (Pad.Sym E →₀ ℤ) →+ (Letter Dw → ℤ) :=
  AddMonoidHom.mk' (expo Dw) fun w w' => LineTest.expo_add Dw w w'

theorem expo_sum_zsmul {ι : Type} [Fintype ι] (n : ι → ℤ) (w : ι → Pad.Sym E →₀ ℤ) :
    expo Dw (∑ i, n i • w i) = ∑ i, n i • expo Dw (w i) := by
  change expoHom Dw _ = ∑ i, n i • expoHom Dw (w i)
  simp only [map_sum, map_zsmul]

end Expo

theorem rootSym_support {D : D7} (O : Setup D) (Pc : Finset ℕ) (R : ℝ) (x : DV.Rt D.what₂.Tau O.N) :
    ∀ a ∈ (rootSym O.S.Dw (ArIn.ind Pc) (some R) (DV.tauEmb D x.1) x.2).support,
      {q | a.1 q = true}.Finite ∧ a.2.1 = some R := by
  intro a ha
  unfold rootSym at ha
  split_ifs at ha <;>
  · rw [Finsupp.support_single_ne_zero _ (by norm_num)] at ha
    rw [Finset.mem_singleton] at ha
    subst ha
    exact ⟨Pc.finite_toSet.subset fun q hq => by simpa [ArIn.ind] using hq, rfl⟩

theorem inter_roots (hP : Hypotheses2) {D : D7} (O : Setup D) (c : O.s.Comp) (n : D.what₂.Tau × Fin O.N → ℤ) :
    (((O.var c).inter fun _ => ∑ x, n x • divOf (O.Φ.C c) (O.ex x) : ℤ) : ℝ) =
      (O.s.cx O.L O.B O.fl).volC c * degFl D.what₂.Tau O.N (lin (fun x => (n x : ℝ)) ^ dimFl D.what₂.Tau O.N) := by
  have h := GlobalTheory.CompPropObj.interPoly_int (GlobalTheory.T.stronger_published_hypotheses_imply hP).p16 O c fun τ i => -n (τ, i)
  simp only [neg_neg] at h
  rw [← Fin.prod_const, GlobalTheory.ProjVar.Var.interPoly_prod_sum] at h
  refine h.trans ?_
  have hl : linRoot (fun τ i => ((-n (τ, i) : ℤ) : ℝ)) = lin fun x => (n x : ℝ) := by
    simp [linRoot, lin, Finset.sum_neg_distrib]
  rw [← hl]
  rfl

theorem geo_eq (hP : Hypotheses2) (hH : HypothesesH) {D : D7} (O : Setup D) (hC : O.Core) (Pc : Finset ℕ) {R : ℝ} (hR : 2 ≤ R)
    (c : O.s.Comp) (W : BunModel O Pc R c)
    (Ψ : MvPolynomial (Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.N O.j a)) ℝ →ₗ[ℝ] ℝ)
    (hΨ : IsGeoFun (fun z : Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.N O.j a) =>
      VMetric.grLB (W.fl z.1) z.2 ((W.H z.1).pull W.π W.w)) (O.var c).dim Ψ)
    (Q : MvPolynomial (Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.N O.j a)) ℝ) :
    Ψ Q = W.V.ν * (O.s.cx O.L O.B O.fl).volC c *
      degFl D.what₂.Tau O.N (rename (blockEquiv D.what₂.Tau O.N O.j O.indef.2.le) Q) := by
  obtain ⟨xa, _, hcw⟩ := id hC
  have hm : O.met.hm = metsOf xa O.Φ := hcw.hm_eq
  have hdim : (O.var c).dim = dimFl D.what₂.Tau O.N := O.dim_eq c
  let e := blockEquiv D.what₂.Tau O.N O.j O.indef.2.le
  let w : (Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.N O.j a)) → Pad.Sym D.host.E →₀ ℤ := fun z =>
    rootSym O.S.Dw (ArIn.ind Pc) (some R) (DV.tauEmb D (e z).1) (e z).2
  obtain ⟨-, hT⟩ := GlobalTheory.ArTopTrue.arTop_true hP.p4 hH.deg GlobalTheory.ShFam.Pad.HTBound.htBound D O.A O.N O.j O.S O.κ O.s
    xa O.Φ c R hR
  obtain ⟨M, L, m, -, hL, -, -⟩ := hT _ w (fun z => rootSym_support O _ R (e z))
  obtain ⟨P, π, -, hPn, hπ, -, hj, -, -, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating _ (O.var c) M M
  have hL' := fun i => InducedPull.induced_pull _ _ _ _ M P π hπ hj (L i) m 0 (hL i)
  have key : ∀ n : D.what₂.Tau × Fin O.N → ℤ, Ψ (lin (fun z => (n (e z) : ℝ)) ^ dimFl D.what₂.Tau O.N) =
      W.V.ν * (O.s.cx O.L O.B O.fl).volC c * degFl D.what₂.Tau O.N (lin (fun x => (n x : ℝ)) ^ dimFl D.what₂.Tau O.N) := by
    intro n
    have h₁ := gdeg_comb hP.p4 W.V P hPn _ _ m hL' _ (fun z => by have := W.ind z.1 z.2; rw [hm] at this; exact this)
      fun z => n (e z)
    have h₂ := GlobalTheory.ReadModel.gdeg_induced hH.deg _ _ _ _ P _ m 0 (GlobalTheory.T.adelic_divisor_induced_linear D O.A O.N O.j O.S O.κ O.s xa O.Φ c R P _ w _ m
      (fun z a ha => (rootSym_support O _ R (e z) a ha).2) hL' fun z => n (e z))
    have h₃ := hΨ.1 fun z => ((m : ℕ) : ℤ) * n (e z)
    have e₁ : lin (fun z => ((((m : ℕ) : ℤ) * n (e z) : ℤ) : ℝ)) = ((m : ℕ) : ℝ) • lin fun z => (n (e z) : ℝ) := by
      simp [lin, Finset.smul_sum, smul_eq_C_mul, mul_assoc]
    have h₄ : (adlOf (O.Φ.C c) (metsOf xa O.Φ c) (∑ z, n (e z) • w z)).deg =
        (O.s.cx O.L O.B O.fl).volC c * degFl D.what₂.Tau O.N (lin (fun x => (n x : ℝ)) ^ dimFl D.what₂.Tau O.N) := by
      rw [← inter_roots hP O c n]
      have e₂ : divOf (O.Φ.C c) (expo O.S.Dw (∑ z, n (e z) • w z)) = ∑ x, n x • divOf (O.Φ.C c) (O.ex x) := by
        rw [expo_sum_zsmul, ← e.sum_comp]
        simp only [w, expo_rootSym, divOf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.smul_sum,
          mul_smul]
        exact Finset.sum_comm
      simp only [Adl.deg, adlOf, e₂, PNat.one_coe, Nat.cast_one, one_pow, div_one]
    rw [e₁, smul_pow, map_smul, h₁, h₂, h₄, NumberField.RingOfIntegers.rank, hdim] at h₃
    have hm0 : ((m : ℕ) : ℝ) ^ dimFl D.what₂.Tau O.N ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 m.ne_zero)
    apply mul_left_cancel₀ hm0
    rw [← smul_eq_mul, h₃, Cover.ν]
    simp only [adlOf, PNat.one_coe, Nat.cast_one, mul_one]
    ring
  have fin := GlobalTheory.ArInt.Model.eq_zero_of_pow (dimFl D.what₂.Tau O.N)
    (Ψ - (W.V.ν * (O.s.cx O.L O.B O.fl).volC c) • Formalism.L2.Geo.degFlL D.what₂.Tau O.N ∘ₗ (rename e).toLinearMap)
    (fun n => by
      have := key fun x => n (e.symm x)
      simp only [Equiv.symm_apply_apply] at this
      rw [LinearMap.sub_apply, this, LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        Formalism.L2.Geo.degFlL_apply, map_pow, ← rename_lin_comp e]
      simp only [Equiv.symm_apply_apply, smul_eq_mul, sub_self])
    (fun Q d hd hQ => by
      rw [LinearMap.sub_apply, hΨ.2 Q d (hdim ▸ hd) hQ, LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        Formalism.L2.Geo.degFlL_apply, Formalism.DegreeFormula.degreeHomogeneousEqZero _ _ d _ hQ.rename_isHomogeneous hd]
      simp)
  have := LinearMap.congr_fun fin Q
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    Formalism.L2.Geo.degFlL_apply, LinearMap.zero_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.BcRead

end
