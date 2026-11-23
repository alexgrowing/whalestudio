import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StrictWeightGrowthBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightThresholdLimitCoefficientsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NefPolarization
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSupBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormDehomRoots

namespace GlobalTheory.CompanionTheory.Ar.Plug

section Alg

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
  ReciprocityTheory.ChartRestriction.G.AI.I1

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem exists_section_of_nef [CharZero Ω] (hIn : PB.Inputs) (y : (Σ k, ι k) → Ω) (D : ℕ) (M : HermLine ι)
    (har : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1)) (hb : Birational y) (hN : Small.IsNefH (mCoordIdeal y) M)
    (hpos : 0 < geomDeg (mCoordIdeal y) M D) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * M.a κ - 1) 1, e ≠ 0 := by
  classical
  have hK : Nonempty K := har.1
  let I : IFamily ℚ ι := fun V _ L => NumbersDVR.intNum ℚ V L
  have hI : IsFieldIntersection I := NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι
  have hDG := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hIn.degree
  obtain ⟨P0, hP0, hsemi⟩ := hN.semipos
  have hsm : IsSmoothHerm M := hsemi.1
  have hgen := NefOnGenericOfSemipos.proof K ι _ P0 M hP0 hsemi
  have hnef : KH.NefOnF I (KH.genIdeal y) M.a := by
    intro W hW hle
    obtain ⟨hWar, hWmap⟩ := NefAmpleGeneric.isArithVar_comap_of_isProjVarF hW
    have hPW : mCoordIdeal y ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ)) :=
      Ideal.map_le_iff_le_comap.mp hle
    have h0 := hgen _ hWar hPW
    have hd := hDG K ι _ 1 (fun _ => M) hWar (fun _ => hsm)
    rw [hWmap] at hd
    have h1 : (0 : ℝ) ≤ (NumbersDVR.intNum ℚ W (fun _ : Fin 1 => M.a) : ℤ) := by
      rw [← hd]; exact h0
    have h2 : (fun _ : Fin 1 => M.a) = ![M.a] := by
      funext j; fin_cases j; rfl
    rw [h2] at h1
    exact_mod_cast h1
  have hI0 : 0 < I (KH.genIdeal y) D (fun _ => M.a) := by
    have hd := hDG K ι _ D (fun _ => M) har (fun _ => hsm)
    have : (0 : ℝ) < (I (KH.genIdeal y) D (fun _ => M.a) : ℤ) := by
      show (0 : ℝ) < (NumbersDVR.intNum ℚ (KH.genIdeal y) (fun _ => M.a) : ℤ)
      rw [KH.genIdeal, ← hd]; exact hpos
    exact_mod_cast this
  exact hIn.siuZ K ι Ω y D M.a I hI har hb hnef hI0

theorem mem_chartLat_congr {y : (Σ k, ι k) → Ω} {a b : K → ℤ} {τ τ' : ℕ} (h : ∀ k, (τ : ℤ) * a k = τ' * b k)
    {s : Ω} (hs : s ∈ chartLat y a τ) : s ∈ chartLat y b τ' := by
  intro c hc
  have := hs c hc
  simpa only [h] using this

theorem mul_mem_chartLat {y : (Σ k, ι k) → Ω} {a b : K → ℤ} {s t : Ω} (hs : s ∈ chartLat y a 1)
    (ht : t ∈ chartLat y b 1) : s * t ∈ chartLat y (a + b) 1 := by
  intro c hc
  have h := mul_mem (hs c hc) (ht c hc)
  have e : s * t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (a + b) k)) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k))) := by
    have e' : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (a + b) k)) =
        (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (hc k)]
      congr 1
      simp only [Pi.add_apply]
      ring
    rw [e']
    ring
  rw [e]
  exact h

theorem pow_mem_chartLat {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} (hs : s ∈ chartLat y a 1) (j : ℕ) :
    s ^ j ∈ chartLat y (fun k => (j : ℤ) * a k) 1 := by
  induction j with
  | zero =>
    intro c _
    simpa using one_mem (chartRingZ y c)
  | succ j ih =>
    rw [pow_succ]
    refine mem_chartLat_congr (fun k => ?_) (mul_mem_chartLat ih hs)
    simp only [Pi.add_apply]
    push_cast
    ring

theorem form_mul_pow_mem_chartLat {y : (Σ k, ι k) → Ω} {α : K → ℤ} {k j : ℕ} {e : Ω}
    (he : e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1) 1) {w : MRing ι} (hw : IsMultiHomog w (fun _ => j)) :
    aeval y w * e ^ j ∈ chartLat y α (j * k) := by
  have h1 : aeval y w ∈ chartLat y (fun _ => (j : ℤ)) 1 := LiftBirationalAmple.chartLat_form hw
  refine mem_chartLat_congr (fun κ => ?_) (mul_mem_chartLat h1 (pow_mem_chartLat he j))
  simp only [Pi.add_apply]
  push_cast
  ring

theorem chartLat_le_chartLatNm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ := by
  intro s hs c hc
  have hmem := hs c hc
  rw [mem_integralClosure_iff]
  exact isIntegral_algebraMap (x := (⟨_, hmem⟩ : chartRingZ y c))

end Alg

end GlobalTheory.CompanionTheory.Ar.Plug

namespace GlobalTheory.CompanionTheory.Ar.Plug

section Alg2

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem exists_form_basis {L : Type} [Field L] (y : (Σ k, ι k) → Ω) (φ : L →+* Ω) (d : ℕ) (c : ∀ k, ι k)
    (hb : Birational y) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hd : letI := φ.toAlgebra; Module.finrank L Ω = d) (hd0 : 0 < d) :
    ∃ (j : ℕ) (w : Fin d → MRing ι), 1 ≤ j ∧ (∀ i, IsMultiHomog (w i) (fun _ => j)) ∧
      ∀ a : Fin d → L, ∑ i, φ (a i) * aeval y (w i) = 0 → a = 0 := by
  classical
  letI := φ.toAlgebra
  haveI : Module.Finite L Ω := Module.finite_of_finrank_pos (by omega)
  set r : (Σ k, ι k) → Ω := fun p => y p * (y ⟨p.1, c p.1⟩)⁻¹ with hr
  let B : Subalgebra L Ω := Algebra.adjoin L (Set.range r)
  have hrB : ∀ g : MRing ι, aeval r g ∈ B := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simpa using intCast_mem B a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, aeval_X]
      exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hform : ∀ (d' : K → ℕ) (g : MRing ι), IsMultiHomog g d' →
      aeval y g * ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d' k ∈ B := by
    intro d' g hg
    rw [← GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.aeval_scale hg y (fun k => (y ⟨k, c k⟩)⁻¹)]
    exact hrB g
  have hBtop : ∀ s : Ω, s ∈ B := by
    intro s
    obtain ⟨d', g, h, hg, hh, hh0, heq⟩ := hb s
    have hu : (∏ k, (y ⟨k, c k⟩)⁻¹ ^ d' k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (hc k))
    have h1 := hform d' g hg
    have h2 := hform d' h hh
    have h3 : (aeval y h * ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d' k)⁻¹ ∈ B :=
      Subalgebra.inv_mem_of_algebraic (A := B) (x := ⟨_, h2⟩) (Algebra.IsAlgebraic.isAlgebraic _)
    have h4 := mul_mem h1 h3
    have h5 : aeval y g * (∏ k, (y ⟨k, c k⟩)⁻¹ ^ d' k) * (aeval y h * ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d' k)⁻¹ = s := by
      have hne := mul_ne_zero hh0 hu
      rw [heq, mul_assoc s, mul_inv_cancel_right₀ hne]
    rwa [h5] at h4
  let T : Set Ω := {x | ∃ (d' : K → ℕ) (w : MRing ι), IsMultiHomog w d' ∧ aeval y w = x * ∏ k, y ⟨k, c k⟩ ^ d' k}
  have hcl : ∀ x ∈ Submonoid.closure (Set.range r), x ∈ T := by
    intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      refine ⟨Pi.single p.1 1, X p, isMultiHomog_X' p.1 p.2, ?_⟩
      rw [aeval_X, Finset.prod_eq_single p.1]
      · simp [hr, hc]
      · intro b _ hbp
        simp [Pi.single_apply, hbp]
      · simp
    | one =>
      exact ⟨0, 1, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one, by simp⟩
    | mul x x' _ _ hx hx' =>
      obtain ⟨d₁, w₁, h₁, e₁⟩ := hx
      obtain ⟨d₂, w₂, h₂, e₂⟩ := hx'
      refine ⟨d₁ + d₂, w₁ * w₂, isMultiHomog_mul h₁ h₂, ?_⟩
      rw [map_mul, e₁, e₂]
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      ring
  have hspan : Submodule.span L T = ⊤ := by
    rw [eq_top_iff]
    intro s _
    have h1 : s ∈ Subalgebra.toSubmodule B := hBtop s
    rw [Algebra.adjoin_eq_span] at h1
    exact Submodule.span_mono (fun x hx => hcl x hx) h1
  obtain ⟨f₀, hfT, -, hli₀⟩ := Submodule.exists_fun_fin_finrank_span_eq L T
  have hcard : Module.finrank L (Submodule.span L T) = d := by
    rw [hspan, finrank_top]; exact hd
  let f : Fin d → Ω := fun i => f₀ (Fin.cast hcard.symm i)
  have hli : LinearIndependent L f := hli₀.comp _ (Fin.cast_injective _)
  have hfT' : ∀ i, ∃ (d' : K → ℕ) (w : MRing ι), IsMultiHomog w d' ∧ aeval y w = f i * ∏ k, y ⟨k, c k⟩ ^ d' k :=
    fun i => hfT _
  choose dd ww hww hww' using hfT'
  let J : ℕ := 1 + ∑ i, ∑ k, dd i k
  have hJ : ∀ i k, dd i k ≤ J := fun i k => by
    have h1 : dd i k ≤ ∑ k, dd i k := Finset.single_le_sum (f := dd i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h2 : ∑ k, dd i k ≤ ∑ i, ∑ k, dd i k :=
      Finset.single_le_sum (f := fun i => ∑ k, dd i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [J]
    omega
  refine ⟨J, fun i => ww i * xpow c (fun k => J - dd i k), by simp only [J]; omega, fun i => ?_, fun a ha => ?_⟩
  · have := isMultiHomog_mul (hww i) (isMultiHomog_xpow c (fun k => J - dd i k))
    convert this using 1
    funext k
    have := hJ i k
    simp only [Pi.add_apply]
    omega
  · have hY : (∏ k, y ⟨k, c k⟩ ^ J) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
    have hval : ∀ i, aeval y (ww i * xpow c (fun k => J - dd i k)) = f i * ∏ k, y ⟨k, c k⟩ ^ J := by
      intro i
      have e : (∏ k, y ⟨k, c k⟩ ^ dd i k) * aeval y (xpow c fun k => J - dd i k) = ∏ k, y ⟨k, c k⟩ ^ J := by
        rw [xpow, map_prod, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [map_pow, aeval_X, ← pow_add]
        congr 1
        have := hJ i k
        omega
      rw [map_mul, hww', mul_assoc, e]
    simp only [hval] at ha
    have h0 : (∑ i, φ (a i) * f i) * ∏ k, y ⟨k, c k⟩ ^ J = 0 := by
      rw [Finset.sum_mul]
      simpa only [mul_assoc] using ha
    have h1 := (mul_eq_zero.1 h0).resolve_right hY
    have hsm : ∀ (t : L) (x : Ω), t • x = φ t * x := fun t x => rfl
    funext i
    exact Fintype.linearIndependent_iff.1 hli a (by simpa only [hsm] using h1) i

theorem eq_zero_of_trace {L : Type} [Field L] [CharZero L] (φ : L →+* Ω) (d : ℕ)
    (hd : letI := φ.toAlgebra; Module.finrank L Ω = d) (hd0 : 0 < d) (f : Fin d → Ω)
    (hf : ∀ a : Fin d → L, ∑ i, φ (a i) * f i = 0 → a = 0) (x : Ω)
    (hx : letI := φ.toAlgebra; ∀ i, Algebra.trace L Ω (x * f i) = 0) : x = 0 := by
  letI := φ.toAlgebra
  haveI : Module.Finite L Ω := Module.finite_of_finrank_pos (by omega)
  have hli : LinearIndependent L f := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have hsm : ∀ (t : L) (x : Ω), t • x = φ t * x := fun t x => rfl
    have := hf a (by simpa only [hsm] using ha)
    exact congrFun this i
  have hspan : Submodule.span L (Set.range f) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simpa using hd.symm)
  have hall : ∀ w, Algebra.traceForm L Ω x w = 0 := by
    intro w
    have hw : w ∈ Submodule.span L (Set.range f) := hspan ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      simpa using hx i
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul t a _ ha => rw [map_smul, ha, smul_zero]
  exact (traceForm_nondegenerate L Ω).1 x hall

end Alg2

end GlobalTheory.CompanionTheory.Ar.Plug

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem gauge_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Y : Model Xo c β} {S : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
    {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
    {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}
    (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw) : gauge Rd u ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (Or.lines r).1)

theorem exists_small_basis : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (II : IntersectionSystem) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ), IsFullIntersectionSystem II → T.T1 II → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g < B + 1 → ∃ (k₀ : ℕ) (R₀ : ℝ) (f : Fin (o.toTowerOrigin.Or B b).Fl.deg → (T.M B b).Ω), 8 ∣ k₀ ∧ 0 < R₀ ∧ (∀ i, f i ∈ modelSmall (o.toTowerOrigin.Or B b) (k₀ • u) R₀) ∧ (∀ a : Fin (o.toTowerOrigin.Or B b).Fl.deg → Om Z, ∑ i, Rd.φ (a i) * f i = 0 → a = 0) ∧ ∀ (v : GlobalTheory.AllWt.Weight Dw) (s : (T.M B b).Ω), (∀ i, trOf Rd v (s * f i) = 0) → s = 0 := by
  intro hG E _ _ _ H Dw l Xo c h Y _ T o B b Fr Z Rd II u g hII hT1 hW hB
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hStrict : ∀ τ, StrictAnti (u τ) := fun τ a b' hab => by
    have := hW.2.1 τ a b' hab
    simpa [reW] using this
  obtain ⟨C, s, q, m, θ, hC, hs, hs0, hq, hm, hsm⟩ := GlobalTheory.T.strict_weight_growth_bound hG E H Dw l Xo c Y T o B b u hStrict
  obtain ⟨hnefE, hdeg, -, hposV⟩ := GlobalTheory.T.weight_threshold_limit_coefficients (CMType H) (Dw.p + Dw.q) T II B (reW u) g b s q m hII hT1 hW hB hs hs0
    (fun n => (hq n).1) hm
  have hδ : (0 : ℝ) < ((T.M B b).δ : ℝ) := by exact_mod_cast (T.M B b).δ_pos
  have hdegE := hdeg.eventually_const_lt (mul_pos hδ hposV)
  obtain ⟨n, hn1, hn2⟩ := (hnefE.and hdegE).exists
  have hdeg0 : 0 < (o.toTowerOrigin.Or B b).Fl.deg := by
    have h1 := (T.M B b).δ_pos
    rw [(o.toTowerOrigin.Or B b).δ_eq] at h1
    exact Nat.pos_of_mul_pos_left h1 |> fun h => by simpa using h
  set M := Top.combLine ((T.M B b).line (Top.scale (s n))) (m n) with hM
  have hq0 : (0 : ℝ) < (q n : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) := pow_pos (by exact_mod_cast (hq n).1) _
  have hgp : 0 < geomDeg (mCoordIdeal (T.M B b).y) M (Top.dimFl (CMType H) (Dw.p + Dw.q)) := by
    exact (div_pos_iff_of_pos_right hq0).1 hn2
  haveI : CharZero (T.M B b).Ω := charZero_of_injective_ringHom (o.toTowerOrigin.Or B b).𝔐.cst.injective
  haveI : CharZero (Om Z) := RingHom.charZero Rd.φ
  obtain ⟨k, hk1, e, he, he0⟩ := exists_section_of_nef hIn (T.M B b).y _ M (T.M B b).arith (T.M B b).birational hn1 hgp
  have hrel := GlobalTheory.CompanionTheory.Ar.PB.NefPolProof.exists_ne_zero_of_relevant (T.M B b).y (T.M B b).arith.2.1.2.2
  choose cc hcc using hrel
  obtain ⟨j, w, hj, hw, hind⟩ := exists_form_basis (T.M B b).y Rd.φ (o.toTowerOrigin.Or B b).Fl.deg cc (T.M B b).birational hcc Rd.deg hdeg0
  have hτ : 0 < j * k := Nat.mul_pos hj hk1
  set τ := j * k with hτd
  let σ : Fin (o.toTowerOrigin.Or B b).Fl.deg → (T.M B b).Ω := fun i => MvPolynomial.aeval (T.M B b).y (w i) * e ^ j
  have hσ : ∀ i, σ i ∈ chartLat (T.M B b).y M.a τ := fun i => form_mul_pow_mem_chartLat he (hw i)
  have hsmooth : IsSmoothHerm M := by
    obtain ⟨P0, -, hsemi⟩ := hn1.semipos
    exact hsemi.1
  choose Cb hCb0 hCb using fun i => GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSupBound.proof _ _ _ (T.M B b).y M τ (σ i)
    hsmooth.continuousOn (hσ i)
  have hτr : (0 : ℝ) < (τ : ℝ) := by exact_mod_cast hτ
  have hqr : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast (hq n).1
  let t : ℝ := (∑ i, Cb i) / τ / q n
  have hqt : (q n : ℝ) * t = (∑ i, Cb i) / τ := by
    simp only [t]
    field_simp
  have hsmall : ∀ i, IsSmallH (mCoordIdeal (T.M B b).y) (T.M B b).y (Small.shiftH M ((q n : ℝ) * t)) τ (σ i) := by
    intro i dg dh g' h' z hg hh hd heq hz
    have hb := hCb i dg dh g' h' z hg hh hd heq hz
    have hpos : 0 < M.h z := M.pos z hz.1
    have hsum : Cb i ≤ ∑ i, Cb i := Finset.single_le_sum (fun i _ => hCb0 i) (Finset.mem_univ i)
    have hexp : Real.exp (Cb i) ≤ (Real.exp ((∑ i, Cb i) / τ)) ^ τ := by
      rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hτr.ne']
      exact Real.exp_le_exp.2 hsum
    show _ ≤ _ * (Real.exp ((q n : ℝ) * t) * M.h z) ^ τ
    rw [hqt, mul_pow]
    calc _ ≤ _ := hb
      _ ≤ (Real.exp ((∑ i, Cb i) / τ)) ^ τ * ‖MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) h')‖ * M.h z ^ τ := by
        gcongr
      _ = _ := by ring
  have hf := fun i => hsm n τ t (σ i) (chartLat_le_chartLatNm _ _ _ (hσ i)) (hsmall i)
  have hne : e ^ j * θ n ^ τ ≠ 0 := mul_ne_zero (pow_ne_zero _ he0) (pow_ne_zero _ (hq n).2.2)
  have hind' : ∀ a : Fin (o.toTowerOrigin.Or B b).Fl.deg → Om Z, ∑ i, Rd.φ (a i) * (σ i * θ n ^ τ) = 0 → a = 0 := by
    intro a ha
    refine hind a ?_
    have h0 : (∑ i, Rd.φ (a i) * MvPolynomial.aeval (T.M B b).y (w i)) * (e ^ j * θ n ^ τ) = 0 := by
      rw [Finset.sum_mul, ← ha]
      exact Finset.sum_congr rfl fun i _ => by simp only [σ]; ring
    exact (mul_eq_zero.1 h0).resolve_right hne
  refine ⟨τ * q n, Real.exp (((τ * q n : ℕ) : ℝ) * (t + C * s n)), fun i => σ i * θ n ^ τ,
    Dvd.dvd.mul_left (hq n).2.1 _, Real.exp_pos _, hf, hind', fun v s' hs' => ?_⟩
  have hg0 := gauge_ne_zero Rd v
  have hx := eq_zero_of_trace Rd.φ (o.toTowerOrigin.Or B b).Fl.deg Rd.deg hdeg0 (fun i => σ i * θ n ^ τ) hind' (s' / gauge Rd v) (fun i => by
    have := hs' i
    rw [trOf] at this
    rwa [div_mul_eq_mul_div])
  exact (div_eq_zero_iff.1 hx).resolve_right hg0

end GlobalTheory.CompanionTheory.Ar.Plug
