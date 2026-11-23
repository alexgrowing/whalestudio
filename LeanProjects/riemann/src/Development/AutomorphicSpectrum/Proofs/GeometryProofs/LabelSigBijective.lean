import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ExistsAlgPtOff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsHomogeneousGrL
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {SS : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y SS RM Fx}

def GoodRing (Fr : Small.GenFrame Or) (A : Subring RM.Ω) : Prop :=
  (∀ a : c.F, Or.𝔐.cst a ∈ A) ∧
  (letI := Small.cstAlg Or
    ∃ (q : TRing c.F) (φ : q.R →ₐ[c.F] RM.Ω) (yq : FrPt Xo c q.R), FrMap φ yq Fr.y₀ ∧ ∀ r, φ r ∈ A) ∧
  (∀ (ρ : RootIx Dw) (s : (k : RM.K) → RM.ι k), (∀ k, RM.y ⟨k, s k⟩ ≠ 0) →
    (∏ k, RM.y ⟨k, s k⟩ ^ RM.xdeg ρ k) * Or.e ρ ∈ A ∧ ((∏ k, RM.y ⟨k, s k⟩ ^ RM.xdeg ρ k) * Or.e ρ)⁻¹ ∈ A) ∧
  ∀ (s : CMType H ⊕ CMType H) (q : Cpt Or.𝔐.ξ),
    ∃ (b : Fin (labelRk Dw s) → Or.𝔐.Li) (T : Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) RM.Ω),
      (∀ i, flagStep RM.Ω b i = flagStep RM.Ω (Or.Fl.b s) i) ∧ (Or.𝔐.V s).IsFrameAt b q ∧
      (∀ i, b i = ∑ j, T i j • Or.Fl.b s j) ∧ (∀ i j, T i j ∈ A) ∧ ∀ i, T i i ≠ 0 ∧ (T i i)⁻¹ ∈ A

open Classical in

def absT (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ) (x : T.Fr) : ℝ :=
  if x = 0 then 0 else (p : ℝ) ^ (-((vV T.V x : ℝ) / ((e : ℝ) * (ramOverZ la : ℝ))))

def IsIntPt (Fr : Small.GenFrame Or) (A : Subring RM.Ω) {p : ℕ} [Fact p.Prime] (ev : A →+* PadicAlgCl p)
    (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io)
    (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ) : Prop :=
  letI := io.toAlgebra
  letI := Small.cstAlg Or
  (p : 𝓞 c.F) ∈ la.asIdeal ∧ OverLa la T.V io e ∧ y.IsAlg ∧ (∃ τ : ℝ, Ref.IsPhiAt Xo c la T io y τ) ∧
    (∀ (a : c.F) (h : Or.𝔐.cst a ∈ A), evT ⟨_, h⟩ = io a) ∧
    (∀ x : A, ‖ev x‖ = absT p la T e (evT x)) ∧
    (∃ (q : TRing c.F) (φ : q.R →ₐ[c.F] RM.Ω) (ψ : q.R →ₐ[c.F] T.Fr) (yq : FrPt Xo c q.R),
      FrMap φ yq Fr.y₀ ∧ FrMap ψ yq zT ∧ ∀ r, ∃ h : φ r ∈ A, ψ r = evT ⟨φ r, h⟩) ∧
    FrBor t zT y.1

def tOf (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ) (t : Ix Dw → T.Frˣ) (j : Ix Dw) : ℝ :=
  (absT p la T e (t j : T.Fr))⁻¹

def ReadsZ (Fr : Small.GenFrame Or) {p : ℕ} [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p)
    {la : HeightOneSpectrum (𝓞 c.F)} (x : (Ref.pjSys Xo c).Pt la) (t : Ix Dw → ℝ) : Prop :=
  ∀ (a : WZ E), ∀ f ∈ secZ Xo c a, ∃ v : PadicAlgCl p, Small.HasVal RM.y 0 (Fr.rd f) z v ∧
    ((Ref.pjSys Xo c).val x f = ⊤ → v = 0) ∧
    ∀ s : ℝ, (Ref.pjSys Xo c).val x f = ((ramOverZ la * s : ℝ) : EReal) →
      ‖v‖ = (p : ℝ) ^ (-s) * ∏ j, t j ^ exZ Dw a j

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd

open GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest (hasVal_unique mConeMap_form)

section HV

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] {𝕜 : Type} [Field 𝕜]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → 𝕜}

theorem hv_mul {a b : K → ℤ} {s s' : Ω} {w w' : 𝕜} (h : Small.HasVal y a s z w)
    (h' : Small.HasVal y b s' z w') : Small.HasVal y (a + b) (s * s') z (w * w') := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  obtain ⟨dg', dh', g', f', hg', hf', hd', e', hz0', ez'⟩ := h'
  refine ⟨dg + dg', dh + dh', g * g', f * f', ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hg hg',
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hf hf', fun k => ?_, ?_, ?_, ?_⟩
  · have := hd k
    have := hd' k
    simp only [Pi.add_apply]
    push_cast
    omega
  · rw [map_mul, map_mul, e, e']
    ring
  · rw [map_mul]
    exact mul_ne_zero hz0 hz0'
  · rw [map_mul, map_mul, ez, ez']
    ring

theorem hv_one : Small.HasVal y (0 : K → ℤ) (1 : Ω) z (1 : 𝕜) :=
  ⟨0, 0, 1, 1, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one, fun _ => by simp,
    by simp, by simp, by simp⟩

theorem hv_inv (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) {a : K → ℤ} {s : Ω} {w : 𝕜}
    (h : Small.HasVal y a s z w) (hs : s ≠ 0) (hw : w ≠ 0) : Small.HasVal y (-a) s⁻¹ z w⁻¹ := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  have hfy : MvPolynomial.aeval y f ≠ 0 := fun h0 => hz0 (hz.2 f (by
    show mConeMap y f = 0
    rw [mConeMap_form y hf, h0]
    simp))
  refine ⟨dh, dg, f, g, hf, hg, fun k => ?_, ?_, ?_, ?_⟩
  · have := hd k
    simp only [Pi.neg_apply]
    omega
  · rw [e]
    field_simp
  · rw [ez]
    exact mul_ne_zero hw hz0
  · rw [ez]
    field_simp

theorem hv_pow {a : K → ℤ} {s : Ω} {w : 𝕜} (h : Small.HasVal y a s z w) (n : ℕ) :
    Small.HasVal y (n • a) (s ^ n) z (w ^ n) := by
  induction n with
  | zero => simpa using hv_one
  | succ n ih =>
    rw [pow_succ, pow_succ, succ_nsmul]
    exact hv_mul ih h

theorem hv_zpow (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) {a : K → ℤ} {s : Ω} {w : 𝕜}
    (h : Small.HasVal y a s z w) (hs : s ≠ 0) (hw : w ≠ 0) (n : ℤ) :
    Small.HasVal y (n • a) (s ^ n) z (w ^ n) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using hv_pow h m
  · have := hv_inv hz (hv_pow h m) (pow_ne_zero _ hs) (pow_ne_zero _ hw)
    simpa using this

theorem hv_prod {I : Type} (S : Finset I) {a : I → K → ℤ} {s : I → Ω} {w : I → 𝕜}
    (h : ∀ i ∈ S, Small.HasVal y (a i) (s i) z (w i)) :
    Small.HasVal y (∑ i ∈ S, a i) (∏ i ∈ S, s i) z (∏ i ∈ S, w i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hv_one
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    exact hv_mul (h i (Finset.mem_insert_self i S)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end HV

section Roots

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def labelSig (q : Σ s, Fin (labelRk Dw s)) : Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
  ⟨Small.labelC q.1, Small.labelFin Dw q.1 q.2⟩

theorem labelSig_bijective : Function.Bijective (labelSig Dw) := by
  constructor
  · rintro ⟨s, i⟩ ⟨s', i'⟩ h
    have h1 : Small.labelC s = Small.labelC s' := congrArg Sigma.fst h
    obtain rfl := (Small.labelC_bijective H).1 h1
    have h2 : (i : ℕ) = i' := congrArg (fun x : Σ τ : E →+* ℂ, Fin (Dw.mult τ) => (x.2 : ℕ)) h
    exact congrArg _ (Fin.ext h2)
  · rintro ⟨σ, i⟩
    obtain ⟨s, k, hk⟩ := Small.exists_labelFin Dw σ i
    exact ⟨⟨s, k⟩, hk⟩

theorem rootIdx_lt {τ : CMType H} {n : Fin (Dw.p + Dw.q)} (h : (n : ℕ) < Dw.p) :
    HodgeCpt.rootIdx Dw (τ, n) = ⟨.inl τ, ⟨n, h⟩⟩ := dif_pos h

theorem rootIdx_ge {τ : CMType H} {n : Fin (Dw.p + Dw.q)} (h : ¬ (n : ℕ) < Dw.p) :
    HodgeCpt.rootIdx Dw (τ, n) = ⟨.inr τ, ⟨Dw.p + Dw.q - 1 - n, by have := n.2; show _ < Dw.q; omega⟩⟩ := dif_neg h

theorem rootVal_lt {τ : CMType H} {n : Fin (Dw.p + Dw.q)} (h : (n : ℕ) < Dw.p) :
    ((HodgeCpt.rootIdx Dw (τ, n)).2 : ℕ) = n :=
  congrArg (fun x : Σ s, Fin (labelRk Dw s) => (x.2 : ℕ)) (rootIdx_lt Dw (τ := τ) h)

theorem rootVal_ge {τ : CMType H} {n : Fin (Dw.p + Dw.q)} (h : ¬ (n : ℕ) < Dw.p) :
    ((HodgeCpt.rootIdx Dw (τ, n)).2 : ℕ) = Dw.p + Dw.q - 1 - n :=
  congrArg (fun x : Σ s, Fin (labelRk Dw s) => (x.2 : ℕ)) (rootIdx_ge Dw (τ := τ) h)

theorem rootIdx_bijective : Function.Bijective (HodgeCpt.rootIdx Dw) := by
  constructor
  · rintro ⟨τ, n⟩ ⟨τ', n'⟩ h
    have hn := n.2
    have hn' := n'.2
    have hs := congrArg Sigma.fst h
    have hv := congrArg (fun x : Σ s, Fin (labelRk Dw s) => (x.2 : ℕ)) h
    by_cases h1 : (n : ℕ) < Dw.p <;> by_cases h2 : (n' : ℕ) < Dw.p
    · simp only [rootIdx_lt Dw h1, rootIdx_lt Dw h2] at hs
      rw [show (HodgeCpt.rootIdx Dw (τ, n)).2.val = n from rootVal_lt Dw h1,
        show (HodgeCpt.rootIdx Dw (τ', n')).2.val = n' from rootVal_lt Dw h2] at hv
      exact Prod.ext (Sum.inl.inj hs) (Fin.ext hv)
    · simp only [rootIdx_lt Dw h1, rootIdx_ge Dw h2] at hs
      exact absurd hs (by simp)
    · simp only [rootIdx_ge Dw h1, rootIdx_lt Dw h2] at hs
      exact absurd hs (by simp)
    · simp only [rootIdx_ge Dw h1, rootIdx_ge Dw h2] at hs
      rw [show (HodgeCpt.rootIdx Dw (τ, n)).2.val = _ from rootVal_ge Dw h1,
        show (HodgeCpt.rootIdx Dw (τ', n')).2.val = _ from rootVal_ge Dw h2] at hv
      exact Prod.ext (Sum.inr.inj hs) (Fin.ext (by show (n : ℕ) = n'; omega))
  · rintro ⟨s | s, k⟩
    · have h : (k : ℕ) < Dw.p := k.2
      exact ⟨(s, ⟨k, by omega⟩), rootIdx_lt Dw (n := ⟨k, by omega⟩) h⟩
    · have hk : (k : ℕ) < Dw.q := k.2
      have h : ¬ (Dw.p + Dw.q - 1 - (k : ℕ) < Dw.p) := by omega
      refine ⟨(s, ⟨Dw.p + Dw.q - 1 - k, by omega⟩), ?_⟩
      rw [rootIdx_ge Dw (n := ⟨Dw.p + Dw.q - 1 - k, by omega⟩) h]
      congr 2
      show Dw.p + Dw.q - 1 - (Dw.p + Dw.q - 1 - (k : ℕ)) = k
      omega

theorem prod_exZ (a : WZ E) (t : Ix Dw → ℝ) :
    ∏ j, t j ^ exZ Dw a j = ∏ r : RootIx Dw, t (Small.rootFrameIx Dw r) ^ exZ Dw a (Small.rootFrameIx Dw r) := by
  let g : RootIx Dw ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    Equiv.ofBijective _ ((labelSig_bijective Dw).comp (rootIdx_bijective Dw))
  rw [← Fintype.prod_equiv (Equiv.optionCongr g) (fun o => t (Option.map g o) ^ exZ Dw a (Option.map g o))
    (fun j => t j ^ exZ Dw a j) (fun _ => rfl), Fintype.prod_option]
  simp only [Option.map_none, Option.map_some]
  rw [show exZ Dw a none = 0 from rfl, zpow_zero, one_mul]
  rfl

theorem towerWt_root (a : WZ E) (r : RootIx Dw) :
    towerWt Dw a r.1 r.2 = ((HodgeCpt.rootSgn Dw r * exZ Dw a (Small.rootFrameIx Dw r) : ℤ) : ℝ) := by
  obtain ⟨τ, n⟩ := r
  by_cases h : (n : ℕ) < Dw.p
  · have e1 : exZ Dw a (Small.rootFrameIx Dw (τ, n)) = a (τ.1, n) :=
      congrArg (fun x : Σ s, Fin (labelRk Dw s) => a (Small.labelC x.1, (x.2 : ℕ))) (rootIdx_lt Dw (τ := τ) h)
    rw [e1]
    simp [towerWt, HodgeCpt.rootSgn, h]
  · have e1 : exZ Dw a (Small.rootFrameIx Dw (τ, n)) = a (conjEmb τ.1, Dw.p + Dw.q - 1 - n) :=
      congrArg (fun x : Σ s, Fin (labelRk Dw s) => a (Small.labelC x.1, (x.2 : ℕ))) (rootIdx_ge Dw (τ := τ) h)
    rw [e1]
    simp [towerWt, HodgeCpt.rootSgn, h]

theorem rootSgn_mul_self (r : RootIx Dw) : HodgeCpt.rootSgn Dw r * HodgeCpt.rootSgn Dw r = 1 := by
  unfold HodgeCpt.rootSgn
  split_ifs <;> norm_num

end Roots

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd

open GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest (hasVal_unique)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {SS : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y SS RM Fx}

theorem ram_pos {p : ℕ} [hp : Fact p.Prime] {la : HeightOneSpectrum (𝓞 c.F)} (hla : (p : 𝓞 c.F) ∈ la.asIdeal) :
    0 < ramOverZ la := by
  have hp0 : (p : c.F) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hres : Formalism.L2.Pj.resCharOf la = p := by
    by_contra h
    refine Formalism.L2.Pj.Crude.crv_not_mem la (fun hd => h ?_) hla
    exact (Nat.prime_dvd_prime_iff_eq (Formalism.L2.Pj.Crude.resCharOf_prime la) hp.out).1 hd
  have hv : Ref.vl la (p : c.F) = ramOverZ la := by
    rw [← hres]
    exact Formalism.L2.Pj.Crude.crv_vLa_char la
  have h1 : la.valuation c.F (p : c.F) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 c.F) c.F)]
    exact (la.valuation_lt_one_iff_mem _).2 hla
  have h2 := (WithZero.log_lt_log ((la.valuation c.F).ne_zero_iff.2 hp0) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  have h3 : (0 : ℤ) < Ref.vl la (p : c.F) := by unfold Ref.vl; omega
  rw [hv] at h3
  exact_mod_cast h3

theorem tOf_pos {p : ℕ} [hp : Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ) (t : Ix Dw → T.Frˣ)
    (j : Ix Dw) : 0 < tOf p la T e t j := by
  unfold tOf absT
  rw [if_neg (t j).ne_zero]
  exact inv_pos.2 (Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _)

theorem val_indicator {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c} {e : Comp Xo c → Rul Xo c}
    (hL : CompLaws U h e) {Fr : Small.GenFrame Or} {Z : Comp Xo c} (Rd : Reading Fr h Z) {p : ℕ} [hp : Fact p.Prime]
    {z : (Σ k, RM.ι k) → PadicAlgCl p} (hz : z ∈ Small.ptsOver (PadicAlgCl p) (mCoordIdeal RM.y))
    {la : HeightOneSpectrum (𝓞 c.F)} (hra : 0 < ramOverZ la) (y : (Ref.pjSys Xo c).Pt la) {t : Ix Dw → ℝ}
    (hS : ReadsZ Fr z y t) : (Ref.pjSys Xo c).val y (e Z) = 0 := by
  have he0 : e Z ∈ secZ Xo c 0 := by
    have h1 := hL.e_sec Z
    rw [← secZ_nat] at h1
    exact h1
  have hex : ∀ i, exZ Dw (0 : WZ E) i = 0 := fun i => by cases i <;> rfl
  have hrd : Fr.rd (e Z) = 1 := by
    rw [Rd.rd_eq 0 (e Z) he0, (hL.e_val Z).1, map_one]
    simp [hex]
  obtain ⟨v, hv, htop, hs⟩ := hS 0 (e Z) he0
  rw [hrd] at hv
  have hv1 : v = 1 := hasVal_unique hz hv hv_one
  subst hv1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hra' : (0 : ℝ) < ramOverZ la := by exact_mod_cast hra
  induction hval : (Ref.pjSys Xo c).val y (e Z) with
  | bot => exact absurd hval ((Ref.pjSys Xo c).val_ne_bot y _)
  | top => exact absurd (htop hval) one_ne_zero
  | coe m =>
    have h2 := hs (m / ramOverZ la) (by rw [hval]; congr 1; field_simp)
    simp only [hex, zpow_zero, Finset.prod_const_one, mul_one, norm_one] at h2
    have h3 : -(m / ramOverZ la) = 0 := by
      have h5 := congrArg Real.log h2
      rw [Real.log_one, Real.log_rpow (by linarith)] at h5
      exact (mul_eq_zero.1 h5.symm).resolve_right (Real.log_pos hp1).ne'
    have h4 : m = 0 := by
      field_simp at h3
      linarith
    rw [h4]
    rfl

theorem read_of_reads {Fr : Small.GenFrame Or} {p : ℕ} [hp : Fact p.Prime]
    {z : (Σ k, RM.ι k) → PadicAlgCl p} (hz : z ∈ Small.ptsOver (PadicAlgCl p) (mCoordIdeal RM.y))
    {la : HeightOneSpectrum (𝓞 c.F)} (y : (Ref.pjSys Xo c).Pt la) {t : Ix Dw → ℝ} (htp : ∀ j, 0 < t j) {θ : ℝ}
    (hS : ReadsZ Fr z y t) (hR : Small.ReadsRootsFin Or z t θ) :
    ∃ rec : RootIx Dw → ℝ, (∀ r', 0 < rec r' ∧
        |Real.log (Small.supMet (RM.xdeg r') z) - Real.log (rec r')| ≤ θ * Real.log p) ∧
      ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) →
        ∀ f ∈ secZ Xo c a, ∃ v, Small.HasVal RM.y (Top.combLine (RM.line 1) n').a
            (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z v ∧ ((Ref.pjSys Xo c).val y f = ⊤ → v = 0) ∧
          ∀ s : ℝ, (Ref.pjSys Xo c).val y f = ((ramOverZ la * s : ℝ) : EReal) →
            ‖v‖ = (p : ℝ) ^ (-s) * ∏ r', rec r' ^ n' (some r') := by
  choose w hw hw0 hb using hR
  have hwn : ∀ r, 0 < ‖w r‖ := fun r => norm_pos_iff.2 (hw0 r)
  refine ⟨fun r => ‖w r‖ / t (Small.rootFrameIx Dw r) ^ HodgeCpt.rootSgn Dw r,
    fun r => ⟨div_pos (hwn r) (zpow_pos (htp _) _), hb r⟩, fun a n' hn f hf => ?_⟩
  obtain ⟨v0, hv0, htop, hs⟩ := hS a f hf
  have hnone : n' none = 0 := by
    have h1 := hn none
    have h2 : RM.coef (towerWt Dw a) 0 none = 0 := by simp [Top.RootModel.coef]
    rw [h2] at h1
    exact_mod_cast h1
  have hsome : ∀ r, n' (some r) = -(HodgeCpt.rootSgn Dw r * exZ Dw a (Small.rootFrameIx Dw r)) := fun r => by
    have h1 := hn (some r)
    have h2 : RM.coef (towerWt Dw a) 0 (some r) = -towerWt Dw a r.1 r.2 := rfl
    rw [h2, towerWt_root] at h1
    exact_mod_cast h1
  have hdeg : (Top.combLine (RM.line 1) n').a = 0 + ∑ r, n' (some r) • RM.xdeg r := by
    show ∑ j, n' j • (RM.line 1 j).a = _
    rw [Fintype.sum_option, hnone, zero_smul]
    refine congrArg _ (Finset.sum_congr rfl fun r _ => ?_)
    show n' (some r) • (RM.x 1 r).a = _
    rw [RM.x_deg]
  have hev : ∀ r, Or.e r ^ (-n' (some r)) = (Or.e r)⁻¹ ^ n' (some r) := fun r => by
    rw [zpow_neg, inv_zpow]
  have hroot : ∀ r ∈ (Finset.univ : Finset (RootIx Dw)), Small.HasVal RM.y (n' (some r) • RM.xdeg r)
      ((Or.e r)⁻¹ ^ n' (some r)) z (w r ^ n' (some r)) := fun r _ =>
    hv_zpow hz (hw r) (inv_ne_zero (Or.lines r).1) (hw0 r) _
  refine ⟨v0 * ∏ r, w r ^ n' (some r), ?_, fun h => ?_, fun s h => ?_⟩
  · rw [hdeg]
    simp only [hev]
    exact hv_mul hv0 (hv_prod Finset.univ hroot)
  · rw [htop h, zero_mul]
  · have hrew : ∏ r, (‖w r‖ / t (Small.rootFrameIx Dw r) ^ HodgeCpt.rootSgn Dw r) ^ n' (some r) =
        (∏ r, ‖w r‖ ^ n' (some r)) *
          ∏ r, t (Small.rootFrameIx Dw r) ^ exZ Dw a (Small.rootFrameIx Dw r) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun r _ => ?_
      have ht := htp (Small.rootFrameIx Dw r)
      rw [div_zpow, div_eq_mul_inv, ← zpow_mul, ← zpow_neg]
      congr 2
      rw [hsome r]
      linear_combination (exZ Dw a (Small.rootFrameIx Dw r)) * rootSgn_mul_self Dw r
    rw [hrew, norm_mul, hs s h, norm_prod, prod_exZ]
    simp only [norm_zpow]
    ring

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd
