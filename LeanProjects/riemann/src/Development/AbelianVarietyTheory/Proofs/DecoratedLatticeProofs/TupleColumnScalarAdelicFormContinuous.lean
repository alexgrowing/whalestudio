import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTupleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousChartLevelCharactersAdelicTupleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlices
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RamCont

variable {D : D7}

theorem infM_mul' (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn (g * h) τ = infM θ V hn g τ * infM θ V hn h τ := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.infM_mul θ V g h τ

theorem infM_fin' (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    infM θ V hn k τ = 1 := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

theorem continuous_infM' (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n) (τ : D.what₂.Tau) :
    Continuous fun g : GA D V => infM θ V hn g τ := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.continuous_infM θ hθ V τ

theorem pf_mul (V : HSp D) (g h : GA D V) :
    GlobalTheory.AdForm.RdLaw.pf V (g * h) = GlobalTheory.AdForm.RdLaw.pf V g * GlobalTheory.AdForm.RdLaw.pf V h := by
  apply Subtype.ext
  show GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V (g * h)) =
    GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V g) * GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V h)
  rw [map_mul, map_mul]

theorem pf_inv (V : HSp D) (g : GA D V) : GlobalTheory.AdForm.RdLaw.pf V g⁻¹ = (GlobalTheory.AdForm.RdLaw.pf V g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pf_mul, inv_mul_cancel, GlobalTheory.AdForm.RdLaw.pf_one]

theorem pf_inv_mul_mem (V : HSp D) (g : GA D V) : (GlobalTheory.AdForm.RdLaw.pf V g)⁻¹ * g ∈ GinfC V := by
  rw [GlobalTheory.CentreTarget.mem_GinfC, ← pf_inv, GlobalTheory.CentreTarget.mt_mul, Matrix.map_mul, GlobalTheory.AdForm.RdLaw.mt_pf,
    GlobalTheory.AdForm.RdLaw.PM_map, GlobalTheory.AdForm.RdLaw.finPart_eps, RingHom.map_sub, RingHom.map_one,
    GlobalTheory.AdForm.RdLaw.finPart_eps, sub_self, zero_smul, add_zero, one_smul, ← Matrix.map_mul,
    ← GlobalTheory.CentreTarget.mt_mul, inv_mul_cancel]
  show (matHom V 1).1.map _ = 1
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem infM_mul_pf (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k d : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn (k * ((GlobalTheory.AdForm.RdLaw.pf V d)⁻¹ * d)) τ = infM θ V hn k τ * infM θ V hn d τ := by
  rw [infM_mul' θ V hn k, infM_mul' θ V hn _ d, infM_fin' θ V hn _ (inv_mem (GlobalTheory.AdForm.RdLaw.pf_fin V d)), one_mul]

end GlobalTheory.AdForm.RamCont

namespace GlobalTheory.AdForm.RamCont

theorem rd_continuous : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b y, Continuous (A.rd θ j hj b φ y) := by
  classical
  intro B X I hI hPins l Z u a Ch A hA θ hθ j hj φ hφ b y
  obtain ⟨hreps, -, -⟩ := GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hI hPins l Z u a Ch A hA j hj b
  have hchi := GlobalTheory.T.continuous_chartLevelCharacters_adelic_tuple I hI hPins l Z u a Ch A hA j hj b
  obtain ⟨hval, hrd⟩ := GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hI hPins l Z u a Ch A hA θ hθ j hj φ hφ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X j).gram
  rw [continuous_iff_continuousAt]
  intro g0
  obtain ⟨γ, hγ, c, k, hk, κ, hκ, e0⟩ := hreps.dec g0
  obtain ⟨P, -, hP⟩ := hval c.1
  let V := (I.rec7 l Z).sp.X j
  let hn := rankN (I.rec7 l Z) j hj
  have hpc : Continuous fun g : GA (I.rec7 l Z) V => GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) :=
    (GlobalTheory.AdForm.RdLaw.continuous_pf V).comp (continuous_mul_left g0⁻¹)
  let p : GA (I.rec7 l Z) V → GfC V := fun g => ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), GlobalTheory.AdForm.RdLaw.pf_fin V _⟩
  have hp : Continuous p := hpc.subtype_mk _
  let O : Set (GA (I.rec7 l Z) V) := {g | GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b}
  have hO : IsOpen O := by
    have h1 := hreps.opn.preimage hp
    have e : O = p ⁻¹' (((A.U j b).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) := by
      ext g
      show GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b ↔ p g ∈ (A.U j b).subgroupOf (GfC V)
      rw [Subgroup.mem_subgroupOf]
    rw [e]; exact h1
  have hg0 : g0 ∈ O := by
    show GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g0) ∈ A.U j b
    rw [inv_mul_cancel, GlobalTheory.AdForm.RdLaw.pf_one]; exact one_mem _
  let G : GA (I.rec7 l Z) V → ℂ := fun g =>
    if h : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b then ((A.chi j b ⟨_, h⟩ : ℂˣ) : ℂ) else 0
  have hG : ContinuousAt G g0 := by
    have hc : ContinuousOn G O := by
      rw [continuousOn_iff_continuous_restrict]
      have e : (fun x : O => G x.1) = fun x : O => ((A.chi j b ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * x.1), x.2⟩ : ℂˣ) : ℂ) := by
        funext x
        exact dif_pos x.2
      show Continuous fun x : O => G x.1
      rw [e]
      exact hchi.comp ((hpc.comp continuous_subtype_val).subtype_mk _)
    exact hc.continuousAt (hO.mem_nhds hg0)
  let M : GA (I.rec7 l Z) V → (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ :=
    fun g τ => (show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ V hn k τ * infM θ V hn (g0⁻¹ * g) τ) * y.1 τ
  have hMu : ∀ g τ, IsUnit (M g τ).det := fun g τ => by
    simp only [M]
    erw [det_mul, det_mul]
    exact ((GlobalTheory.AdForm.RdVal.infM_unit θ V hn k τ).mul (GlobalTheory.AdForm.RdVal.infM_unit θ V hn _ τ)).mul (y.2 τ)
  have hM : ∀ τ, Continuous fun g =>
      (1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * M g τ := by
    intro τ
    have h1 : Continuous fun g : GA (I.rec7 l Z) V => infM θ V hn (g0⁻¹ * g) τ :=
      (continuous_infM' θ hθ V hn τ).comp (continuous_mul_left g0⁻¹)
    show Continuous fun g : GA (I.rec7 l Z) V => (1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * ((show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ V hn k τ * infM θ V hn (g0⁻¹ * g) τ) * y.1 τ)
    exact continuous_const.matrix_mul ((continuous_const.matrix_mul h1).matrix_mul continuous_const)
  let Φ : GA (I.rec7 l Z) V → ℂ := fun g =>
    (∏ τ, ((1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * M g τ).det ^
      shiftOf (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j) τ) *
    MvPolynomial.eval (fun q : (I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N j) × Fin ((I.rec7 l Z).R.N j) =>
      ((1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) q.1 * M g q.1) q.2.1 q.2.2) P
  have hΦ : Continuous Φ := by
    refine Continuous.mul (continuous_finset_prod _ fun τ _ => ((hM τ).matrix_det).zpow₀ _ fun g => Or.inl ?_) ?_
    · rw [Pi.one_apply, one_mul]; exact (hMu g τ).ne_zero
    · exact (MvPolynomial.continuous_eval P).comp (continuous_pi fun q => (hM q.1).matrix_elem q.2.1 q.2.2)
  refine ContinuousAt.congr (f := fun g => ((A.chi j b ⟨κ, hκ⟩ : ℂˣ) : ℂ) * G g * Φ g)
    ((continuousAt_const.mul hG).mul hΦ.continuousAt) ?_
  filter_upwards [hO.mem_nhds hg0] with g hg
  have hU : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b := hg
  have hδi : (GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g) ∈ GinfC V := pf_inv_mul_mem V _
  have hδf : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ GfC V := GlobalTheory.AdForm.RdLaw.pf_fin V _
  have hκf : κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ GfC V := mul_mem (hreps.le hκ) hδf
  have eg : g = γ * (A.h j b c * (k * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)))) *
      (κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g)) := by
    have hc := Formalism.IndefR.Eqv.Act.comm_inf_fin hδi hκf
    calc g = g0 * (GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g))) := by group
      _ = γ * (A.h j b c * k) * ((κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g)) *
          ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g))) := by rw [e0]; group
      _ = γ * (A.h j b c * k) * (((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)) *
          (κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))) := by rw [hc]
      _ = _ := by group
  let y' : (I.chain l u a).Y j := ⟨M g, hMu g⟩
  have htr : IsTr (G := fun _ => 1) (infM θ V hn (k * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)))) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := by
    intro τ
    rw [infM_mul_pf θ V hn k (g0⁻¹ * g) τ]
    rfl
  have key := hrd b y γ hγ c _ (mul_mem hk hδi) ⟨κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), mul_mem hκ hU⟩ y' htr
  rw [show A.rd θ j hj b φ y g = _ from (congrArg (A.rd θ j hj b φ y) eg).trans key]
  have e1 : (⟨κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), mul_mem hκ hU⟩ : A.U j b) =
      ⟨κ, hκ⟩ * ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), hU⟩ := rfl
  have e2 : G g = ((A.chi j b ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), hU⟩ : ℂˣ) : ℂ) := dif_pos hU
  have e3 : Φ g = φ c.1 y' := congrFun hP ⟨M g, hMu g⟩
  rw [e1, map_mul, Units.val_mul, e2, e3, mul_assoc]

end GlobalTheory.AdForm.RamCont
