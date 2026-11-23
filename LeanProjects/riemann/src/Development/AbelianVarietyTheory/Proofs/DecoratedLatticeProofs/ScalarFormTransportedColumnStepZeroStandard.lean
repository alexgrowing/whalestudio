import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartLevelStandardBasePointEqMemberStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartCharacterEqMemberChartCharacterStdBStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRepresentativeDiffersByLevelStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.ZeroCongr
open Formalism.UG

theorem adFun_of_same {D : D7} {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {T f T' f' : ℕ}
    {bad bad' : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (S' : StepLevel D.host.F D.host.E (sigD D) J T' f' bad')
    (hU : ∀ x, x ∈ S.U ↔ x ∈ S'.U) (hchi : ∀ (x : S.U) (x' : S'.U), x.1 = x'.1 → S.chi x = S'.chi x')
    (Ψ) (hΨ : Ψ ∈ AdFun S' (embT D)) : Ψ ∈ AdFun S (embT D) := by
  intro γ hγ x x' κ h y y' hy
  rw [hchi κ ⟨κ.1, (hU _).1 κ.2⟩ rfl]
  exact hΨ γ hγ x x' ⟨κ.1, (hU _).1 κ.2⟩ h y y' hy

set_option maxHeartbeats 1000000 in

theorem rdS_congr (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (n : ℕ) (hn : V.rank = n)
    (J : Matrix (Fin n) (Fin n) D.host.E) (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) {T f T' f' : ℕ}
    {bad bad' : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (S' : StepLevel D.host.F D.host.E (sigD D) J T' f' bad')
    {cl cl' : Type} (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (yc' : cl' → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (hb' : Function.Bijective (fun c => (Quotient.mk'' (yc' c) : Cls S')))
    (lam : D.what₂.Tau → DomWeight n) (φ) (φ') (hφ' : φ' ∈ FiC S' (embT D) lam yc')
    (hU : ∀ x, x ∈ S.U ↔ x ∈ S'.U) (hchi : ∀ (x : S.U) (x' : S'.U), x.1 = x'.1 → S.chi x = S'.chi x')
    (hrep : ∀ c, ∃ c', ∃ κ : S.U, (yc' c').1 = (yc c).1 * κ.1 ∧ S.chi κ = 1 ∧ φ c = φ' c')
    (y : Frames (gramC J (embT D))) (g : GA D V) :
    rdS θ V hn S yc φ y g = rdS θ V hn S' yc' φ' y g := by
  obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hφ'
  have hA' := (Submodule.mem_inf.1 hΨ).1
  have hA := adFun_of_same S S' hU hchi Ψ hA'
  have e : φ = fun c => Ψ (yc c) := by
    funext c z
    obtain ⟨c', κ, hy, hχ, hφc⟩ := hrep c
    rw [hφc]
    have h1 : IsTr (atInf (embT D) ((1 : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) z z := fun τ => by
      show z.1 τ = _ * z.1 τ
      simp [atInf]
    have e3 := hA 1 (Subgroup.one_mem _) (yc c) (yc' c') κ (by rw [map_one, one_mul]; try exact hy) z z h1
    show Ψ (yc' c') z = Ψ (yc c) z
    rw [e3, hχ, Units.val_one, one_mul]
  subst e
  obtain ⟨⟨x, hx⟩, hu, hv⟩ := GlobalTheory.AdForm.rdS_val D θ hθ V n hn J hJ T f bad S cl yc hb Ψ hA y g
  obtain ⟨-, -, hv'⟩ := GlobalTheory.AdForm.rdS_val D θ hθ V n hn J hJ T' f' bad' S' cl' yc' hb' Ψ hA' y g
  let z : Frames (gramC J (embT D)) :=
    ⟨fun τ => infM θ V hn g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hu τ).mul (y.2 τ)⟩
  exact (hv x z hx (fun τ => rfl)).trans (hv' x z hx (fun τ => rfl)).symm

end GlobalTheory.AdForm.ZeroCongr

namespace GlobalTheory.Fam

set_option maxHeartbeats 4000000 in

theorem rd_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ θ, IsInfFam θ → ∀ ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram, ∀ y, A.rd θ 0 (Nat.zero_le _) β ((I.rec7 l Z).e0Tw u a ψ₀) y = (GlobalTheory.Core.Mi.chart0 (C.forms u).to0).rd θ ψ₀ y := by
  intro B X I hI hP l Z C hC u a Ch A hA β hβ θ hθ ψ₀ hψ y
  unfold GlobalTheory.AdForm.TwDat.rd GlobalTheory.AdForm.Chart.rd GlobalTheory.Core.Mi.chart0
  dsimp only
  have hfr : ((C.forms u).to0.val0.eY y) = (⟨y.1, y.2⟩ : Frames (gramC (gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (embT (I.rec7 l Z)))) :=
    Subtype.ext ((hC u).eY 0 (Nat.zero_le _) (Or.inl rfl) y)
  rw [hfr]
  funext g
  refine GlobalTheory.AdForm.ZeroCongr.rdS_congr (I.rec7 l Z) θ hθ _ _ _ _ ?hJ _ _ _ _ (A.K 0 (Nat.zero_le _) β).y_bij ((C.forms u).to0.cls0.toChart.y_bij) (lamT u 0) _ _ ?hφ ?hU ?hchi ?hrep _ g
  case hJ => rfl
  case hφ => exact ((C.forms u).to0.val0.Fi ψ₀).1 (((I.rec7 l Z).fm u).Fi_zero ▸ hψ.1)
  case hU => exact GlobalTheory.T.stepZeroChartLevel_standardBasePoint_eq_member I hI hP l Z C hC u a Ch A hA β hβ
  case hchi => exact GlobalTheory.T.levelZeroChartCharacter_eq_memberChartCharacter_stdBase I hI hP l Z C hC u a Ch A hA β hβ
  case hrep =>
    intro c
    obtain ⟨κ, h1, h2⟩ := GlobalTheory.T.stepZero_representative_differs_by_level I hI hP l Z C hC u a Ch A hA β hβ c
    refine ⟨(I.eCls0 l u a).symm c.1, κ, h1, h2, ?_⟩
    funext z
    have hz : (C.forms u).to0.val0.eY.symm z = ⟨z.1, z.2⟩ := by
      apply (C.forms u).to0.val0.eY.injective
      rw [Equiv.apply_symm_apply]
      exact Subtype.ext ((hC u).eY 0 (Nat.zero_le _) (Or.inl rfl) _).symm
    rw [hz]
    rfl

end GlobalTheory.Fam

end
