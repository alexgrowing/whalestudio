import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedLevelStabilizerIffAllDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTupleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleColumnScalarAdelicFormContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiamondTranslatesScalarFormsSumIffStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem rd_mul_level {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is)
    (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ) (j : ℕ) (hj : j ≤ B.R.m) (φ : ColT I l u a j) (hφ : φ ∈ (I.fm l u a).Fi j)
    (b : Ch j) (y : (I.chain l u a).Y j) (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (γ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hγ : γ ∈ GQ ((I.rec7 l Z).sp.X j)) (κ : A.U j b) :
    A.rd θ j hj b φ y (γ * x * κ.1) = (A.chi j b κ : ℂ) * A.rd θ j hj b φ y x := by
  obtain ⟨γ0, hγ0, c, k0, hk0, κ0, hκ0, rfl⟩ := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hP l Z u a Ch A hA j hj b).1.dec x
  have hrd := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ).2 b y
  let y' : (I.chain l u a).Y j := ⟨fun τ => (show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ _ (rankN (I.rec7 l Z) j hj) k0 τ) * y.1 τ, fun τ => by
    rw [Matrix.det_mul]; exact (GlobalTheory.AdForm.RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) k0 τ).mul (y.2 τ)⟩
  have hy' : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) k0) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := fun _ => rfl
  rw [hrd γ0 hγ0 c k0 hk0 ⟨κ0, hκ0⟩ y' hy']
  have e : γ * (γ0 * (A.h j b c * k0) * κ0) * κ.1 = (γ * γ0) * (A.h j b c * k0) * ((⟨κ0, hκ0⟩ : A.U j b) * κ).1 := by
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [e, hrd (γ * γ0) (Subgroup.mul_mem _ hγ hγ0) c k0 hk0 (⟨κ0, hκ0⟩ * κ) y' hy', map_mul, Units.val_mul]
  ring

theorem ram_iff_scalar_ram : TwRam' := by
  intro B X I hOk hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hStd j hj φ hφ
  have hlaw := rd_mul_level I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ
  have hcont : ∀ b y, IsContAut _ (A.rd θ j hj b φ y) := fun b y =>
    ⟨fun γ hγ g => by simpa using hlaw b y g γ hγ 1, GlobalTheory.T.tupleColumn_scalarAdelicForm_continuous I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ b y⟩
  refine ⟨hcont, ?_⟩
  obtain ⟨e, he⟩ := hStd.1
  have : Finite ι := Finite.of_equiv _ e.symm
  haveI := Fintype.ofFinite ι
  have hlev := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a Ch A hA k ι p β Q L hStd (Finset.univ.toList) (Finset.nodup_toList _)
    (fun i => Finset.mem_toList.2 (Finset.mem_univ i)) j hj
  have hfix : ∀ b y i (x : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), x • Q j i = Q j i →
      rTrans ((β j i).gl x) (A.rd θ j hj b φ y) = A.rd θ j hj b φ y := by
    intro b y i x hx
    obtain ⟨hm, h1⟩ := (hlev b).1 i x hx
    funext g
    have := hlaw b y g 1 (Subgroup.one_mem _) ⟨_, hm⟩
    simpa [rTrans, h1] using this
  choose gS hgS using fun (i : ι) (s : 𝓀[k]ˣ) =>
    MulAction.exists_smul_eq (GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (Q j i) (s • Q j i)
  have hram : ∀ b y i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y) ↔
      ∑ᶠ s, rTrans ((β j i).gl (gS i s)) (A.rd θ j hj b φ y) = 0 := by
    intro b y i
    rw [GlobalTheory.T.ramifiedLevel_stabilizer_iff_all_data (I.rec7 l Z) k (p i) (Fin _) _ (β j i) (Q j i) (gS i) (hgS i)]
    exact ⟨fun h => h.2.2, fun h => ⟨hcont b y, fun x hx => hfix b y i x hx, h⟩⟩
  have hdia := fun i => GlobalTheory.T.diamondTranslates_scalarForms_sum_iff I hOk hP l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ i (e i) (he i) (gS i) (hgS i)
  simp only [hram]
  unfold RamT
  constructor
  · rintro ⟨-, hR⟩ b y i
    exact (hdia i).2 (fun c => hR (e i) c) b y
  · intro h
    refine ⟨hφ, fun v c => ?_⟩
    obtain ⟨i, rfl⟩ := e.surjective v
    exact (hdia i).1 (fun b y => h b y i) c

end GlobalTheory.AdForm
