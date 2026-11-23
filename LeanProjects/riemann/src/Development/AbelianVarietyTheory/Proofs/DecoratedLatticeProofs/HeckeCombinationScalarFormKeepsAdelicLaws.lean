import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTupleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.TransLaw

theorem trc_apply' {D : D7} {V : HSp D} (c : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc c f x = ∑ g ∈ c.support, c g * f (x * g) := by
  simp [trc, rTrans, Finset.sum_apply]

theorem list_prod_right {G : Type} [Group G] (F : G → ℂ) (L : List G) (hL : ∀ a ∈ L, ∀ z, F (z * a) = F z) (z : G) :
    F (z * L.prod) = F z := by
  induction L generalizing z with
  | nil => simp
  | cons a L ih =>
    rw [List.prod_cons, ← mul_assoc, ih (fun b hb => hL b (List.mem_cons_of_mem _ hb)) (z * a), hL a List.mem_cons_self]

theorem list_prod_chi {G : Type} [Group G] (U : Subgroup G) (χ : U →* ℂˣ) (L : List G)
    (hL : ∀ a ∈ L, ∃ h : a ∈ U, χ ⟨a, h⟩ = 1) : ∃ h : L.prod ∈ U, χ ⟨_, h⟩ = 1 := by
  induction L with
  | nil => exact ⟨U.one_mem, χ.map_one⟩
  | cons a L ih =>
    obtain ⟨ha, hχa⟩ := hL a List.mem_cons_self
    obtain ⟨hP, hχP⟩ := ih (fun b hb => hL b (List.mem_cons_of_mem _ hb))
    refine ⟨by rw [List.prod_cons]; exact U.mul_mem ha hP, ?_⟩
    have e : (⟨(a :: L).prod, by rw [List.prod_cons]; exact U.mul_mem ha hP⟩ : U) = ⟨a, ha⟩ * ⟨L.prod, hP⟩ := by
      apply Subtype.ext; simp [List.prod_cons]
    rw [e, map_mul, hχa, hχP, one_mul]

set_option maxHeartbeats 1000000 in
theorem rd_laws {B : Base} {X : PreX B.toPre} (I : TC B X) (hok : I.Ok) (hpins : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is) (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ)
    (j : ℕ) (hj : j ≤ B.R.m) (φ : ColT I l u a j) (hφ : φ ∈ (I.fm l u a).Fi j) (b : Ch j) (y : (I.chain l u a).Y j) :
    (∀ γ ∈ GQ ((I.rec7 l Z).sp.X j), ∀ g, A.rd θ j hj b φ y (γ * g) = A.rd θ j hj b φ y g) ∧
    (∀ κ : A.U j b, ∀ g, A.rd θ j hj b φ y (g * κ.1) = (A.chi j b κ : ℂ) * A.rd θ j hj b φ y g) ∧
    (∀ k ∈ GinfC ((I.rec7 l Z).sp.X j), ∀ y' : (I.chain l u a).Y j,
      IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ →
      ∀ g, A.rd θ j hj b φ y (g * k) = A.rd θ j hj b φ y' g) := by
  let eY : (I.chain l u a).Y j ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) j hj :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a j hj (A.bad j) (Ch j) (A.chOf j) (A.K j hj) eY
    ⟨A.kb j, hA.reads j hj⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  obtain ⟨hL, hK, hR, -⟩ := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X j) (B.R.N j) (rankN (I.rec7 l Z) j hj)
      (gramN (I.rec7 l Z) j hj) rfl (B.T u) (I.rec7 l Z).R.f (A.bad j) (A.K j hj b).lev {c // A.chOf j c = b}
      (A.K j hj b).y (A.K j hj b).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF b) ⟨y.1, y.2⟩
  refine ⟨fun γ hγ g => hL γ hγ g, fun κ g => ?_, fun k hk y' hy g => hR k hk ⟨y'.1, y'.2⟩ hy g⟩
  obtain ⟨hκf, κ', hκ'⟩ := (hA.U j hj b κ.1).1 κ.2
  rw [hA.chi j hj b κ κ' hκ']
  exact hK κ.1 hκf κ' hκ' g

end GlobalTheory.AdForm.TransLaw

open GlobalTheory.AdForm.TransLaw in
set_option maxHeartbeats 2000000 in

theorem GlobalTheory.AdForm.trc_rd_laws : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ b y, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X j), ∀ (e : {e // A.chOf j e = b}), ∀ g ∈ GinfC ((I.rec7 l Z).sp.X j), ∀ (κ : A.U j b) (y' : (I.chain l u a).Y j),
        IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) g) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ →
        trc c (A.rd θ j hj b φ y) (γ * (A.h j b e * g) * κ.1) = (A.chi j b κ : ℂ) * trc c (A.rd θ j hj b φ y') (A.h j b e) := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ K _ _ _ _ ι p β Q L hT j hj c hc φ hφ hinv b y γ hγ e g0 hg0 κ y' hy
  obtain ⟨hLy, hKy, hRy⟩ := rd_laws I hok hpins l Z u a Ch A hA θ hθ j hj φ hφ b y
  have hT' := hT
  obtain ⟨⟨eι, -⟩, -⟩ := hT'
  haveI : Fintype ι := Fintype.ofEquiv _ eι.symm
  obtain ⟨hstab, hdec⟩ := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hok hpins l Z u a Ch A hA K ι p β Q L hT Finset.univ.toList
    (Finset.nodup_toList _) (fun i => Finset.mem_toList.2 (Finset.mem_univ _)) j hj b
  obtain ⟨gs, hgs, κ', hκ'off, hκeq⟩ := hdec κ.1 κ.2
  set s := (Finset.univ.toList.map fun i => (β j i).gl (gs i)).prod with hs
  obtain ⟨hsU, hχs⟩ := list_prod_chi (A.U j b) (A.chi j b) (Finset.univ.toList.map fun i => (β j i).gl (gs i)) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hstab i (gs i) (hgs i))
  have hκ'U : κ' ∈ A.U j b := by
    have : κ' = s⁻¹ * κ.1 := by rw [hκeq, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]; exact (A.U j b).mul_mem ((A.U j b).inv_mem hsU) κ.2
  have hχκ : A.chi j b κ = A.chi j b ⟨κ', hκ'U⟩ := by
    have e1 : κ = (⟨s, hsU⟩ : A.U j b) * ⟨κ', hκ'U⟩ := Subtype.ext hκeq
    rw [e1, map_mul, hχs, one_mul]
  set F := trc c (A.rd θ j hj b φ y) with hF

  have hcomm : ∀ g' ∈ c.support, κ' * g' = g' * κ' := fun g' hg' =>
    ((GlobalTheory.FinPlLoc.part_grp (fun x => ∃ i, x = (p i).v) ((I.rec7 l Z).sp.X j)).2.1 g' (hc g' hg') κ' hκ'off).symm

  have step1 : ∀ x, F (x * κ.1) = (A.chi j b κ : ℂ) * F (x * s) := by
    intro x
    rw [hF, trc_apply', trc_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl fun g' hg' => ?_
    rw [hκeq, ← mul_assoc, mul_assoc (x * s), hcomm g' hg', ← mul_assoc, hKy ⟨κ', hκ'U⟩, hχκ]
    ring

  have step2 : ∀ x, F (x * s) = F x := by
    intro x
    refine list_prod_right F _ ?_ x
    intro a' ha' z
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha'
    exact congrFun (hinv b y i (gs i) (hgs i)) z

  have step3 : F (γ * (A.h j b e * g0)) = trc c (A.rd θ j hj b φ y') (A.h j b e) := by
    rw [hF, trc_apply', trc_apply']
    refine Finset.sum_congr rfl fun g' hg' => ?_
    have hfin : g' ∈ GfC ((I.rec7 l Z).sp.X j) := GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hc g' hg')
    rw [mul_assoc γ, hLy γ hγ, mul_assoc, ← GlobalTheory.FinTranslate.comm_fin_real _ hfin hg0, ← mul_assoc,
      hRy g0 hg0 y' hy]
  rw [step1, step2, step3]
