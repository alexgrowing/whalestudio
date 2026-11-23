import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.ChartVal

theorem infM_fin' {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V)
    (τ : D.what₂.Tau) : infM θ V hn k τ = 1 := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

end GlobalTheory.AdForm.ChartVal

open GlobalTheory.AdForm.ChartVal in

theorem GlobalTheory.AdForm.rd_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (i : ℕ) (hi : i ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi i, (∀ c, (fun z : FrN (I.rec7 l Z) (B.R.N i) => φ c ⟨z.1, z.2⟩) ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i)) ∧ ∀ β y, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X i), ∀ c, ∀ k ∈ GinfC ((I.rec7 l Z).sp.X i), ∀ (κ : A.U i β) (y' : (I.chain l u a).Y i), IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) i hi) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ → A.rd θ i hi β φ y (γ * (A.h i β c * k) * κ.1) = (A.chi i β κ : ℂ) * φ c.1 y' := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ i hi φ hφ
  let eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a i hi (A.bad i) (Ch i) (A.chOf i) (A.K i hi) eY
    ⟨A.kb i, hA.reads i hi⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  refine ⟨?_, ?_⟩
  · intro c
    obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF (A.chOf i c))
    have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hΨ).2) ((A.K i hi (A.chOf i c)).y ⟨c, rfl⟩) (Set.mem_univ _)
    have e2 : Ψ ((A.K i hi (A.chOf i c)).y ⟨c, rfl⟩) = fun z => φ c (eY.symm z) := congrFun he ⟨c, rfl⟩
    rw [e2] at hval
    exact hval

  · intro β y γ hγ c k hk κ y' hy
    obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF β)
    have hAd : Ψ ∈ AdFun (A.K i hi β).lev (embT (I.rec7 l Z)) := (Submodule.mem_inf.1 hΨ).1
    have hfun : (fun (c : {c // A.chOf i c = β}) (z : Frames (gramC (gramN (I.rec7 l Z) i hi) (embT (I.rec7 l Z)))) =>
        φ c.1 ⟨z.1, z.2⟩) = fun c => Ψ ((A.K i hi β).y c) := he.symm
    have laws := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
      (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
      (A.K i hi β).y (A.K i hi β).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF β) ⟨y.1, y.2⟩
    obtain ⟨hL, hK, hR, -⟩ := laws
    have hκ := (hA.U i hi β κ.1).1 κ.2
    obtain ⟨hκf, κ', hκ'⟩ := hκ
    have hchi := hA.chi i hi β κ κ' hκ'
    have hval := (GlobalTheory.AdForm.rdS_val (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
      (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
      (A.K i hi β).y (A.K i hi β).y_bij Ψ hAd ⟨y'.1, y'.2⟩ (A.h i β c)).2.2 ((A.K i hi β).y c) ⟨y'.1, y'.2⟩
      ((hA.h i hi β c).2.symm) (fun τ => by
        have h1 := infM_fin' θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (A.h i β c) (hA.h i hi β c).1 τ
        show y'.1 τ = infM θ _ _ (A.h i β c) τ * y'.1 τ
        erw [h1, Matrix.one_mul])
    show rdS θ _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (fun c z => φ c.1 ⟨z.1, z.2⟩) ⟨y.1, y.2⟩
      (γ * (A.h i β c * k) * κ.1) = _
    have e1 := hL γ hγ (A.h i β c * k * κ.1)
    have e2 := hK κ.1 hκf κ' hκ' (A.h i β c * k)
    have e3 := hR k hk ⟨y'.1, y'.2⟩ hy (A.h i β c)
    have e5 := congrArg (fun F => rdS θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y F
      ⟨y'.1, y'.2⟩ (A.h i β c)) hfun
    have e6 : Ψ ((A.K i hi β).y c) ⟨y'.1, y'.2⟩ = φ c.1 y' := (congrFun (congrFun hfun c) ⟨y'.1, y'.2⟩).symm
    have e4 := e3.trans (e5.trans (hval.trans e6))
    rw [mul_assoc]
    exact e1.trans (e2.trans (congrArg₂ (· * ·) (congrArg (fun x : ℂˣ => (x : ℂ)) hchi.symm) e4))
