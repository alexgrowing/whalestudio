import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueChainKernelEqClassSumJetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.ClsKLive

theorem kval : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Kval := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  intro j hj hab φ hφ Fv hV hval γ a' y'
  have hj1 : j + 1 ≤ B.R.m := hj
  have hinj : Function.Injective (ι j) := hP.live.inj j
  have hram := ((hP.ram j hj.le φ).1 hφ).2
  let Fc : (I.chain l u a).cls j → PY (I.rec7 l Z).what₂.Tau (B.R.N j) := fun c =>
    if h : ∃ β, A.chOf j c = ι j β then Fv h.choose ⟨c, h.choose_spec⟩ else 0
  have hFcEq : ∀ β (c : {c // A.chOf j c = ι j β}), Fc c.1 = Fv β c := by
    intro β c
    have h : ∃ β, A.chOf j c.1 = ι j β := ⟨β, c.2⟩
    have hb : h.choose = β := hinj (h.choose_spec.symm.trans c.2)
    have gen : ∀ β' (hβ' : A.chOf j c.1 = ι j β'), β' = β → Fv β' ⟨c.1, hβ'⟩ = Fv β c := by
      rintro β' hβ' rfl; rfl
    simp only [Fc, dif_pos h]
    exact gen _ _ hb
  have hFc : ∀ c y, φ c y = evalAt y.1 (Fc c) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp j τ) := by
    intro c y
    by_cases h : ∃ β, A.chOf j c = ι j β
    · obtain ⟨β, hβ⟩ := h
      rw [hFcEq β ⟨c, hβ⟩]
      exact hval β ⟨c, hβ⟩ ⟨y.1, y.2⟩
    · have h0 : Fc c = 0 := by simp only [Fc, dif_neg h]
      rw [h0, show φ c y = 0 by rw [hram c (fun ⟨β, hβ⟩ => h ⟨β, hβ.symm⟩)]; rfl]
      have hz : KJInf.evalAt y.1 (0 : PY (I.rec7 l Z).what₂.Tau (B.R.N j)) = 0 := map_zero (MvPolynomial.eval _)
      rw [hz, zero_mul]
  have key := GlobalTheory.T.trueChainKernel_eq_classSum_jets I hOk hPins l Z u a Ch₀ A hP.is j hj1 hab φ Fc hFc a'.1 ⟨y'.1, y'.2⟩
  have e0 : (clsKL R g P r k tl s J A ι).val (j + 1) γ ((tupOf R P u g t r k tl).K j φ) a' y' = (I.chain l u a).K j φ a'.1 ⟨y'.1, y'.2⟩ := rfl
  rw [e0, key]
  letI := (I.chain l u a).clsFin j
  letI : Fintype ((tupOf R P u g t r k tl).Ch j) := (tupOf R P u g t r k tl).fin j
  rw [finsum_eq_sum_of_fintype]
  symm
  refine (Fintype.sum_sigma (fun x : (Σ β : (tupOf R P u g t r k tl).Ch j, (clsKL R g P r k tl s J A ι).cl j β) =>
      ((stabOrd (A.U j (ι j x.1)) (A.h j (ι j x.1) x.2) : ℕ) : ℂ)⁻¹ * A.abelian₂ j x.2.1 a'.1 (subY hab y'.1 (Fv x.1 x.2)) *
        ∏ τ, (y'.1 τ).det ^ (-(I.chain l u I.mu0).sDiv j τ))).symm.trans ?_
  refine Fintype.sum_of_injective (fun x => x.2.1) ?_ _ _ ?_ ?_
  · rintro ⟨β, c, hc⟩ ⟨β', c', hc'⟩ h
    simp only at h
    subst h
    have hb : β = β' := hinj (hc.symm.trans hc')
    subst hb
    rfl
  · intro c hc
    have h : ¬ ∃ β, A.chOf j c = ι j β := fun ⟨β, hβ⟩ => hc ⟨⟨β, c, hβ⟩, rfl⟩
    have h0 : Fc c = 0 := by simp only [Fc, dif_neg h]
    rw [h0]
    erw [map_zero (subY hab _), map_zero, mul_zero, zero_mul]
  · rintro ⟨β, c⟩
    have hst := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hPins l Z u a Ch₀ A hP.is j hj.le (ι j β)).2.2 c
    simp only
    rw [hFcEq β c, hst]
    rfl

end GlobalTheory.AdForm.ClsKLive
