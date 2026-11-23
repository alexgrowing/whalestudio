import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrcSingleApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveTopMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.TopTranslate

open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift

theorem infM_eq_reindex {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn g τ = (infMat D.sp.cm.sig V.gram (θ τ) g).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  rfl

theorem infPt_eq_infM {D : D7} (θ : InfFam D) (x : GA D D.sp.X') (τ : D.what₂.Tau) :
    ((infPt θ x τ : GL _ ℂ) : Matrix _ _ ℂ) = infM θ D.sp.X' (rankP D) x τ := by
  rw [infM_eq_reindex]
  exact GlobalTheory.Core.Rk.TopOnto.infN_eq (rankP D) x τ

theorem infPt_mul_inv {D : D7} (θ : InfFam D) (x : GA D D.sp.X') (τ : D.what₂.Tau) :
    (infPt θ x τ).1 * (infPt θ x⁻¹ τ).1 = 1 := by
  rw [← Units.val_mul, ← Pi.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem top_translate : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ (f : CXP R P t) v c, ∀ x ∈ GinfC (I.rec7 l Z).sp.X', f.1 v (h c * x * g.bT) = (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) * (I.per l u a).period (eW.symm (Pi.single c fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩)) (G' f) := by
  intro B X I _ _ l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w _ UT ε _ bad K eW _ _ hbT _ _ h hh G' hG' f v c x hx
  obtain ⟨v', e1, e2⟩ := GlobalTheory.Core.Rk.TopOnto.real_translate (J := levS _ R.βX (datXP R P t))
    (χ := levChi _ R.βX (datXP R P t)) hX.inf hj x hx v
  have ex : h c * x * g.bT = h c * g.bT * x := by
    rw [mul_assoc, GlobalTheory.PointAtPlaceHom.comm_of_mem _ hx hbT, ← mul_assoc]
  have key : j v' = fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩ := by
    funext y
    have h1 : j v' y = j v (frL _ (infPt R.θ x⁻¹) y) := by
      rw [← e1, lT_apply]
      refine congrArg (j v') (Subtype.ext (funext fun τ => ?_))
      show y.1 τ = _ * (_ * y.1 τ)
      rw [← Matrix.mul_assoc, infPt_mul_inv, Matrix.one_mul]
    rw [h1]
    refine (hJ v x hx ⟨(frL _ (infPt R.θ x⁻¹) y).1, (frL _ (infPt R.θ x⁻¹) y).2⟩ ⟨y.1, y.2⟩ fun τ => ?_).symm
    show y.1 τ = infM R.θ _ (rankP (I.rec7 l Z)) x τ * (_ * y.1 τ)
    rw [← infPt_eq_infM, ← Matrix.mul_assoc, infPt_mul_inv, Matrix.one_mul]
  rw [ex, ← e2 f.1 f.2 (h c * g.bT), hG' f c v' (h c) (hh c), key]

end GlobalTheory.AdForm.TopTranslate

end
