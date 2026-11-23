import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOOnb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCharExponentInfinityKernelShiftStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteLiftCommLevelPrimeOperators
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KJRealLive

theorem castP_mvZ {D : D7} {p q a b : ℕ} (hp : p = a) (hq : q = b) (M : D.what₂.Tau → Matrix (Fin p) (Fin p) ℂ)
    (M' : D.what₂.Tau → Matrix (Fin q) (Fin q) ℂ) (P : PolF D q p) :
    castP (D := D) hp hq (mvZ M M' P) =
      mvZ (fun τ => (M τ).reindex (finCongr hp) (finCongr hp)) (fun τ => (M' τ).reindex (finCongr hq) (finCongr hq))
        (castP (D := D) hp hq P) := by
  subst hp; subst hq
  rw [Sized.castP_rank, Sized.castP_rank]
  have h : ∀ n (N : Matrix (Fin n) (Fin n) ℂ), N.reindex (finCongr rfl) (finCongr rfl) = N := fun n N => by ext; simp
  simp only [h]

theorem comb_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : WO S T →₀ ℂ) (x : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (x • f) = x • comb ψ S T c f := by
  funext u
  simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.KJRealLive

open GlobalTheory.KJRealLive in

theorem GlobalTheory.KJRealLive.clsKL_real : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Real := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  intro j hj α γ k₁ hk₁ k₂ hk₂ P₁ P₂ hP₁₂
  have hjle : j ≤ B.R.m := Nat.le_of_succ_le hj
  have hjlt : j < B.R.m := hj
  obtain ⟨e, he, hee⟩ := GlobalTheory.T.exists_charExponent_infinity_kernel_shift I hOk hPins l Z u a Ch₀ A hP.is j hj
  have hvac := hX.vc j hjlt
  have hxj := hX.xs j hjle
  have hxj1 := hX.xs (j + 1) hj
  have hW := hP.om j hjlt
  have hfin := (hP.dat j hj α γ).1
  have hstd := hX.std
  have hth0 : IsThetaFunO R.ψ _ _ (g.vac j) := hvac.2.theta
  have eS : Even ((I.rec7 l Z).sp.X j).rank := by rw [rankN (I.rec7 l Z) j hjle]; exact even_rankN _ j
  have eT : Even ((I.rec7 l Z).sp.X (j + 1)).rank := by rw [rankN (I.rec7 l Z) (j + 1) hj]; exact even_rankN _ (j + 1)
  have key := GlobalTheory.KJReal.om_pureTensorO_onb (I.rec7 l Z) R.ψ R.θ _ _ (g.x j) (g.x (j + 1)) (A.chr (j + 1)) (k.kom j) hX.inf
    (hx j hjle) (hx (j + 1) hj) hxj.1 hxj1.1 eS eT hW e he (g.vac j) hth0 hvac.2.fock k₁ hk₁ k₂ hk₂
  have hPP : P₂ = mvZ (fun τ => (inB R.θ _ (g.x j).B k₁ τ)⁻¹) (inB R.θ _ (g.x (j + 1)).B k₂) P₁ := by
    apply (Sized.castP_bijective (D := I.rec7 l Z) (rankN (I.rec7 l Z) j hjle) (rankN (I.rec7 l Z) (j + 1) hj)).1
    refine hP₁₂.trans ?_
    rw [castP_mvZ]
    congr 2
    funext τ
    exact Matrix.inv_reindex _ _ _
  have hs1 : ∀ τ, (realOf u R g s J).sS j τ = -e τ - (((I.rec7 l Z).sp.X (j + 1)).rank : ℤ) / 2 := fun τ => (hee τ).1
  have hs2 : ∀ τ, -(realOf u R g s J).sD j τ = e τ + (((I.rec7 l Z).sp.X j).rank : ℤ) / 2 := fun τ => (hee τ).2.1
  have hpt0 : IsThetaFunO R.ψ _ _ (pureTensorO R.ψ R.θ _ _ (g.x j).s (g.x (j + 1)).s (g.x j).B (g.x (j + 1)).B (g.vac j) P₁) :=
    GlobalTheory.FockTheta.ptStable _ R.ψ R.θ hstd hX.inf _ _ _ _ _ _ _ P₁ hth0
  show k.kom j (k₁, k₂) (pureTensorO R.ψ R.θ _ _ (g.x j).s (g.x (j + 1)).s (g.x j).B (g.x (j + 1)).B
    (comb R.ψ _ _ (k.dd j α γ) (g.vac j)) P₁) = _ • pureTensorO R.ψ R.θ _ _ (g.x j).s (g.x (j + 1)).s (g.x j).B (g.x (j + 1)).B
    (comb R.ψ _ _ (k.dd j α γ) (g.vac j)) P₂
  rw [LiftsAtLevel.comb_pureTensorO hstd hX.inf _ _ _ _ hth0 hfin, GlobalTheory.FrComb.om_comb hW hk₁ hk₂ hfin hpt0, key, comb_smul,
    LiftsAtLevel.comb_pureTensorO hstd hX.inf _ _ _ _ hth0 hfin, hPP]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hs1 τ, hs2 τ]
  show _ = ((inB R.θ _ (g.x j).B k₁ τ).reindex _ _).det ^ _ * ((inB R.θ _ (g.x (j + 1)).B k₂ τ).reindex _ _).det ^ _
  rw [Matrix.det_reindex_self, Matrix.det_reindex_self]
