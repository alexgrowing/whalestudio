import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem trc_single_apply {D : D7} {V : HSp D} (b : GA D V) (ε : ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc (Finsupp.single b ε) f x = ε * f (x * b) := by
  unfold trc
  by_cases hε : ε = 0
  · simp [hε]
  · rw [Finsupp.support_single_ne_zero _ hε]
    simp [GlobalTheory.MixPer.rTrans]
end GlobalTheory.AdForm

noncomputable section
namespace GlobalTheory.AdForm

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))
  (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) {t : T} (r : RowCh R P u g t) (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

def ellTop (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)) (ε : ℂ)
    (G' : CXP R P t → (I.per l u a).Mt) (c : (I.fm l u a).clsP) (f : CXP R P t) :
    (FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) →ₗ[ℂ] ℂ :=
  (ε * (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ)) •
    ((I.per l u a).period.flip (G' f) ∘ₗ eW.symm.toLinearMap ∘ₗ
      LinearMap.single ℂ (fun _ : (I.fm l u a).clsP => FrP (I.rec7 l Z) → ℂ) c ∘ₗ
      LinearMap.funLeft ℂ ℂ (fun y : FrP (I.rec7 l Z) => (⟨y.1, y.2⟩ : FrN (I.rec7 l Z) (B.R.N B.R.m - 1))))

theorem ellTop_apply (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)) (ε : ℂ)
    (G' : CXP R P t → (I.per l u a).Mt) (c : (I.fm l u a).clsP) (f : CXP R P t) (φ : FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) :
    ellTop R P eW ε G' c f φ = ε * (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) *
      (I.per l u a).period (eW.symm (Pi.single c (fun y : FrP (I.rec7 l Z) => φ ⟨y.1, y.2⟩))) (G' f) := by
  simp only [ellT, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, LinearMap.flip_apply,
    LinearEquiv.coe_coe, LinearMap.coe_single, smul_eq_mul]
  rfl

@[reducible] def clsTop (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ)
    (UT : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) (h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X')
    (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)) (ε : ℂ) (G' : CXP R P t → (I.per l u a).Mt) :
    ClsT (realOf u R g s J) (tupOf R P u g t r k tl) where
  cl := (I.fm l u a).clsP
  U := UT
  h := h
  ell := fun _ _ _ c f => ellTop R P eW ε G' c f

end GlobalTheory.AdForm
end
