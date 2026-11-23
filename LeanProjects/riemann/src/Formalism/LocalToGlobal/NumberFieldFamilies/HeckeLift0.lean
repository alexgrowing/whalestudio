import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCBase

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N Formalism.L2

namespace Formalism.L2.Fam.NPC.BaseC

variable {R : Ranks} (H : Host R) (what₂ : Rows.Data R)

structure MtReal0 (μ : what₂.Tup) (j : ℕ) where
  wt : NG.AlgWt H.E R.nV
  J : Subgroup (GAf H.E R.nV)
  χ : J →* ℂˣ
  J_open : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong H.E R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1
  real : what₂.Mt μ j →ₗ[ℂ] (GAf H.E R.nV → wt.W)
  real_inj : Function.Injective real
  real_range : LinearMap.range real = NG.TypeSp wt.ρ J χ

abbrev MtFam0 : Type 1 := ∀ (μ : what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ R.m → MtReal0 H what₂ μ j

variable {H what₂}

def HeckeLift0 (M : MtFam0 H what₂) (Qw : what₂.places.Pl → Finset (HeightOneSpectrum (𝓞 H.E))) : Prop :=
  ∀ (j : ℕ) (w : what₂.places.Pl) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ R.m),
    GenAt0 H (what₂.places.resChar w) (Qw w) v k →
    ∃ T : Module.End what₂.LL (what₂.MtL (what₂.muTw w) j), ∀ (s : SplitPlace H.E)
      (ϖ : HeightOneSpectrum.adicCompletion (↥(maximalRealSubfield H.E)) s.v),
      IsConjPl H v s.w → IsUnif H.E s.v ϖ → ∀ x,
        (M (what₂.muTw w) j h1 h2).real (what₂.jMt (what₂.muTw w) j (T x)) = NG.tN (M (what₂.muTw w) j h1 h2).J s ϖ k ((M (what₂.muTw w) j h1 h2).real (what₂.jMt (what₂.muTw w) j x))

variable (M : MtFam0 H what₂) (Qw : what₂.places.Pl → Finset (HeightOneSpectrum (𝓞 H.E))) (hR : HeckeLift0 M Qw)

open Classical in

def hLC (j : ℕ) (w : what₂.places.Pl) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) :
    Module.End what₂.LL (what₂.MtL (what₂.muTw w) j) :=
  if h : (1 ≤ j ∧ j ≤ R.m) ∧ GenAt0 H (what₂.places.resChar w) (Qw w) v k then (hR j w v k h.1.1 h.1.2 h.2).choose else 0

theorem hLC_spec (j : ℕ) (w : what₂.places.Pl) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ R.m)
    (hg : GenAt0 H (what₂.places.resChar w) (Qw w) v k) (s : SplitPlace H.E)
    (ϖ : HeightOneSpectrum.adicCompletion (↥(maximalRealSubfield H.E)) s.v) (hc : IsConjPl H v s.w) (hu : IsUnif H.E s.v ϖ)
    (x : what₂.MtL (what₂.muTw w) j) :
    (M (what₂.muTw w) j h1 h2).real (what₂.jMt (what₂.muTw w) j (hLC M Qw hR j w v k x)) =
      NG.tN (M (what₂.muTw w) j h1 h2).J s ϖ k ((M (what₂.muTw w) j h1 h2).real (what₂.jMt (what₂.muTw w) j x)) := by
  have h : (1 ≤ j ∧ j ≤ R.m) ∧ GenAt0 H (what₂.places.resChar w) (Qw w) v k := ⟨⟨h1, h2⟩, hg⟩
  unfold hLC
  rw [dif_pos h]
  exact (hR j w v k h.1.1 h.1.2 h.2).choose_spec s ϖ hc hu x

variable (X : CoefIn what₂)

def hKC (j : ℕ) (w : what₂.places.Pl) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) :
    Module.End (FractionRing (OcC X j w)) (VC X j w) :=
  (hLC M Qw hR j w v k).baseChange (FractionRing (OcC X j w))

theorem hKC_def (j : ℕ) (w : what₂.places.Pl) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ) (x : what₂.MtL (what₂.muTw w) j) :
    hKC M Qw hR X j w v k (iVC X j w x) = iVC X j w (hLC M Qw hR j w v k x) :=
  LinearMap.baseChange_tmul _ _ _

def SplitK : Prop :=
  ∀ j w v k, GenAt0 H (what₂.places.resChar w) (Qw w) v k → ⨆ μ, (hKC M Qw hR X j w v k).maxGenEigenspace μ = ⊤

def baseC (hS : SplitK M Qw hR X) : LocBase0 H what₂ where
  Oc := OcC X
  Oc_adic := oc_adic X
  Oc_complete := oc_complete X
  ec := ecC X
  ec_w := ecC_w X
  V := VC X
  iV := iVC X
  iV_basis := iVC_basis X
  Qw := Qw
  hL := hLC M Qw hR
  hK := hKC M Qw hR X
  hK_def := hKC_def M Qw hR X
  split := hS

theorem baseC_Oc (hS : SplitK M Qw hR X) : (baseC M Qw hR X hS).Oc = OcC X := rfl
theorem baseC_hL (hS : SplitK M Qw hR X) : (baseC M Qw hR X hS).hL = hLC M Qw hR := rfl
theorem baseC_iV (hS : SplitK M Qw hR X) : (baseC M Qw hR X hS).iV = iVC X := rfl

end Formalism.L2.Fam.NPC.BaseC
