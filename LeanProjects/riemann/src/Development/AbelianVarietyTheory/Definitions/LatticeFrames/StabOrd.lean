import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BrEqv

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

abbrev FrN (D : D7) (n : ℕ) : Type := Frames (fun _ : D.what₂.Tau => (1 : Matrix (Fin n) (Fin n) ℂ))

def inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V) :
    D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => (B τ)⁻¹ * compAt θ τ (mt V g) * B τ

def volLev {V : HSp D} (v : Vol V) (U : Subgroup (GA D V)) : ℝ := (v.μ {g | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ}).toReal

def stabOrd {V : HSp D} (U : Subgroup (GA D V)) (h : GA D V) : ℕ :=
  Nat.card {γ : GQ V // ∃ k ∈ GinfC V, ∃ κ ∈ U, γ.1 * h = h * k * κ}

structure IsReps (V : HSp D) (U : Subgroup (GA D V)) {cl : Type} (h : cl → GA D V) : Prop where
  le : U ≤ GfC V
  cpt : IsCompact (U : Set (GA D V))
  opn : IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V))
  fin : ∀ c, h c ∈ GfC V
  dec : ∀ g, ∃ γ ∈ GQ V, ∃ c, ∃ k ∈ GinfC V, ∃ κ ∈ U, g = γ * (h c * k) * κ
  uniq : ∀ c c', ∀ γ ∈ GQ V, ∀ k ∈ GinfC V, ∀ κ ∈ U, h c' = γ * (h c * k) * κ → c = c'

structure RealC (c : Comm D) where
  fr : ∀ j, c.Fr j ≃ FrN D (c.X j).rank
  lam : ∀ j, D.what₂.Tau → DomWeight (c.X j).rank
  n : ℕ → D.what₂.Tau → ℕ
  sS : ℕ → D.what₂.Tau → ℤ
  sD : ℕ → D.what₂.Tau → ℤ
  sc : ℕ → D.what₂.Tau → ℂ
  BT : D.what₂.Tau → Matrix (Fin c.T.rank) (Fin c.T.rank) ℂ
  sg : D.what₂.Tau → DomWeight c.T.rank
  J : SmT c.MT → GA D c.T → FrN D c.T.rank → ℂ
  low : ∀ n, n = D.R.m → ((FrN D (c.X n).rank → ℂ) →ₗ[ℂ] (FrN D c.T.rank → ℂ))

abbrev Comm.r (c : Comm D) (j : ℕ) (g : GA D (c.X j)) := inB c.θ (c.X j) (c.x j).B g

structure RealC.Is {c : Comm D} (ρ : RealC c) : Prop where
  uni : ∀ j, j ≤ D.R.m → OntoUni fun k : GinfC (c.X j) => c.r j k.1
  uniT : OntoUni fun k : GinfC c.T => inB c.θ c.T ρ.BT k.1
  rk : ∀ j, j < D.R.m → 0 < (c.X j).rank ∧ (c.X j).rank ≤ (c.X (j + 1)).rank
  sc : ∀ j τ, ρ.sc j τ ≠ 0
  n : ∀ j, j < D.R.m → ∀ τ, (ρ.n j τ : ℤ) = shiftOf (ρ.lam j) τ + ρ.sS j τ
  J : ∀ v, ρ.J v 1 ∈ ValC _ ρ.sg ∧ ∀ k ∈ GinfC c.T, ∀ z z', IsTr (inB c.θ c.T ρ.BT k) z z' → ρ.J v k z' = ρ.J v 1 z
  low : ∀ n (h : n = D.R.m), ∃ hN : (c.X n).rank = c.T.rank + 1,
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (ρ.lam n τ) (ρ.sg τ)) ∧ BrEqv hN _ _ (ρ.lam n) ρ.sg (ρ.low n h) ∧
    (∃ Φ ∈ ValC _ (ρ.lam n), ρ.low n h Φ ≠ 0) ∧
    ∀ k ∈ GinfC c.T, ∀ τ, GlobalTheory.BranchFormula.IsBlock hN (c.r n ((c.oT n h).emb (k, 1)) τ) (inB c.θ c.T ρ.BT k τ) 1

structure ClsDat {c : Comm D} (t : Tup c) where
  cl : ∀ j, t.Ch j → Type
  [fin : ∀ j β, Fintype (cl j β)]
  U : ∀ j, t.Ch j → Subgroup (GA D (c.X j))
  chi : ∀ j β, U j β →* ℂˣ
  h : ∀ j β, cl j β → GA D (c.X j)

  val : ∀ j β, t.Col j → cl j β → FrN D (c.X j).rank → ℂ

  abelian₂ : ∀ j α γ, cl j α → cl (j + 1) γ → (FP D.what₂.Tau (c.X j).rank (c.X (j + 1)).rank →ₗ[ℂ] ℂ)
  clT : Type
  [finT : Fintype clT]
  UT : Subgroup (GA D c.T)
  hT : clT → GA D c.T

  ell : ∀ n, n = D.R.m → t.Ch n → clT → t.CT → ((FrN D c.T.rank → ℂ) →ₗ[ℂ] ℂ)

attribute [instance] ClsDat.fin ClsDat.finT

structure ClsDat.Is {c : Comm D} (ρ : RealC c) {t : Tup c} (A : ClsDat t) : Prop where
  reps : ∀ j, j ≤ D.R.m → ∀ β, IsReps (c.X j) (A.U j β) (A.h j β)
  chi : ∀ j, j ≤ D.R.m → ∀ β, Continuous fun κ => ((A.chi j β κ : ℂˣ) : ℂ)
  valC : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram j, ∀ β a, A.val j β ψ a ∈ ValC _ (ρ.lam j)

  rd : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram j, ∀ β y, ∀ γ ∈ GQ (c.X j), ∀ a, ∀ k ∈ GinfC (c.X j), ∀ (κ : A.U j β) y',
    IsTr (c.r j k) (ρ.fr j y) y' → t.rd j β ψ y (γ * (A.h j β a * k) * κ.1) = (A.chi j β κ : ℂ) * A.val j β ψ a y'

  real : ∀ j, j < D.R.m → ∀ α γ, ∀ k ∈ GinfC (c.X j), ∀ k' ∈ GinfC (c.X (j + 1)), ∀ P,
    t.kom j (k, k') ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) =
      (∏ τ, (c.r j k τ).det ^ ρ.sS j τ * (c.r (j + 1) k' τ).det ^ (-ρ.sD j τ)) •
        (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) (mvZ (fun τ => (c.r j k τ)⁻¹) (c.r (j + 1) k') P)

  lev : ∀ j, j < D.R.m → ∀ α γ (κ : A.U j α) (κ' : A.U (j + 1) γ),
    t.kom j (κ.1, κ'.1) (comb c.ψ _ _ (t.dd j α γ) (c.vac j)) =
      (((A.chi j α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) γ κ' : ℂˣ) : ℂ)) • comb c.ψ _ _ (t.dd j α γ) (c.vac j)

  core : ∀ j, j < D.R.m → ∀ α γ a a' P,
    (volLev (c.x j).vol (A.U j α) : ℂ) *
        thetaKO (t.kom j) (A.h j α a) (A.h (j + 1) γ a') ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) =
      t.cK j * A.abelian₂ j α γ a a' (mvZ (fun _ => 1) (fun τ => ρ.sc j τ • 1) P)

  kval : ∀ j, j < D.R.m → ∀ (hab : (c.X j).rank ≤ (c.X (j + 1)).rank), ∀ ψ ∈ t.Ram j,
    ∀ F : ∀ α, A.cl j α → PY D.what₂.Tau (c.X j).rank, (∀ α a, F α a ∈ Vn (ρ.lam j) (ρ.n j)) →
      (∀ α a y, A.val j α ψ a y = evalAt y.1 (F α a) * ∏ τ, (y.1 τ).det ^ (-ρ.sS j τ)) →
      ∀ γ a' y', A.val (j + 1) γ (t.K j ψ) a' y' =
        ∑ α, ∑ a, ((stabOrd (A.U j α) (A.h j α a) : ℕ) : ℂ)⁻¹ * A.abelian₂ j α γ a a' (subY hab y'.1 (F α a)) *
          ∏ τ, (y'.1 τ).det ^ (-ρ.sD j τ)
  repsT : IsReps c.T A.UT A.hT

  invT : ∀ n (h : n = D.R.m), ∀ ψ ∈ t.Ram n, ∀ (G : t.CT) v y β g, ∀ κ ∈ A.UT,
    trc (t.eT n h β) (G.1 v) (g * κ) * t.rd n β ψ y ((c.oT n h).emb (g * κ, 1)) =
      trc (t.eT n h β) (G.1 v) g * t.rd n β ψ y ((c.oT n h).emb (g, 1))

  top : ∀ n (h : n = D.R.m) (G : t.CT) v β a, ∀ k ∈ GinfC c.T,
    trc (t.eT n h β) (G.1 v) (A.hT a * k) = A.ell n h β a G (ρ.J v k)

  tail : ∀ n (h : n = D.R.m), ∀ ψ ∈ t.Ram n, ∀ G : t.CT,
    (volLev c.volT A.UT : ℂ) * ∑ β, ∑ a, ((stabOrd A.UT (A.hT a) : ℕ) : ℂ)⁻¹ *
        A.ell n h β a G (ρ.low n h fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.hT a, 1))) =
      t.cP * t.tail n h ψ G

def ClsPin {c : Comm D} {𝒯 : Type} (t : 𝒯 → Tup c) : Prop := ∃ ρ : RealC c, ρ.Is ∧ ∀ s, ∃ A : ClsDat (t s), A.Is ρ

end GlobalTheory.SeeSaw

end
