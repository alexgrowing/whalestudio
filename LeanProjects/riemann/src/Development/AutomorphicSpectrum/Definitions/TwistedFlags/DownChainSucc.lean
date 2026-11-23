import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HaarOrderData

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup

namespace GlobalTheory.CompanionTheory.Sep

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Objects

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

def per (φ : Fn G (.core 0)) (u : GA D (Yc D 0) → ℂ) : ℂ :=
  ∫ h in M.fd (.grid 0 0), φ (stabilizerEmbedding G.sp.dec0 h) * u h ∂M.ν (.grid 0 0)

structure IsCoreForm (i : ℕ) (φ : Fn G (.core i)) : Prop where
  cusp : GlobalTheory.Mem.Th.IsCuspForm W.θ (G.V (.core i)) φ
  listed : G.IsListed W.θ (.core i) φ
  level : ∀ k ∈ GfC (G.V (.core i)), Lev.finE (G.V (.core i)) k ∈ G.levCong (.core i) → ∀ g, φ (g * k) = φ g

def IsCoreDatum (i : ℕ) (f : Sch G (.coreDown i)) : Prop :=
  ∃ (v f₀ : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ) (e : AE D) (κ : Cos (G.Λ (.core (i + 1))) (G.Λ (.core i)) G.modul)
    (P : PolF D (G.pT (.core i)).rank (G.pS (.core i)).rank),
    W.IsVac (.core i) v ∧ IsIdemSum e G.pl.W0 ∧
    IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) 1
      v (cosInd e κ) f₀ ∧ f = W.fock (.core i) f₀ P

def downChain (f : ∀ i, Sch G (.coreDown i)) (n : ℕ) : Fn G (.core n) → Fn G (.core 0) :=
  Nat.rec (motive := fun n => Fn G (.core n) → Fn G (.core 0)) (fun F => F)
    (fun n ih F => ih (liftA W M (.coreDown n) (f n) F)) n

def CoreHaar : Prop := ∀ i, i ≤ D.R.m → GlobalTheory.IndefiniteRowSideFullHecke.HaarEquallySpacedConditions.HaarAt M (.core i)

def HasPeriod (u : GA D (Yc D 0) → ℂ) : Prop := ∃ φ, IsCoreForm W 0 φ ∧ per M φ u ≠ 0

def HasColumn (u : GA D (Yc D 0) → ℂ) : Prop :=
  ∃ Ψ ∈ Cols G W.θ, ∃ (ξ : Module.Dual ℂ (coefPlus G W.θ).W) (f : ∀ i, Sch G (.coreDown i)),
    (∀ i, i < D.R.m → IsCoreDatum W i (f i)) ∧ per M (downChain W M f D.R.m (pairVec (coefPlus G W.θ) ξ Ψ)) u ≠ 0

def HasValue (u : GA D (Yc D 0) → ℂ) : Prop :=
  ∃ (ρ : G.RealVec) (ξ : Module.Dual ℂ (coefPlus G W.θ).W), ∃ Ψ ∈ Cols G W.θ, ∃ Φ : G.Datum, fPsiPhi W M ρ ξ Ψ Φ u ≠ 0

end Objects

abbrev PropG := ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {sc : Consts}
  {G : GridData R.toLevCh sc}, G.Weil → Vol G → Prop

def Big (P : PropG) : Prop :=
  ∀ ε CF : ℝ, 6510 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → SizeRows large₂ →
    GlobalTheory.GLq.ESerTie D →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
      R.toLevCh.Is A.μ0 → R.grp_record →
      ∀ (G : GridData R.toLevCh ⟨1, CF, large₂.sc.b⟩) (W : G.Weil), W.Over R → ∀ M : Vol G, M.IsRow → P R W M

def Conv : Prop := Big fun R _ G W M => ∀ t ∈ R.EEat R.triv, ∀ (w : SmT (R.MY 0)) (ρ : G.RealVec)
  (ξ : Module.Dual ℂ (coefPlus G W.θ).W), ∀ Ψ ∈ Cols G W.θ, ∀ Φ : G.Datum, FConv W M ρ ξ Ψ Φ (rowForm R w t)

def RankOne : Prop := Big fun R _ G W M => ∀ (w : SmT (R.MY 0)) (ρ ρ' : G.RealVec)
  (ξ ξ' : Module.Dual ℂ (coefPlus G W.θ).W), ∀ t ∈ R.EEat R.triv, ∀ t' ∈ R.EEat R.triv, ∀ Ψ ∈ Cols G W.θ, ∀ Ψ' ∈ Cols G W.θ,
    ∀ Φ Φ' : G.Datum, fPsiPhi W M ρ ξ Ψ Φ (rowForm R w t) * fPsiPhi W M ρ' ξ' Ψ' Φ' (rowForm R w t') =
      fPsiPhi W M ρ ξ Ψ' Φ' (rowForm R w t') * fPsiPhi W M ρ' ξ' Ψ Φ (rowForm R w t)

def AllVec : Prop := Big fun R _ _ W M => ∀ t ∈ R.EEat R.triv, ∀ w₀ w : SmT (R.MY 0), w ≠ 0 →
  HasValue W M (rowForm R w₀ t) → HasValue W M (rowForm R w t)

def PerEx : Prop := Big fun R _ _ W M => ∀ t ∈ R.EEat R.triv, t ≠ 0 → ∃ w : SmT (R.MY 0), HasPeriod W M (rowForm R w t)

def Onto : Prop := Big fun R _ _ W M => CoreHaar M → ∀ t ∈ R.EEat R.triv, ∀ w : SmT (R.MY 0),
  HasPeriod W M (rowForm R w t) → HasColumn W M (rowForm R w t)

def Unfold : Prop := Big fun R _ _ W M => CoreHaar M → ∀ t ∈ R.EEat R.triv, ∀ w : SmT (R.MY 0),
  HasColumn W M (rowForm R w t) → HasValue W M (rowForm R w t)

def Rechoose : Prop := Big fun _ _ G _ M => ∃ M' : Vol G, CoreHaar M' ∧ M'.νN = M.νN ∧ M'.fdN = M.fdN ∧
  ∀ X : Node, (∀ i, X ≠ .core i) → M'.ν X = M.ν X ∧ M'.fd X = M.fd X

end GlobalTheory.CompanionTheory.Sep

end
