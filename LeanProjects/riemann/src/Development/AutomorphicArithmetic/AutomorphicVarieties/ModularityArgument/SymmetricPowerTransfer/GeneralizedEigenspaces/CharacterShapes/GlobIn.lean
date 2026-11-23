import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.QuaternionDoubleCosetIndicator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Grp

variable {G : Type} [Group G]

def DC (U : Subgroup G) (a : G) : Set G := {g | ∃ u ∈ U, ∃ u' ∈ U, g = u * a * u'}

def UF (U : Subgroup G) (a b : G) : Prop :=
  ∀ g : G, (g ∈ DC U (a * b) → ∃! y : G ⧸ U, y.out ∈ DC U a ∧ y.out⁻¹ * g ∈ DC U b) ∧
    ∀ y ∈ DC U a, y⁻¹ * g ∈ DC U b → g ∈ DC U (a * b)

abbrev dcF {V : Type} [AddCommGroup V] [Module ℂ V] (U : Subgroup G) (a : G) (φ : G → V) : G → V :=
  dc (rightReg ℂ G V) U U a φ

end Grp

variable {F : Type} [Field F] [NumberField F]

structure SD (Δ : F) where
  Sg : Finset (Pl F)
  s : ∀ v : Pl F, Kv v
  hs : ∀ v ∈ Sg, s v * s v = cv v Δ
  V : ∀ v : Pl F, Lev (Kv v)
  Ry : ∀ v : Pl F, Finset (Kv v)ˣ
  χ : ∀ v : Pl F, (Kv v)ˣ →* ℂˣ

abbrev ParN (F : Type) [Field F] [NumberField F] (n : ℕ) : Type := ∀ v : Pl F, Fin n → (Kv v)ˣ

abbrev Chs (F : Type) [Field F] [NumberField F] : Type := ∀ v : Pl F, (Kv v)ˣ →* ℂˣ

namespace SD

variable {Δ : F} (A : SD Δ)

open Classical in

def dat : Dat Δ where
  Sg := A.Sg
  S v := if h : v ∈ A.Sg then (A.V v).data (A.hs v h) (A.Ry v) (A.χ v) else ⟨∅, ⊤, ⊤, ⊤, 0, 0, 0, 1, 1, 1⟩
  χ := A.χ

structure Ok : Prop where
  real : IsTotallyReal F
  neg : ∀ σ : F →+* ℝ, σ Δ < 0
  ne : A.Sg.Nonempty
  off : ∀ v ∉ A.Sg, IsLoc (Ov v) (cv v Δ)
  chi : ∀ v, IsChi (Ov v) (cv v Δ) (A.χ v)
  ry : ∀ v ∈ A.Sg, (A.V v).IsSqReps (A.Ry v)

def DomS {n : ℕ} (d : ParN F n) : Prop := ∀ v ∈ A.Sg, Dom (d v)

def Cone (t : Dat.Par F) : Prop := ∀ v ∈ A.Sg, valuation (Kv v) (t v : Kv v) < valuation (Kv v) (unif (Kv v) : Kv v) ^ 2

def IsElG (g : GA Δ) (d : ParN F 3) : Prop := (∀ v (h : v ∈ A.Sg), eU (A.hs v h) (g.1 v) = dg (d v)) ∧ ∀ v ∉ A.Sg, g.1 v = 1

def IsElD (g : DA Δ) (d : ParN F 2) : Prop := (∀ v (h : v ∈ A.Sg), eD (A.hs v h) (g.1 v) = dg (d v)) ∧ ∀ v ∉ A.Sg, g.1 v = 1

def dS (t : Dat.Par F) : ParN F 2 := fun v => ![t v, (t v)⁻¹]

def sg (d : ParN F 3) : ParN F 3 := fun v => ![(d v 2)⁻¹, (d v 1)⁻¹, (d v 0)⁻¹]

open Classical in

def dG (t : Dat.Par F) (y : ∀ v : A.Sg, (Kv v.1)ˣ) : ParN F 3 :=
  fun v => ![t v * (unif (Kv v))⁻¹, if h : v ∈ A.Sg then y ⟨v, h⟩ else 1, (unif (Kv v))⁻¹]

open Classical in

def Ys : Finset (∀ v : A.Sg, (Kv v.1)ˣ) := Fintype.piFinset fun v => A.Ry v.1

open Classical in

def F0 (d : ParN F 3) (g : GA Δ) : ℂ :=
  ∏ᶠ v, if h : v ∈ A.Sg then (A.V v).unitaryDoubleCosetIndicator (d v) (eU (A.hs v h) (g.1 v)) else one (g.1 v ∈ KU (Ov v) _)

def exG (a : Chs F) (d : ParN F 3) : ℂ := ∏ v ∈ A.Sg, Dict.expo ![a v, 1, (a v)⁻¹] (d v)

def exS (a : Chs F) (t : Dat.Par F) : ℂ := ∏ v ∈ A.Sg, Dict.expo ![a v, 1] (dS t v)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def EigG (φ : GA Δ → V) (a : Chs F) : Prop := ∀ d g, A.DomS d → A.IsElG g d → dcF A.dat.UG g φ = A.exG a d • φ

def EigS (U : Subgroup (SA Δ)) (φ : SA Δ → V) (a : Chs F) : Prop :=
  ∀ t (g : SA Δ), A.Cone t → A.IsElD g (dS t) → dcF U g φ = A.exS a t • φ

def EigK (φ : DA Δ → V) (a : Chs F) : Prop := ∀ t g, A.DomS (dS t) → A.IsElD g (dS t) → dcF A.dat.U2 g φ = A.exS a t • φ

structure GOps (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw) (u : ParN F 3 → Module.End ℂ B.Forms) (Θ : Module.End ℂ B.Forms) : Prop where
  eq : ∀ d g, A.DomS d → A.IsElG g d → ∀ φ : B.Forms, (u d φ).1 = dcF A.dat.UG g φ.1
  mul : ∀ d d', A.DomS d → A.DomS d' → u (d * d') = u d * u d'
  lev : ∀ d, (∀ v ∈ A.Sg, ∀ i, d v i ∈ (A.V v).H) → u d = 1
  th : ∀ d, A.DomS d → Θ * u d = u (sg d) * Θ
  tr : ∀ t, A.Cone t → s.R (A.dat.FG t) = ∑ y ∈ A.Ys, u (A.dG t y) * Θ

end SD

structure GlobIn : Prop where
  tf : TFId0
  bG : BaseG
  bS : BaseS
  bK : BaseK
  fG : FinG
  fS : FinS
  fK : FinK

def SpecF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok →
    ∀ (VG VS VK : Type) [AddCommGroup VG] [Module ℂ VG] [FiniteDimensional ℂ VG] [AddCommGroup VS] [Module ℂ VS]
      [FiniteDimensional ℂ VS] [AddCommGroup VK] [Module ℂ VK] [FiniteDimensional ℂ VK] (ch : F → ℂ)
      (BG : Base (U3 Δ) (GA Δ) VG) (s : BG.Tw) (x : DA Δ) (BS : Base (SU Δ) (SA Δ) VS) (BK : Base (DX Δ) (DA Δ) VK),
    A.dat.IsBG ch BG s → A.dat.Off x → A.dat.IsBS ch x BS → A.dat.IsBK ch BK →
    ∀ (a : Chs F) (φ : SA Δ → VS), φ ∈ BS.Forms → φ ≠ 0 → A.EigS BS.U φ a →
    (∃ φ' ∈ BG.Forms, φ' ≠ 0 ∧ A.EigG φ' a) ∨ ∃ φ' ∈ BK.Forms, φ' ≠ 0 ∧ A.EigK φ' (a ^ 2)

end UpperTheory.V.Z.Sym.So

end
