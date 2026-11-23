import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Formalism.LocalToGlobal.Divisibility.CoefMod

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.DIV

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

abbrev Psi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : Type := {τ : E →+* ℂ // InPsi H τ}

instance instFintypePsi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : Fintype (Psi H) := Fintype.ofFinite _

def IsPartFam (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ (σ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult σ → a (σ, j) ≤ a (σ, i)

def part (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (σ : E →+* ℂ) (i : ℕ) : ℕ :=
  if i < Dw.mult σ then a (σ, i) else 0

theorem part_anti {Dw : Datum H} {a : (E →+* ℂ) × ℕ → ℕ} (ha : IsPartFam Dw a) (σ : E →+* ℂ) :
    Antitone (part Dw a σ) := by
  intro i j hij
  unfold part
  by_cases hj : j < Dw.mult σ
  · rw [if_pos hj, if_pos (lt_of_le_of_lt hij hj)]
    exact ha σ i j hij hj
  · rw [if_neg hj]
    exact Nat.zero_le _

def lamP (Dw : Datum H) (n : ℕ) {a : (E →+* ℂ) × ℕ → ℕ} (ha : IsPartFam Dw a) (d : Psi H → ℤ) (τ : Psi H) :
    DomWeight n where
  w i := (part Dw a τ.1 i.val : ℤ) - (part Dw a (ComplexEmbedding.conjugate τ.1) (Fin.rev i).val : ℤ) + d τ
  anti := by
    intro i j hij
    have h1 := part_anti ha τ.1 (show i.val ≤ j.val from hij)
    have h2 := part_anti ha (ComplexEmbedding.conjugate τ.1)
      (show (Fin.rev j).val ≤ (Fin.rev i).val from Fin.rev_le_rev.mpr hij)
    simp only
    omega

def dTw (Dw : Datum H) (e : Psi H → ℤ) (τ : Psi H) : ℤ := ((Dw.p : ℤ) - Dw.q - 1) / 2 - e τ

variable {l : Level H} (Dw : Datum H) (c : Coeff l) (n : ℕ)

def embPsi : Psi H → E →+* c.F := fun τ => embF c τ.1

variable {a : (E →+* ℂ) × ℕ → ℕ} (ha : IsPartFam Dw a) (d : Psi H → ℤ)

abbrev CoefSp : Type := VV c.F (lamP Dw n ha d)

def coefRep : GL (Fin n) E →* Module.End c.F (CoefSp Dw c n ha d) :=
  rhoVr (embPsi c) (lamP Dw n ha d)

open Classical in

def coefAct (γ : Matrix (Fin n) (Fin n) E) : CoefSp Dw c n ha d →ₗ[c.F] CoefSp Dw c n ha d :=
  if h : IsUnit γ then coefRep Dw c n ha d h.unit else 0

theorem coefAct_coe (g : GL (Fin n) E) :
    coefAct Dw c n ha d (g : Matrix (Fin n) (Fin n) E) = coefRep Dw c n ha d g := by
  unfold coefAct
  rw [dif_pos g.isUnit, IsUnit.unit_of_val_units]

def vacChar (γ : Matrix (Fin n) (Fin n) E) : c.F := ∏ τ : Psi H, embPsi c τ γ.det ^ (-(d τ))

def coefLat : Submodule (𝓞 c.F) (CoefSp Dw c n ha d) :=
  nabAtr (embPsi c) (lamP Dw n ha d) (Formalism.L2.Pj.stdLat E n)

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by omega)

theorem ten_extremal_mem {K ι : Type} [Field K] [Fintype ι] {N : ℕ} (lam : ι → DomWeight N) :
    ten (fun τ => extremal K N (lam τ)) ∈ VV K lam :=
  Submodule.subset_span
    ⟨fun τ => extremal K N (lam τ), fun τ => Formalism.GradedWeylDivisibility.hwMem K N N le_rfl _ (natW_anti (lam τ)), rfl⟩

def extTen : CoefSp Dw c n ha d :=
  ⟨ten fun τ => extremal c.F n (lamP Dw n ha d τ), ten_extremal_mem _⟩

def TieAt (io : CoefSp Dw c n ha d →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) : Prop :=
  IoLF (Dw := Dw) c a io (coefAct Dw c n ha d) (vacChar c n d) (coefLat Dw c n ha d) (extTen Dw c n ha d)
    (pG (Dw := Dw) c a n)

open Classical in

def ioMap : CoefSp Dw c n ha d →ₗ[c.F] MvPolynomial (LtN Dw n) c.F :=
  if h : ∃ io, TieAt Dw c n ha d io then h.choose else 0

def LFTieAt : Prop := Dw.p + Dw.q ≤ n → ∃ io, TieAt Dw c n ha d io

def LFTieUniqueAt : Prop := ∀ io io', TieAt Dw c n ha d io → TieAt Dw c n ha d io' → io = io'

end GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights

namespace GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

def LFTie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw : Datum H)
    (c : Coeff l) (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (ha : IsPartFam Dw a) (d : Psi H → ℤ), LFTieAt Dw c n ha d

def LFTieUnique : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw : Datum H)
    (c : Coeff l) (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (ha : IsPartFam Dw a) (d : Psi H → ℤ), LFTieUniqueAt Dw c n ha d

def LFTieWeil : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw : Datum H)
    (c : Coeff l) (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (ha : IsPartFam Dw a) (e : Psi H → ℤ),
    Odd (Dw.p + Dw.q) → LFTieAt Dw c n ha (dTw Dw e)

theorem LFTie.weil (h : LFTie) : LFTieWeil :=
  fun E _ _ _ H l Dw c n a ha e _ => h E H l Dw c n a ha (dTw Dw e)

example {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
    (Dw : Datum H) (c : Coeff l) (n : ℕ) {a : (E →+* ℂ) × ℕ → ℕ} (ha : IsPartFam Dw a) (d : Psi H → ℤ) :
    coefAct Dw c n ha d 1 = 1 ∧ vacChar c n d 1 = 1 := by
  refine ⟨?_, by simp [vacChar]⟩
  have := coefAct_coe Dw c n ha d 1
  rw [map_one] at this
  simpa using this

end GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights
