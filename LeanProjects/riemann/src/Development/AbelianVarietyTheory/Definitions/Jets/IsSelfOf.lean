import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.RowTieAdm
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace GlobalTheory.RowAt

open NumberField Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV GlobalTheory.RowLaw
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def gap (r : ℕ) (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  if 1 ≤ k ∧ k ≤ r then a (k - 1) - (if k < r then a k else 0) else 0

section Supply

variable {C : Type} [Field C]

def Supply (V : VF C) (d : ℕ) [NeZero d] (Orb : Type) [Fintype Orb] (Z : Finset Orb) (n m : ℕ)
    (big : Orb → Fin 2 → ZMod d → Prop) (rk : Orb → Fin 2 → ZMod d → ℕ) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)
    (nW : ℕ) (ν : ℝ) : Prop :=
  ∃ (I J : Orb → Fin 2 → Type) (_ : ∀ o g, Fintype (I o g)) (_ : ∀ o g, Fintype (J o g))
    (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, RF.Flag (X o)),
    (∀ o, (X o).n = n ∧ (X o).m = m) ∧ (∀ o ∈ Z, ∀ g s, ((X o).big g s ↔ big o g s) ∧ (X o).rkF g s = rk o g s) ∧
      RF.ValBlocks X F Z nW ga ν

def SupplyC (V : VF C) (Orb : Type) [Fintype Orb] (n m : ℕ) (rk : Orb → ZMod 2 → ℕ) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (nW : ℕ) (ν : ℝ) : Prop :=
  ∃ (I J : Orb → Fin 2 → Type) (_ : ∀ o g, Fintype (I o g)) (_ : ∀ o g, Fintype (J o g))
    (X : ∀ o, RowData C V 2 (I o) (J o)) (F : ∀ o, RF.Flag (X o)),
    (∀ o, (X o).n = n ∧ (X o).m = m ∧ (X o).Alt ∧ ∀ s, (X o).rkF 0 s = rk o s) ∧ RF.ValBlocksC X F nW gaC ν

end Supply

section ND

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def c2 (X : RawChart C d I κ) (u : κ → C) : MvPowerSeries (Fin 2 × κ) C :=
  fun μ => ∑ i, u i * MvPowerSeries.coeff
    (μ.mapDomain (fun p : Fin 2 × κ => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1)
    (hAt X (gp C κ (0 : Fin 3)) (gp C κ 1) + hAt X (gp C κ 0) (gp C κ 2) -
      hAt X (gp C κ 0) (addP X (gp C κ 1) (gp C κ 2)))

def cob (X : RawChart C d I κ) (b : MvPowerSeries κ C) : MvPowerSeries (Fin 2 × κ) C :=
  MvPowerSeries.subst (addP X (gp C κ (0 : Fin 2)) (gp C κ 1)) b - MvPowerSeries.subst (gp C κ (0 : Fin 2)) b -
    MvPowerSeries.subst (gp C κ (1 : Fin 2)) b

def NonDeg (X : RawChart C d I κ) (V : VF C) : Prop :=
  ∀ γ : κ → PowerSeries C, IsCv V γ → (∃ i, ¬ V.MM (PowerSeries.coeff 1 (γ i))) →
    (∀ i (μ : Fin 2 →₀ ℕ), μ 0 < V.l → μ 1 < V.l → V.MM (MvPowerSeries.coeff μ
      (addP X (fun j => cvAt (MvPowerSeries.X 0) (γ j)) (fun j => cvAt (MvPowerSeries.X 1) (γ j)) i -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i)))) →
    ¬ ∃ b : MvPowerSeries κ C, IntS V b ∧
      ∀ μ, V.MM (MvPowerSeries.coeff μ (c2 X (fun i => PowerSeries.coeff 1 (γ i)) - cob X b))

def hCoef (X : RawChart C d I κ) (γ : κ → PowerSeries C) (n : ℕ) : MvPowerSeries κ C :=
  fun μ => PowerSeries.coeff n (alongCv γ (fun ν : κ →₀ ℕ => MvPowerSeries.coeff
    (ν.mapDomain (fun x : κ => ((0 : Fin 2), x)) + μ.mapDomain (fun x : κ => ((1 : Fin 2), x))) X.h))

end ND

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure LabS (E : Type) [Field E] (Orb : Type) where
  tau : Orb → ZMod 2 → (E →+* ℂ)
  n : ℕ
  j : ℕ
  j' : ℕ

abbrev LabS.II {Orb : Type} (lab : LabS E Orb) (Dw : Datum H) (o : Orb) : Type :=
  Σ s : ZMod 2, Fin (Dw.mult (lab.tau o s))

def LabS.RankOK {Orb : Type} (lab : LabS E Orb) (Dw : Datum H) : Prop :=
  ∀ o, Dw.mult (lab.tau o 0) = lab.n + lab.j ∧ Dw.mult (lab.tau o 1) = lab.j'

variable {Dw : Datum H} {lv : Level H} {Xo : Moduli Dw lv} {c : Coeff lv}
variable {C : Type} [Field C] [CharZero C]

def FrobOrd (V : VF C) {T : CDVR} (io : c.F →+* T.Fr) (ι : T.Fr →+* C) {d : ℕ} (tau : ZMod d → (E →+* ℂ)) : Prop :=
  ∀ s x, V.MM (emA3 io ι (tau (s + 1)) x - emA3 io ι (tau s) x ^ V.l)

structure ArithS (V : VF C) {T : CDVR} (io : c.F →+* T.Fr) (ι : T.Fr →+* C) {Orb : Type} (lab : LabS E Orb) : Prop where
  inj : Function.Injective fun x : Orb × ZMod 2 => lab.tau x.1 x.2
  conj : ∀ o s, lab.tau o (s + 1) = ComplexEmbedding.conjugate (lab.tau o s)
  frob : ∀ o, FrobOrd V io ι (lab.tau o)
  unr : ¬ (V.l : ℤ) ∣ NumberField.discr E

variable [StarRing (𝓞 E)] {V : VF C} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

structure IsSelfOf (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch)) {Orb : Type}
    (lab : LabS E Orb) (p : ∀ o, SelfData Y 2 (lab.II Dw o)) : Prop where
  em : ∀ o s, (p o).em s = emA3 io ι (lab.tau o s)
  hd : ∀ o, (p o).hd = 1
  e : ∀ o x i, (p o).e x i = ι (chartUnitVectors C3 ⟨lab.tau o x.1, x.2⟩ i)
  ty0 : ∀ o x, (p o).ty0 x = x.1
  n : ∀ o, (p o).n = lab.n
  j : ∀ o, (p o).j = lab.j
  j' : ∀ o, (p o).j' = lab.j'
  big : ∀ o g s, (p o).big g s ↔ s = ((g.val : ℕ) : ZMod 2)

section Img

variable {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb] {I0 : Orb → Type}
  [∀ o, Fintype (I0 o)]

def imgFamS (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (Ls : LetSys C dd) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) :
    Set (∀ o, MvPolynomial (Fin N × WV fun _ => I0 o) C) :=
  {Po | ∃ P ∈ Ls.FF n, IsImgS (fun o => Y.rawSelf (p o)) pl (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o))}

end Img

def tauIn (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)) (l : ℕ) (z : RPl N.R) (g : Fin 2) (s : ZMod (N.ordP l)) : E →+* ℂ :=
  if g = RF.bg s then pl (N.pos l z s.val) else ComplexEmbedding.conjugate (pl (N.pos l z s.val))

def tauSp (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)) {d : ℕ} (pos : RPl N.R → ℕ → RPl N.R) (z : RPl N.R) (g : Fin 2)
    (s : ZMod d) : E →+* ℂ :=
  if g = 0 then pl (pos z s.val) else ComplexEmbedding.conjugate (pl (pos z s.val))

def tauC (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)) (z : RPl N.R) (s : ZMod 2) : E →+* ℂ :=
  if s = 0 then pl z else ComplexEmbedding.conjugate (pl z)

end GlobalTheory.RowAt
