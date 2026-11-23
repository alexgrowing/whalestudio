import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HeightF1OfData
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AgreementOfOrders
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FnFGFnTrdeg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteSupportAdmissible
import ReciprocityTheory.SemistableReduction.AlgAll

noncomputable section

namespace GlobalTheory.TrivOrderTieCompare

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AgreementOfOrders

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem isClopen_comp (Z : Comp Xo c) : IsClopen (Z : Set (Xo.XF c)) := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have hZ : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
  obtain ⟨z, hz⟩ := hZ.nonempty
  have h1 : (Z : Set (Xo.XF c)) ⊆ connectedComponent z :=
    hZ.isConnected.isPreconnected.subset_connectedComponent hz
  have h2 : IsIrreducible (connectedComponent z) :=
    ⟨⟨z, mem_connectedComponent⟩, GlobalTheory.KeyFam.isPreirreducible_connectedComponent_of_smooth (strK (Xo := Xo) (c := c)) z⟩
  rw [Set.Subset.antisymm h1 (Z.2.2 h2 h1)]
  exact ⟨isClosed_connectedComponent, isOpen_connectedComponent_of_noetherianSpace z⟩

def ReadsOrders (h : GenFrEx Xo c) (Z : Comp Xo c) (ord : WTZ E → AC Z → ℤ) (q : QPt Xo c) : Prop :=
  (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
    (((ord (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q f) ∧
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f = 0 → ordQ Xo c q f = ⊤

def TieOver (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (P : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Prop) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), P Z v → IsTrivOn c.F v →
    ∃ q : QPt Xo c, ReadsOrders h Z (ordC (δ Z v) v) q

variable [Fintype (Comp Xo c)]

abbrev CompData (Xo : Moduli Dw l) (c : Coeff l) [Fintype (Comp Xo c)] : Type :=
  Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)

def HasOrders (d : CompData Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ Z v, d.ord Z v = ordC (δ Z v) v

def dataWith (ord : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → WTZ E → AC Z → ℤ) (D N : ℕ)
    (w : Fin (N + 1) → ∀ Z : Comp Xo c, AC Z) : CompData Xo c where
  D := D
  N := N
  T := 0
  i := 0
  g0 := 0
  cc := 0
  wL := 0
  wF := 0
  wde := 0
  ord := ord
  nrm _ _ _ _ := 0
  M := ⊥
  WW := ⊥
  Thp := ⊥
  Th0 := ⊥
  Thk := ⊥
  w := w
  jc _ := 0
  np := 0
  thp := Fin.elim0
  n0 := 0
  th0 := Fin.elim0
  nk := 0
  thk := Fin.elim0
  et := 0
  ta1 := 0
  ta2 := 0
  nu _ := 0
  ip _ _ _ := 0
  wsize _ := 0
  DF := 0
  PN := 0
  PQ := 0
  tableDegreeThreeBase := 0
  PP0' := 0
  Pd := 0
  Gc := 0
  PI4 := 0
  Pet := 0
  tableLineDegreeFive := 0
  tableLineDegreeTwo := 0
  Prw := 0
  PO := 0
  f := 0
  r := 0

section Concrete

variable (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

end Concrete

end GlobalTheory.TrivOrderTieCompare
