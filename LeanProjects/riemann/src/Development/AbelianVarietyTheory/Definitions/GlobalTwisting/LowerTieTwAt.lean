import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll

noncomputable section

namespace GlobalTheory.PerQ

section Coord

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Ker NumberField

def PtT (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) :
    ((D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ) →ₗ[ℂ] (D.PTw u μ).Wrow :=
  (D.PTw u μ).lowerMap ∘ₗ (D.PTw u μ).evz

structure PendTw (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) where
  br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ)
  coM : D.what₂.places.Pl → (T.fm u μ).clsP → (((D.chTw u μ).Y D.R.m → ℂ) →ₗ[ℂ]
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)
  coP : D.what₂.places.Pl → ((D.PTw u μ).Wrow →ₗ[ℂ] ((T.fm u μ).clsP →
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))
  Pt_eq : ∀ w, ∀ φ ∈ (T.fm u μ).Fi D.R.m, ∀ c,
    coP w (PtT D u μ φ) c = blk (fun τ => br τ) (coM w c (φ ((T.fm u μ).til c)))
  lat_co : ∀ w, ∀ x ∈ (T.fm u μ).S D.R.m w, ∀ c,
    coM w c ((T.fm u μ).emb D.R.m x ((T.fm u μ).til c)) ∈ IntSpan D w ((D.fm u).lam D.R.m)
  pt_co : ∀ w, ∀ z ∈ (T.fm u μ).ptC,
    (∃ y ∈ (T.fm u μ).SP w, (T.fm u μ).ptEmb y = z) ↔ ∀ c, coP w z c ∈ IntSpan D w (D.fm u).sg

def LowerTieTwAt (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  (∀ φ ∈ (T.fm u μ).Fi D.R.m, PtT D u μ φ ∈ (T.fm u μ).ptC) ∧ (D.fm u).SgInterlace ∧
    ∃ P : PendTw D T u μ, ∀ τ, P.br τ = brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)

end Coord

section Tw

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

attribute [local instance] MemberForms.clsPFin

variable {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} {C : ColsTiedSym D}
  {Tw : TwForms D}

def resCTw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (c : (Tw.fm u μ).clsP) (z : (D.PTw u μ).Wrow) : (D.PTw u μ).Wrow :=
  open Classical in
  (t.pt.val u μ hμ).eW.symm (fun c' => if c' = c then (t.pt.val u μ hμ).eW z c' else 0)

def pcLTw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (c : (Tw.fm u μ).clsP) (z : (D.PTw u μ).Wrow) (G : (D.PTw u μ).Mt) : ℂ :=
  ((Nat.card ((Tw.fm u μ).stabilizer₂ c) : ℕ) : ℂ) *
    (Tw.fm u μ).ipP (resCTw t u μ hμ c (t.ptE.jM u μ G)) (resCTw t u μ hμ c z)

def PerDecTwT (Y : DivX D) (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) : Prop :=
  ∀ x ∈ (Tw.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier, ∀ c,
    ∃ y : D.what₂.LL, D.what₂.embLL y = pcLTw t u μ hμ c ((Tw.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) ∧
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ∉ Y.Qp μ → y = 0 ∨ 0 ≤ vAdd (D.plEq w) y

end Tw

section Rows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws)

def RowVal (u : B.Word) (a : I.ι) (G : (I.per l u a).Mt) : Prop :=
  ∀ c : (I.stX a).Cl, ∃ y ∈ nabAt B.fields.emb B.wts.sgTrue ((I.stX a).rep c).1.1.deco.1.N,
    (I.perIn u a).rd B.fields.emb B.embLL G c = MvPolynomial.map B.embLL y.1

theorem rowVal_zero (u : B.Word) (a : I.ι) : RowVal I l u a 0 := fun c => ⟨0, Submodule.zero_mem _, by
  rw [map_zero]; exact (map_zero _).symm⟩

structure RowInt (Z : TC.Later B (I.cols l)) : Prop where
  ref : ∀ u, ∀ F ∈ ((I.rec7 l Z).what₂.Mtilde (I.rec7 l Z).what₂.mu0).carrier, RowVal I l u I.mu0 (((I.rec7 l Z).eMt u).symm F)
  tw : ∀ u (a : (I.rec7 l Z).what₂.Tup), ∀ F ∈ ((I.rec7 l Z).what₂.Mtilde a).carrier, RowVal I l u a (((I.rec7 l Z).eMtTw u a).symm F)

end Rows

end GlobalTheory.PerQ

end
