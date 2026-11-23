import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompatAlt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open PAlg Pb

variable {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

variable (l) in

def CrisSurj : Prop := ∀ n, Function.Surjective ((base l).cris n)

def cb (ht : TFil l) (hs : CrisSurj l) : CB l K where
  Λ := Acris l
  R n := (base l).Acr n
  I n := B.JJ false (base l) n
  γ n := B.DD false (base l) n
  κ n := B.κb (okToOC l K) false n
  c n := (base l).cris n
  c_surj := hs
  t := tA l
  ht := ht (base l)
  θ := θA l
  rd n := (base l).red n.le_succ
  rd_dp n := B.dd_red false _ n.le_succ
  rd_κ n := B.red_κb _ false n.le_succ
  rd_c n := B.red_cris _ n.le_succ

variable {K} (ht : TFil l) (hs : CrisSurj l) {M : Model l K}

def toY {r j : ℕ} (x : Fam M r j) : (cb K ht hs).Fam M r j := x

theorem toY_comp {r j : ℕ} (x : Fam M r j) : CB.Comp (toY ht hs x) ↔ Comp x := Iff.rfl

theorem toY_isFirstChern_iff (D : E.LineData M.X) (x : Fam M 1 2) : CB.IsFirstChernClassInFamily D (toY ht hs x) ↔ IsFirstChernClassInFamily D x := Iff.rfl

variable (l K)

def LvEx : Prop := ∀ (ht : TFil l) (hs : CrisSurj l), Nonempty (LvSys (cb K ht hs) (Γ := K.fixingSubgroup)
  (fun σ => ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ)) (fun σ => galBase (IntermediateField.fixingSubgroupEquiv K σ))
  (fun σ => (period_ring_base.σC σ.1).toRingHom) fun σ => qC l (period_ring_base.χ σ.1))

def Half2Of : Prop := ∀ ht : TFil l, CrisSurj l → LvEx l K → RhoEx l K → CoEx l K → HomRho l K → HomMu l K → MulRho l K →
  FirstChernHodgeTateCompat l K → KForm → KFin → ∃ γ, Half2 (K := K) ht γ

end CrystallineSemistableComparison.HT
