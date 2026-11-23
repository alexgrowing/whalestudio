import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.StmtPhi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.FirstChernClassUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DIsoDR0
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsEtaleFirstChernUntwisted

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def Model.Ln (M : Model l K) : Type 1 := {D : E.LineData M.X // Etale D.f ∧ sSup (Pb.𝒱D D) = ⊤}

def Res.IsCrystallineChernClassLimit (r : Res l K) {M : Model l K} (D : E.LineData M.X) (y : Pb.Lim r M 2) : Prop :=
  ∀ m, B.IsFirstChernClassOfLineBundle (q := M.p) (b := Wc.bs l r.k m) (ht := rfl) (κ := (Wc.res l r.k m).comp r.ρ) D (Ideal.Quotient.mk _) (l * m) (y.1 m)

abbrev Res.Cup (r : Res l K) : Type 1 :=
  ∀ (M : Model l K) (i j : ℕ), r.iso.D M i →ₗ[Wc.K₀ l r.k] r.iso.D M j →ₗ[Wc.K₀ l r.k] r.iso.D M (i + j)

def Res.IsCup (r : Res l K) (μ : r.Cup) : Prop := ∀ (M : Model l K) (i j : ℕ) (x : Pb.Lim r M i) (y : Pb.Lim r M j),
  ∃ z, Pb.LimCup r M rfl x y z ∧ μ M i j (Pb.toD r M i x) (Pb.toD r M j y) = Pb.toD r M (i + j) z

def Res.xend (r : Res l K) (ζ : E.Roots l) (μ : r.Cup) : XEnd (C := r.perC) r.iso where
  Ln M := M.Ln
  oneT M v := ∀ k, v.lev k = GlobalTheory.EtC.one (l ^ k) M.spc
  c1T L v := HT.IsEtaleFirstChernUntwisted ζ L.1 v
  oneD M y := ∃ x, Pb.LimOne r M x ∧ y = Pb.toD r M 0 x
  c1D {M} L y := ∃ x, r.IsCrystallineChernClassLimit L.1 x ∧ y = Pb.toD r M 2 x
  cupD := μ

def XEnd.Ex {R : Per l K} {C : PerC R} {I : Iso l K C.K₀} (X : XEnd I) (G : Model l K → Prop) : Prop :=
  ∀ M, G M → (∃ v, X.oneT M v) ∧ (∃ y, X.oneD M y) ∧ ∀ L : X.Ln M, (∃ v, X.c1T L v) ∧ ∃ y, X.c1D L y

def CrysPhiP : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (r : Res l K)
  (ζ : E.Roots l), ∃ (μ : r.Cup) (N : ℕ) (c : CrysCmp Model.Sm r.perC r.iso),
    r.IsCup μ ∧ (r.xend ζ μ).Ex Model.Sm ∧ c.Plus (r.xend ζ μ) N

def Res.xmid (r : Res l K) (ζ : E.Roots l) (μ : r.Cup) (Amp : ∀ M : Model l K, E.LineData M.X → Prop) :
    XMid (C := r.perC) (dat Amp) (r.xend ζ μ) where
  one' {M} _ x := (M.HA true).one x
  cup' {M} _ _ _ x y z := (M.HA true).cup x y z
  c1' {M} _ L x := B.IsFirstChernFamily M.p L.1 (okToOC l K) true (show (M.HS true 2).lim from x).1
  c1A {M} _ L y := E.IsFirstChernClassOfLineBundle M.p (okToOC l K) L.1 (show (M.MS 2).lim from y).1

structure FPlus {R : Per l K} {G : Model l K → Prop} {C : PerC R} {I : Iso l K C.K₀} {D : Dat R} {X : XEnd I} (Y : XMid D X)
    {pull : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N}, D.Mo u hu a b →
      ∀ j, (D.H' b).N j →+ (D.H' a).N j} (F : FMap G C I D pull) : Prop where
  first_chern_class_exists : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ L : X.Ln M, (∃ x, Y.c1' a L x) ∧ ∃ y, X.c1D L y
  one : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ x y, Y.one' a x → X.oneD M y → ∀ f, F.ψ a 0 x f = C.k (f y)
  cup : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ {i j : ℕ} (x : (D.H' a).N i) (y : (D.H' a).N j) (z : (D.H' a).N (i + j)),
    Y.cup' a x y z → ∀ {m m' : ℕ} (b : Module.Basis (Fin m) C.K₀ (I.D M i)) (b' : Module.Basis (Fin m') C.K₀ (I.D M j))
      (f : Module.Dual C.K₀ (I.D M (i + j))),
      F.ψ a (i + j) z f = ∑ s, ∑ s', F.ψ a i x (b.coord s) * F.ψ a j y (b'.coord s') * C.k (f (X.cupD M i j (b s) (b' s')))
  c1 : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (L : X.Ln M) x y, Y.c1' a L x → X.c1D L y → ∀ f, F.ψ a 2 x f = C.k (f y)

def FSeamP : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (r : Res l K)
  (ζ : E.Roots l) (μ : r.Cup) (Amp : ∀ M : Model l K, E.LineData M.X → Prop), r.IsCup μ →
    ∃ F : FMap Model.Sm r.perC r.iso (dat Amp) (datPull Amp), FPlus (r.xmid ζ μ Amp) F

def CupEx : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (r : Res l K), ∃ μ, r.IsCup μ

end CrystallineSemistableComparison
