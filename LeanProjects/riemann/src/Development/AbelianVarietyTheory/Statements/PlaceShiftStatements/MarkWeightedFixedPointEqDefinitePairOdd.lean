import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.LKDef
open scoped TensorProduct Classical

namespace GlobalTheory.RootSumWeights

variable {p : ℕ} [Fact p.Prime]

def eigL (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : Fin G.n → ℂ) : ℂ :=
  if h : FixL G v β y z then h.choose else 0

def cxSumAtM (G : HTGroup p) (v : InfinitePlace G.F) (c : Polynomial G.F → ℂ → ℂ) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : Pts G v β x t hx Kf K',
    ((Nat.card (Stab G v β x t hx Kf K' (Quot.out q)) : ℕ) : ℂ)⁻¹ *
      ∑ᶠ y : grp G β, if FixL G v β y (Quot.out q).2.1 then
        f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) *
          f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) *
          c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (eigL G v β y (Quot.out q).2.1) else 0

def cxSumM (G : HTGroup p) (v : InfinitePlace G.F) (c : Polynomial G.F → ℂ → ℂ) (P : Form G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  cxSumAtM G v c P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec Kf f K' f'

def cxTotalM (G : HTGroup p) (v : InfinitePlace G.F) (c : Polynomial G.F → ℂ → ℂ) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : FCls G, cxSumM G v c (Quot.out q) Kf f K' f'

def markSumC (G : HTGroup p) (c : Polynomial G.F → ℂ → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : Cls G, if h : ∃ μ, (Quot.out q).Mark μ then
    c (Quot.out q).pol h.choose * (Quot.out q).term Kf f 1 K' f' else 0

def rootSum (G : HTGroup p) (v : InfinitePlace G.F) (c : Polynomial G.F → ℂ → ℂ) (P : Polynomial G.F) : ℂ :=
  (((P.map v.embedding).roots).map (c P)).sum

def CxCountRegMark : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 →
    ∀ (c : Polynomial G.F → ℂ → ℂ) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    (∀ g, f g ≠ 0 → RegAf G g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      cxTotalM G v c L.K.toSubgroup f K' f' = markSumC G c L.K.toSubgroup f K' f'

def MarkWeightedFixedPointEqDefinitePairOdd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 →
    ∀ (c : Polynomial G.F → ℂ → ℂ) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    (∀ g, f g ≠ 0 → RegAf G g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
    (∀ P : Pair G, (∃ μ, P.Mark μ) → ¬ Irreducible P.pol → P.term L.K.toSubgroup f 1 K' f' = 0) →
      cxTotalM G v c L.K.toSubgroup f K' f' = dSumIrr G (rootSum G v c) L.K.toSubgroup f 1 K' f'

end GlobalTheory.RootSumWeights
