import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure IsPair (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) : Prop where
  weil : IsWeilDatumO ψ V W χV χW om
  inf : IsInfFam θ
  std : V.gram = 1
  even : Even V.rank
  sigV : V.SigOK
  sigW : W.SigOK
  expV : ∀ τ, ∃ a : ℤ, HasInfExp D χV τ a
  expW : ∀ τ, ∃ b : ℤ, HasInfExp D χW τ ((b : ℚ) + (W.rank : ℚ) / 2)
  unr : ∀ v ε, NonSplitAt D v ε → UnramAt ε χV ∧ UnramAt ε χW
  eta : ∃ η, IsEtaTilde D η

def MarkAd {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (W : HSp D) {r : ℕ} (hr : W.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (h : GA D W) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat W h,
    finVec W (mk a ∘ Fin.cast hr) - (finHom W h).1.mulVec (finVec W (ι a)) = (l.M : ℕ) • w

def hatC {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (l : Level H)
    {n : ℕ} (φ : (Fin n → LevQc Dw l) → ℂ) (q : Fin n → LevQ Dw l) : ℂ :=
  ∑ᶠ x : Fin n → LevQc Dw l, φ x * Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) ^
    pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b))

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def SerOf (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 ∧
    ∀ (t : Tp) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))),
      RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t) →
      ∀ (y : (R.HV i (tup t)).H) (x : O.Cl' t → VsV D i O.c'.F), Place R i (tup t) h O.c0' y x →
      ∀ f ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank,
        IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f →
        ∀ g : GA D (Wc D i), ph * R.thF i (tup t) y v₀ g =
          cc (O.dict g).1 * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.mu g *
            rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2

theorem SerOf.norm {O : OMDat C R i Tp tup} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
    {cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ} {ph : ℂ} (h : SerOf O κ v₀ cc ph) : ‖ph‖ = 1 := h.2.1

end

end GlobalTheory.AdTh
