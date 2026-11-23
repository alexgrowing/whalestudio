import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlCTendsto
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ChartSpec
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Rec

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

structure CompLaws (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) : Prop where
  comps : Nat.card (Comp Xo c) = Fintype.card (U c.F.val.toRingHom).Comp
  ne : Nonempty (Comp Xo c)
  genT : GenFromTest Xo c h
  evalWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  unTest : ∀ σ, GoodEmb c σ → ∀ k x,
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x)
  chiTriv : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1
  ptNe : IntFrNe Xo c (algCls Xo c)
  intAll : IntAll Xo c
  e_sec : ∀ Z, e Z ∈ sec Xo c 0 0
  e_val : ∀ Z, evC h Z (e Z) = 1 ∧ ∀ Z', Z' ≠ Z → evC h Z' (e Z) = 0

def Over {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (e₀ : Rul Xo c) (k : U.Comp) : Prop :=
  ∀ x ∈ (U.X k).dom, rdU U e₀ k x = 1

def WEq (Dw : Datum H) (a b : WZ E) : Prop := ∀ τ i, i < Dw.mult τ → a (τ, i) = b (τ, i)

def towerWt (Dw : Datum H) (a : WZ E) : Top.Wt (CMType H) (Dw.p + Dw.q) :=
  fun τ n => if (n : ℕ) < Dw.p then (a (τ.1, n) : ℝ) else -(a (conjEmb τ.1, Dw.p + Dw.q - 1 - n) : ℝ)

open Classical in

def flatZ (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (w : CMType H → ℤ) : WZ E :=
  fun x => if h : x.1 (H.rt : E) = H.rt0 then w ⟨x.1, h⟩ else -w ⟨conjEmb x.1, Small.conjEmb_rt_of_ne h⟩

def GoodLat (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) : Prop :=
  (latOn U h a Z).FG ∧ Submodule.span c.F (latOn U h a Z : Set (Rul Xo c)) = cuspOn U h a Z

def OntoZ (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (a : WZ E)
    (Z : Comp Xo c) : Prop :=
  ∀ σ, GoodEmb c σ → ∀ k, Over (U σ) (e Z) k → ∀ P ∈ ((U σ).X k).SS (laZ (U σ) a k),
    ∃ (m : ℕ) (as : Fin m → ℂ) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ cuspOn U h a Z) ∧
      ∀ x ∈ ((U σ).X k).dom, P x = ∑ i, as i * rdU (U σ) (fs i) k x

structure FlatSec (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (e₀ : Rul Xo c) (b : WZ E) where

  s : Rul Xo c

  s' : Rul Xo c
  s_sec : s ∈ secZ Xo c b
  s'_sec : s' ∈ secZ Xo c (-b)
  mul_eq : s * s' = e₀
  s_supp : s * e₀ = s
  s'_supp : s' * e₀ = s'

  cInf : (c.F →+* ℂ) → ℝ
  cInf_pos : ∀ σ, 0 < cInf σ
  cInf_good : ∀ σ, cInf σ = cInf (goodOf c σ)
  inf_eq : ∀ σ, GoodEmb c σ → ∀ k, Over (U σ) e₀ k → ∀ y ∈ ((U σ).X k).dom,
    lieFacZ Dw x b * ((U σ).X k).pnorm (laZ (U σ) b k) (rdU (U σ) s k) y = cInf σ

  cFin : HeightOneSpectrum (𝓞 c.F) →₀ ℝ
  fin_eq : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, v e₀ = 0 → v s = ((cFin la : ℝ) : EReal)

def FlatSec.deg {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {e₀ : Rul Xo c} {b : WZ E} (F : FlatSec U x e₀ b) : ℝ :=
  ((F.cFin.sum fun la t => t * Real.log (Ideal.absNorm la.asIdeal)) - ∑ σ : c.F →+* ℂ, Real.log (F.cInf σ)) /
    (Module.finrank ℚ c.F : ℝ)

def BirOn (h : GenFrEx Xo c) (Z : Comp Xo c) {N : ℕ} (g : Fin (N + 1) → Rul Xo c) : Prop :=
  evC h Z (g 0) ≠ 0 ∧ IntermediateField.adjoin c.F (Set.range fun j => evC h Z (g j) / evC h Z (g 0)) = ⊤

def ArchTie (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (a₁ : WZ E)
    (Z : Comp Xo c) (σ : c.F →+* ℂ) (k : (U σ).Comp) (Xa : ArchInM ((U σ).X k)) : Prop :=
  GoodEmb c σ ∧ Over (U σ) (e Z) k ∧ Xa.L = laZ (U σ) a₁ k ∧ GlobalTheory.Shares.RelIn σ ((U σ).X k) Xa ∧
    ∃ (N : ℕ) (hN : N + 1 = Xa.N) (g : Fin (N + 1) → Rul Xo c),
      Submodule.span (𝓞 c.F) (Set.range g) = latOn U h a₁ Z ∧ BirOn h Z g ∧
      ∀ j, Xa.w (Fin.cast hN j) = rdU (U σ) (g j) k

section Read

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx}

structure Reading (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (Z : Comp Xo c) where

  φ : Om Z →+* RM.Ω
  φ_cst : ∀ a : c.F, φ (algebraMap c.F (Om Z) a) = Or.𝔐.cst a

  t : Ix Dw → (RM.Ω)ˣ
  rd_eq : ∀ a : WZ E, ∀ f ∈ secZ Xo c a, Fr.rd f = ((∏ i, t i ^ exZ Dw a i : (RM.Ω)ˣ) : RM.Ω) * φ (evC h Z f)
  deg : letI := φ.toAlgebra; Module.finrank (Om Z) RM.Ω = Or.Fl.deg

end Read

def CompOf {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {T : Top.RootTower (CMType H) (Dw.p + Dw.q)}
    (o : TowerOrigin Y T) (κ : Comp Xo c ≃ T.Comp) : Prop :=
  ∀ Z, GlobalTheory.CompanionTheory.Ar.genPt (o.Fx (κ Z)).ξf = Y.j (Formalism.L2.Pj.genPt Z)

end GlobalTheory.CompanionTheory.Ar.Rec
