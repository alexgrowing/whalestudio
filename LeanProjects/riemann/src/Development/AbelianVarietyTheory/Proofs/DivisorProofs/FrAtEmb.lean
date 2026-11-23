import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift

namespace GlobalTheory.GalOne

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Rec

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  (σ : D.what₂.LL →+* ℂ)

abbrev zAt : Fam (Wc D i) := x0Mat (R.MW i σ)

def ConjW (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (f₀ f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  OverK σ ∧ ChiAt R i σ μ' ∧ IsEtaConj σ R.eta η' ∧ IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω ∧
    IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      R.Pg ∅ (fun _ => 1) f₀ f ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) f

end Rec

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

variable (T R i) in

abbrev OM : Type 1 := OMDat T.toCore R i Unit (fun _ => A.μ0)

abbrev Pinned (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : OM T R i) : Prop :=
  O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)

abbrev sOf (O : OM T R i) (σ' : O.c'.F →+* ℂ) : T.Q.c.F →+* ℂ := σ'.comp (incF T.Q.c O.c' O.hle)

omit [Algebra T.Q.c.F D.what₂.LL] in

abbrev dictS {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) :
    GA D (Wc D i) → Σ k, Frame ((T.U ((i : ℕ) + 1) s).X k).Ψ D.R.r := castDict hV (T.dict ((i : ℕ) + 1) s)

omit [Algebra T.Q.c.F D.what₂.LL] in

abbrev muS {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) : GA D (Wc D i) → ℂ := castDict hV (T.mu ((i : ℕ) + 1) s)

omit [Algebra T.Q.c.F D.what₂.LL] in

abbrev xS {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) (h : GA D (Wc D i)) : Data D.host.E D.R.r :=
  (T.U ((i : ℕ) + 1) s).X (dictS hV h).1

variable (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (O : OM T R i) (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ)

def FactsAt : Prop :=
  res T σ = sOf O σ' ∧ GoodEmb T.Q.c (sOf O σ') ∧ GoodEmb O.c' σ' ∧
    (∀ τ a, (R.MW i σ).ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) ∧
    IsONeg (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (zAt R i σ) ∧
    cart (R.MW i σ) = cartZ (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (zAt R i σ) ∧
    (∀ ρ, T.x₀ ((i : ℕ) + 1) (sOf O σ') (tauE D ρ) =
      Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (zAt R i σ ρ)) ∧
    (∀ ρ, relab O.c' σ' (tauE D (lab σ ρ)) = tauE D ρ) ∧
    ∀ μ' η' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → IsEtaConj σ R.eta η' →
      (∀ hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i, MuVal (Wc D i) μ' (muS hV)) ∧
      (∀ v ε, NonSplitAt D v ε → UnramAt ε μ' ∧ UnramAt ε (μ' * η'⁻¹)) ∧ HypConj R i σ μ' η'

def PointAt (hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i) (h : GA D (Wc D i)) : Prop :=
  ∃ γ ∈ GQ (Wc D i), ∃ (g : ℕ) (eT : D.what₂.Tau ≃ (xS hV h).Ψ)
    (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' σ' (xS hV h) g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i)))
    (hx : (dictS hV h).2 ∈ (xS hV h).dom),
    IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) (xS hV h) eT Dc.bas ∧ Matched T.Q.c (sOf O σ') (xS hV h) Dc.idx Dc.e ∧
    (xS hV h).p0 = (T.Q.Dw ((i : ℕ) + 1)).q ∧ SelfD (xS hV h) (xS hV h).Λ ∧
    latW (rank_Wc i) (xS hV h).Λ = latG (Wc D i) (γ * h) ∧
    (dictS hV h).2 = frOf (rank_Wc i) eT (mvZ R.θ (γ * h) (zAt R i σ)) ∧
    letI : Algebra T.Q.c.F ℂ := (sOf O σ').toAlgebra
    (∃ (A₀ : AnFib (xS hV h) Dc.bas Dc.idx Dc.e (dictS hV h).2 (xS hV h).Λ
        (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩)) (th : (Fin g → ℂ) → ℂ),
      A₀.Reads 1 (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩).s th ∧
        MeanOne (xS hV h) Dc.bas Dc.idx (dictS hV h).2 (xS hV h).Λ th) ∧
    ∀ (g' : ℕ) (bas : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] (xS hV h).Λ) (idx : Fin g' ≃ (xS hV h).Ψ × Fin D.R.r)
      (e : Fin g' ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))), IsSympl (xS hV h) bas → Matched T.Q.c (sOf O σ') (xS hV h) idx e →
      ∀ (A₁ : AnFib (xS hV h) bas idx e (dictS hV h).2 (xS hV h).Λ
          (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩))
        (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ a, mk a ∈ (xS hV h).Λ) →
        MarkAd (rank_Wc i) T.Q.l (iotaW T i) (γ * h) mk → A₁.Marked mk

def FrAtEmb (hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ : WO (Vc D i) (Wc D i) → ℂ)
    (cc : (T.U ((i : ℕ) + 1) (sOf O σ')).Comp → ℂ) : Prop :=
  FrConst R.ψ R.θ (Vc D i) (rank_Wc i) ω f₀ (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV) (muS hV) (zAt R i σ) cc

def TermAt (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (ε : ℤˣ) : Prop :=
  ∀ (h : O.Cl' () → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))),
    RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) →
    ∀ (k : O.Cl' ()) (g' : GA D (Wc D i)) (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ)
      (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r),
      IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) X eT bas → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q →
      ∀ L : Lt D.host.E D.R.r, SelfD X L → latW (rank_Wc i) L = latG (Wc D i) g' →
      ∀ v : TF (Vc D i).rank g, IsVac X bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) L) v →
      ∀ a : ℂ, Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (zAt R i σ))) (a • v) (ω (1, g') f₀) →
      ∀ mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), (∀ b, mk₂ b ∈ L) →
        MarkAd (rank_Wc i) (O.dδ ()).l₂ (iotaW T i) g' mk₂ →
      ∀ Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E,
        IsRoots (O.dδ ()).l₂ L ((ε : ℤ) • mk₂) (O.Nc () k) Y →
        GlobalTheory.SW.IsSB (gphi X bas (T.Q.H.w0 : D.host.E) (O.La () k).La L v (fun q => inC O.c' (O.w () k q)) Y) ∧
        Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (zAt R i σ)))
          ((a * σ' (O.ep () k * ((((O.La () k).mIdx (O.Nc () k) D.R.r : O.c'.F))⁻¹ *
            ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) : O.c'.F))⁻¹ *
            ((O.La () k).zCard (O.Nc () k) D.R.r : O.c'.F)))) •
            gphi X bas (T.Q.H.w0 : D.host.E) (O.La () k).La L v (fun q => inC O.c' (O.w () k q)) Y) (ω (h k, g') f)

def IsUp (x : VsV D i D.what₂.LL) (x' : VsV D i O.c'.F) : Prop :=
  (x' : Pol O.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map O.jL (x : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank)

def IsLtAt (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank) : Prop :=
  ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((relab O.c' σ' ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
    (relab O.c' σ' ℓ.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D (lt ℓ).1) ∧
      ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))

def IoAt {c : CoefA (Vc D i)} (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (f : WO (Vc D i) (Wc D i) → ℂ)
    (Λ : c.W → WO (Vc D i) (Wc D i) → ℂ) (ph : ℂ) : Prop :=
  ∀ x x', IsUp O x x' → ∃ Q : PolF D (Wc D i).rank (Vc D i).rank,
    Λ (c₁ x) = fv R.ψ R.θ (Vc D i) (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (zAt R i σ) f Q ∧
    ∀ (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ)
      (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' σ' X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))),
      (∀ ρ, (eT ρ).1 = tauE D ρ) → MvPolynomial.C ph * toP (Vc D i) (rank_Wc i) eT Dc.hr Q =
        MvPolynomial.C ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) *
          MvPolynomial.rename Dc.eL (MvPolynomial.map σ' (O.io x'))

def CovAt (c0 : ℂ) : Prop :=
  letI : Algebra (O.dδ ()).c₂.F ℂ := (σ'.comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)).toAlgebra
  ∀ y₂ : FrPt (O.dδ ()).Xo₂ (O.dδ ()).c₂ ℂ, evR (O.dδ ()).Xo₂ (O.dδ ()).c₂ (O.dδ ()).cδ y₂ = c0

end GlobalTheory.GalOne

end
