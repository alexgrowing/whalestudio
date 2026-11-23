import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.Ar.Rec

section Forms

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

abbrev WZ (E : Type) [Field E] : Type := (E →+* ℂ) × ℕ → ℤ

def exZ (Dw : Datum H) (a : WZ E) : Ix Dw → ℤ
  | none => 0
  | some x => a (x.1, x.2)

def secWZ {K : Type} [Field K] {ι : Type} [Fintype ι] (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop)
    (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop) (e : ι → ℤ) :
    Submodule K (Rules pts) where
  carrier := {f | IsNatural pts mapR f ∧ ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
    f p y' = (∏ i, ((t i ^ e i : (p.R)ˣ) : p.R)) * f p y}
  zero_mem' := ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h, hg.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h, hg.2 p t y y' h, mul_add]⟩
  smul_mem' := fun c f hf =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h]⟩

def latIn {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R]
    (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) :
    Submodule (𝓞 K) R :=
  (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem mem_latIn {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (f : R) : f ∈ latIn C Vs hV ↔ f ∈ C ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v f :=
  ⟨fun ⟨g, hg, e⟩ => e ▸ ⟨g.2, hg⟩, fun h => ⟨⟨f, h.1⟩, h.2, rfl⟩⟩

variable (Xo : Moduli Dw l) (c : Coeff l)

def secZ (a : WZ E) : Submodule c.F (Rul Xo c) :=
  secWZ (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (exZ Dw a)

theorem secZ_nat (a : (E →+* ℂ) × ℕ → ℕ) : secZ Xo c (fun x => (a x : ℤ)) = sec Xo c a 0 := by
  have h : ∀ (S : Type) [CommRing S] (t : Ix Dw → Sˣ),
      (∏ i, ((t i ^ exZ Dw (fun x => (a x : ℤ)) i : Sˣ) : S)) = wchar (ex Dw a 0) t := by
    intro S _ t
    refine Finset.prod_congr rfl fun i _ => ?_
    cases i <;> simp [exZ, ex]
  ext f
  refine and_congr Iff.rfl (forall_congr' fun p => forall_congr' fun t => forall_congr' fun y => forall_congr' fun y' =>
    forall_congr' fun _ => ?_)
  rw [h]

variable {Xo c} in
open Classical in

def laZ {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (a : WZ E) (k : U.Comp) : Wt (U.X k).Ψ r :=
  fun τ j => if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0)
    else -a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ))

theorem laZ_nat {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) :
    laZ U (fun x => (a x : ℤ)) = laU U a 0 := by
  funext k τ j
  simp [laZ, laU]

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cuspZ (a : WZ E) : Submodule c.F (Rul Xo c) :=
  secZ Xo c a ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laZ (U σ) a)).comap (rdU (U σ))

theorem cuspZ_nat (a : (E →+* ℂ) × ℕ → ℕ) : cuspZ Xo c U (fun x => (a x : ℤ)) = cusp Xo c U a 0 := by
  unfold cuspZ cusp
  simp only [secZ_nat, laZ_nat]

variable {Xo c}

def evL (h : GenFrEx Xo c) (Z : Comp Xo c) : Rul Xo c →ₗ[c.F] Om Z :=
  evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)

theorem evL_apply (h : GenFrEx Xo c) (Z : Comp Xo c) (f : Rul Xo c) : evL h Z f = evC h Z f := rfl

def cuspOn (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) : Submodule c.F (Rul Xo c) :=
  cuspZ Xo c U a ⊓ ⨅ (Z' : Comp Xo c) (_ : Z' ≠ Z), LinearMap.ker (evL h Z')

def latOn (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) : Submodule (𝓞 c.F) (Rul Xo c) :=
  latIn (cuspOn U h a Z) (valSet Xo c (algCls Xo c)) isVal_valSet

def volL (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) (Dn : ℕ) : ℝ :=
  limsup (fun n : ℕ => (Dn.factorial : ℝ) * (Module.finrank c.F (cuspOn U h (n • a) Z) : ℝ) / (n : ℝ) ^ Dn) atTop

def lieFacZ (Dw : Datum H) (x : ℝ) (a : WZ E) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

variable {D : D7} (W : HSp D) (dict : ∀ σ, GA D W → Σ k, Frame ((U σ).X k).Ψ r)

def ipAll (σ : c.F →+* ℂ) (f g : Rul Xo c) : ℂ :=
  ∫ q, jFn W σ (rdU (U σ)) (dict σ) (fun _ => 1) f q * conj (jFn W σ (rdU (U σ)) (dict σ) (fun _ => 1) g q) ∂(muQ1 W)

open Classical in

def ipOn (x : ℝ) (a : WZ E) (e : Rul Xo c) (σ : c.F →+* ℂ) (f g : Rul Xo c) : ℂ :=
  let z : ℂ := ((lieFacZ Dw x a ^ 2 : ℝ) : ℂ) * ipAll U W dict (goodOf c σ) f g / ipAll U W dict (goodOf c σ) e e
  if GoodEmb c σ then z else conj z

open Classical in

def ipGl (x : ℝ) (a : WZ E) (σ : c.F →+* ℂ) (f g : Rul Xo c) : ℂ :=
  let z : ℂ := ((lieFacZ Dw x a ^ 2 : ℝ) : ℂ) * ipAll U W dict (goodOf c σ) f g
  if GoodEmb c σ then z else conj z

def volU (e : Rul Xo c) (σ : c.F →+* ℂ) : ℝ :=
  ∫ q, Complex.normSq (jFn W (goodOf c σ) (rdU (U (goodOf c σ))) (dict (goodOf c σ)) (fun _ => 1) e q) ∂(muQ1 W)

end Forms

end GlobalTheory.CompanionTheory.Ar.Rec
