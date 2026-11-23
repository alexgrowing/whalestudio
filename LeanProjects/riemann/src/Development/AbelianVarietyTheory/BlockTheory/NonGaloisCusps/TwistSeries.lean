import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsLevelFn {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) (N : ℕ) (Φ : Mx D m n → ℂ) : Prop :=
  (∀ t, Φ t ≠ 0 → t ∈ Λ ∧ IsHalf e t) ∧ ∀ u ∈ Λ, IsHalf e u → ∀ t, Φ (t + N • u) = Φ t

def IntVal {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ) (S : Set (HeightOneSpectrum (𝓞 L))) (z : ℂ) : Prop :=
  ∃ a : L, σ a = z ∧ ∀ la ∈ S, la.valuation L a ≤ 1

def OverPrime {L : Type} [Field L] [NumberField L] (l : ℕ) (S : Set (HeightOneSpectrum (𝓞 L))) : Prop :=
  ∀ la ∈ S, ((l : ℕ) : 𝓞 L) ∈ la.asIdeal

def below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L)
    (S : Set (HeightOneSpectrum (𝓞 L))) : Set (HeightOneSpectrum (𝓞 K)) :=
  {p | ∃ la ∈ S, p.asIdeal = la.asIdeal.comap (RingOfIntegers.mapRingHom φ)}

def UnramAt {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L)
    (S : Set (HeightOneSpectrum (𝓞 L))) : Prop :=
  ∀ la ∈ S, ¬ (la.asIdeal.comap (RingOfIntegers.mapRingHom φ)).map (RingOfIntegers.mapRingHom φ) ≤ la.asIdeal ^ 2

structure IsTwist {L : Type} [Field L] (σ : L →+* ℂ) (p : ℕ) (xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ) : Prop where
  rat : ∀ (x : (GlobalTheory.FinalJoin.AfE D)ˣ) (a : D.host.E), (x : GlobalTheory.FinalJoin.AfE D) = 1 ⊗ₜ a → GlobalTheory.FinalJoin.NormOne x → xi x = 1
  cond : ∀ x, GlobalTheory.FinalJoin.NormOne x → GlobalTheory.FinalJoin.CongOne p x → xi x = 1
  val : ∀ x, GlobalTheory.FinalJoin.NormOne x → ∃ a : L, σ a = ((xi x : ℂˣ) : ℂ)

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Series

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev lattice₂ : AddSubgroup (WO (Vc D i) (Wc D i)) := latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True

def IsLevelVec (N : ℕ) (Φ f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ (∀ PP ∈ P, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    IsLevelFn (cA D e) (lattice₂ R i) N Φ ∧
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D e) (lattice₂ R i) 1 (R.vacP i) Φ f

def series (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (s : GA D (Vc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) (w : (R.cV i).W)
    (g : GA D (Wc D i)) : ℂ :=
  thetaKO (R.ωP i A.μ0) s g
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f
      (R.ioP i (PiTensorProduct.tprod ℂ u) w))

def IsCoefMap (c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) : Prop :=
  ∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧
    CoefficientBaseChange R i D.what₂.embLL (RingHom.id ℂ) (c0L i) c0

end Series

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m)
  (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

omit [Algebra T.Q.c.F D.what₂.LL] in

def IsTowerCover (l : ℕ) (C : Cover T ((i : ℕ) + 1) T.σ₀) : Prop :=
  C.IsUnif ∧ Squarefree C.d.pd ∧ Nat.Coprime C.d.pd l ∧
    Nat.Coprime C.d.pd (D.host.QS * D.host.q * Ideal.absNorm D.host.ccK)

variable {T i} in

def FieldBig (Lat : Submodule ℤ (VsV D i ℂ)) (C : Cover T ((i : ℕ) + 1) T.σ₀) : Prop :=
  (R.C.mu0 i * R.C.eta⁻¹).ValuesIn (-1 / 2) C.σ₂ ∧
    (∀ v ∈ Lat, ∀ m, ∃ a, C.σ₂ a = MvPolynomial.coeff m (v : Pol ℂ D.what₂.Tau (Vc D i).rank)) ∧
    ∃ φ : D.host.K →+* C.d.c₂.F, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ C.d.l₂.M

def SerIntAt (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ)
    (c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) : Prop :=
  ∃ ph : ℂ, ‖ph‖ = 1 ∧ ∀ l : ℕ, l.Prime → ∀ s ∈ GfC (Vc D i), ∀ Lat : Submodule ℤ (VsV D i ℂ), Lat.FG →
    ∃ c : ℕ, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, IsTowerCover T i l C → (∀ a, Dom a κ.n → C.IsPinned a κ.n) →
      FieldBig R Lat C → ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), OverPrime l S →
        ∀ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, IsTwist C.σ₂ C.d.pd xi →
          ∀ Φ f : WO (Vc D i) (Wc D i) → ℂ, IsLevelVec R i C.d.l₂.M Φ f → (∀ t, IntVal C.σ₂ S (Φ t)) →
            ∀ v ∈ Lat, ∃ φ ∈ C.intForms (wtA κ) κ.n S, ∀ g : GA D (Wc D i),
              castDict hV φ g = (l : ℂ) ^ c *
                (ph * (((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) * series R i u s f (c0 v) g))

omit [Algebra T.Q.c.F D.what₂.LL] in

def DescIntAt : Prop :=
  ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, IsTowerCover T i l C → C.IsPinned (wtA κ) κ.n →
    ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), OverPrime l S → UnramAt C.inc S →
      ∀ φ ∈ C.intForms (wtA κ) κ.n S, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) →
        ∃ (m : ℕ) (x : Fin m → ℂ) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)),
          (∀ a, IntVal C.σ₂ S (x a)) ∧ (∀ a, ψ a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n (below C.inc S)) ∧
            φ = ∑ a, x a • ψ a

def SerInt : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
      (∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
        ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, IsCoefMap R i c0 → SerIntAt T R i (κ i) hV u c0) ∧
      DescIntAt T i (κ i)

end GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries
