import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsLevDatum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Set (Fin S.rank → D.host.E))
    (ΛT : Set (Fin T.rank → D.host.E)) (N : ℕ) (k : Subfield ℂ) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (Φ : WO S T → ℂ),
    IsIdemSum e P ∧ (∀ PP ∈ P, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    (∀ t, Φ t ≠ 0 → t ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e t) ∧
    (∀ u ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e u → ∀ t, Φ (t + N • u) = Φ t) ∧
    (∀ t, Φ t ∈ k) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Φ f

def RayIn (D : D7) (N : ℕ) (k : Subfield ℂ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra D.host.K L) (_ : IsAbelianGalois D.host.K L),
    GlobalTheory.FieldSize.IsRay L (Ideal.span {((N : ℕ) : 𝓞 D.host.K)}) ∧
      ∃ j : L →+* ℂ, j.comp (algebraMap D.host.K L) = D.host.φ₀.comp (algebraMap D.host.K D.host.E) ∧ ∀ x, j x ∈ k

def IsAuxiliarySplitSquarefreeLevel (D : D7) (M pd : ℕ) : Prop :=
  Odd pd ∧ Squarefree pd ∧ (∀ p : ℕ, p.Prime → p ∣ pd → jacobiSym (-(D.host.d : ℤ)) p = 1) ∧ Nat.Coprime pd M ∧
    Nat.Coprime pd (D.host.QS * D.host.q * Ideal.absNorm D.host.ccK)

def IsTwist (pd : ℕ) {k : Type} [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle) : Prop :=
  ChrEq δc δ ∧ (∃ n : ℕ, 0 < n ∧ δ.OrderDvd n) ∧ δ.TrivOn D.host.F ∧ (∀ v, δ.TameAt v) ∧
    (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((pd : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal → δ.UnrAt v) ∧ δ.ValuesIn 0 σ

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Real

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def SmallIn {k : Type} [Field k] (σ : k →+* ℂ) : Prop :=
  (R.C.mu0 i).ValuesIn 0 σ ∧ R.C.eta.ValuesIn (1 / 2) σ

def ratVec (c0 : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (k : Subfield ℂ) : Submodule k (R.cV i).W :=
  Submodule.span k {w | ∃ v : VsV D i D.what₂.LL,
    (∀ m, D.what₂.embLL (MvPolynomial.coeff m (v : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D i).rank)) ∈ k) ∧ w = c0 v}

def harmVec (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W) (f : WO (Vc D i) (Wc D i) → ℂ) :
    WO (Vc D i) (Wc D i) → ℂ :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f
    (R.ioP i (PiTensorProduct.tprod ℂ u) w)

end Real

section Cover

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) {σ : T.Q.c.F →+* ℂ}
  (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (C : Cover T ((i : ℕ) + 1) σ)

def GoodCover (n : ℕ) : Prop :=
  C.IsUnif ∧ (∀ a, Formalism.L2.Pj.Dom a n → C.IsPinned a n) ∧ IsAuxiliarySplitSquarefreeLevel D T.Q.l.M C.d.pd ∧ SmallIn R i C.σ₂ ∧
    RayIn D (T.Q.l.M * C.d.pd) C.σ₂.fieldRange

def IsRat (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (φ : GA D (Wc D i) → ℂ) : Prop :=
  ∃ φ' ∈ C.ratForms (wtA κ) κ.n, castDict hV φ' = φ

def SeriesRatOn (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ)
    (c0 : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (ph : ℂ) : Prop :=
  ∀ s ∈ GfC (Vc D i), ∀ f : WO (Vc D i) (Wc D i) → ℂ,
    IsLevDatum R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (T.Q.l.M * C.d.pd) C.σ₂.fieldRange (R.vacP i) f →
    ∀ w ∈ ratVec R i c0 C.σ₂.fieldRange,
      IsRat T i hV C κ (fun g => ph * thetaKO (R.ωP i A.μ0) s g (harmVec R i u w f)) ∧
      ∀ (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist C.d.pd C.σ₂ δ δc →
        (∀ dd : GA D (Wc D i) → ℂ, MuVal (Wc D i) δc dd →
          IsRat T i hV C κ (fun g => dd g * (ph * thetaKO (R.ωP i A.μ0) s g (harmVec R i u w f)))) ∧
        ∀ om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ),
          IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).1
            (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).2 om →
          IsRat T i hV C κ (fun g => ph * thetaKO om s g (harmVec R i u w f))

end Cover

def SeriesRat : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → VStd D i →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∃ ph : ℂ, ‖ph‖ = 1 ∧ ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
        SeriesRatOn T R i hV C (κ i) u (c0L i) ph

theorem auxiliarySplitSquarefreeLevel_one (M : ℕ) : IsAuxiliarySplitSquarefreeLevel D M 1 :=
  ⟨odd_one, squarefree_one, fun _ hp h => absurd (Nat.dvd_one.1 h) hp.ne_one, Nat.coprime_one_left _, Nat.coprime_one_left _⟩

end GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
