import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.IntegralSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReframeVStdOfPosDef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtLinearIndependent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTwistProps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRayFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowestWeightVectorsAtRows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelFunctionFiniteRange

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cmp.SeriesRay

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke

variable {D : D7}

section Forms

variable {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)

theorem sum_mem_intForms (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) {m : ℕ} (x : Fin m → C.d.c₂.F)
    (hx : ∀ k, ∀ la ∈ S, la.valuation C.d.c₂.F (x k) ≤ 1) (φ : Fin m → GA D (T.V j σ) → ℂ) (hφ : ∀ k, φ k ∈ C.intForms a n S) :
    (∑ k, C.σ₂ (x k) • φ k) ∈ C.intForms a n S := by
  choose f hf e using hφ
  refine ⟨∑ k, x k • f k, ⟨⟨sum_mem fun k _ => Submodule.smul_mem _ _ (hf k).1.1, ?_⟩, fun la hla v hv => ?_⟩, ?_⟩
  · rw [map_sum]
    exact sum_mem fun k _ => by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (hf k).1.2
  · have hV := isVal_valSet la v hv
    exact GlobalTheory.IdemInt.nonneg_sum hV _ _ fun k _ => GlobalTheory.IdemInt.nonneg_smul hV (hx k la hla) ((hf k).2 la hla v hv)
  · simp only [← e, Cover.rd, map_sum, map_smulₛₗ, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

end Forms

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

variable {T i} in

def FieldRay (Lat : Submodule ℤ (VsV D i ℂ)) (C : Cover T ((i : ℕ) + 1) T.σ₀) : Prop :=
  (R.C.mu0 i * R.C.eta⁻¹).ValuesIn (-1 / 2) C.σ₂ ∧
    (∀ v ∈ Lat, ∀ m, ∃ a, C.σ₂ a = MvPolynomial.coeff m (v : Pol ℂ D.what₂.Tau (Vc D i).rank)) ∧ IntegralSeries.HasRay C

def SerIntRay (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ)
    (c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) : Prop :=
  ∃ ph : ℂ, ‖ph‖ = 1 ∧ ∀ l : ℕ, l.Prime → ∀ s ∈ GfC (Vc D i), ∀ Lat : Submodule ℤ (VsV D i ℂ), Lat.FG →
    ∃ c : ℕ, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, TwistSeries.IsTowerCover T i l C → (∀ a, Dom a κ.n → C.IsPinned a κ.n) →
      FieldRay R Lat C → ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), TwistSeries.OverPrime l S →
        ∀ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, TwistSeries.IsTwist C.σ₂ C.d.pd xi →
          ∀ Φ f : WO (Vc D i) (Wc D i) → ℂ, TwistSeries.IsLevelVec R i C.d.l₂.M Φ f → (∀ t, TwistSeries.IntVal C.σ₂ S (Φ t)) →
            ∀ v ∈ Lat, ∃ φ ∈ C.intForms (wtA κ) κ.n S, ∀ g : GA D (Wc D i),
              castDict hV φ g = (l : ℂ) ^ c *
                (ph * (((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) *
                  TwistSeries.series R i u s f (c0 v) g))

omit [Algebra T.Q.c.F D.what₂.LL] in

def DescIntAll : Prop :=
  ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, TwistSeries.IsTowerCover T i l C → (∀ a, Dom a κ.n → C.IsPinned a κ.n) →
    TwistSeries.UnramAt C.inc (IntegralSeries.placesOver C.d.c₂.F l) →
      ∀ φ ∈ C.intForms (wtA κ) κ.n (IntegralSeries.placesOver C.d.c₂.F l),
        (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) →
        ∃ (m : ℕ) (x : Fin m → ℂ) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)),
          (∀ a, TwistSeries.IntVal C.σ₂ (IntegralSeries.placesOver C.d.c₂.F l) (x a)) ∧
            (∀ a, ψ a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n (TwistSeries.below C.inc (IntegralSeries.placesOver C.d.c₂.F l))) ∧
            φ = ∑ a, x a • ψ a

section Data

variable {T}

variable {R i}

abbrev sb (U : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) :=
  GlobalTheory.AdTh.PhaseMap.sub (m := (Wc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1) U

end Data

section First

variable {T R i κ}

def ker1 (s : GA D (Vc D i)) (g : GA D (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) : PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] ℂ :=
  LinearMap.proj 0 ∘ₗ R.ωP i A.μ0 (s, g) ∘ₗ
    pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) f

variable {hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i} {v₀ : (R.MW i (sg0 D A)).Vec} {u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ}
  {c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W} {ka : ℂ} {J : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}

variable (u c0 ka J) in

structure Dict : Prop where
  norm : ‖ka‖ = 1
  rat : ∀ k : Subfield ℂ, (inC T.Q.c).fieldRange ≤ k → ∀ v : VsV D i ℂ,
    (∀ m, MvPolynomial.coeff m (v : Pol ℂ D.what₂.Tau (Vc D i).rank) ∈ k) ↔ ∀ d, MvPolynomial.coeff d (J v) ∈ k
  eq : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ v,
    IntegralSeries.fock R i (R.BV i) f (R.ioP i (PiTensorProduct.tprod ℂ u) (c0 v)) = ka • IntegralSeries.fock R i (fun _ => 1) f (J v)

theorem Dict.series (h : Dict u c0 ka J) {f} (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) (s v g) :
    TwistSeries.series R i u s f (c0 v) g = ka * ker1 (R := R) s g f (J v) := by
  have e := congrArg (fun x => R.ωP i A.μ0 (s, g) x 0) (h.eq f hf v)
  simp only [map_smul] at e
  exact e

end First

def SerIntStd : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
      IntegralSeries.SerIntAt T R i T.σ₀ hV (κ i) (v₀ i (sg0 D A)) ∧ IntegralSeries.DescIntAt T T.σ₀ ((i : ℕ) + 1) (wtA (κ i)) (κ i).n

def SerIntCommon : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
      (∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
        ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, TwistSeries.IsCoefMap R i c0 → SerIntRay T R i (κ i) hV u c0) ∧
      DescIntAll T i (κ i)

end GlobalTheory.Cmp.SeriesRay
