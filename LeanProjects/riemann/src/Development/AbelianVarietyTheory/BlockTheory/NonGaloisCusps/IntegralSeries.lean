import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralSeries

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def placesOver (K : Type) [Field K] (l : ℕ) : Set (HeightOneSpectrum (𝓞 K)) := {la | (l : 𝓞 K) ∈ la.asIdeal}

def IntOver {K : Type} [Field K] [NumberField K] (l : ℕ) (y : K) : Prop :=
  ∀ la ∈ placesOver K l, la.valuation K y ≤ 1

def UnramOver {K K' : Type} [Field K] [Field K'] (φ : K →+* K') (l : ℕ) : Prop :=
  ∀ P ∈ placesOver K' l,
    ¬ (P.asIdeal.comap (RingOfIntegers.mapRingHom φ)).map (RingOfIntegers.mapRingHom φ) ≤ P.asIdeal ^ 2

variable {D : D7}

section Cover

variable {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)

def IsPinnedCover (n : ℕ) : Prop :=
  C.IsUnif ∧ Squarefree C.d.pd ∧ Nat.Coprime C.d.pd (D.host.QS * D.host.q * Ideal.absNorm D.host.ccK) ∧
    ∀ a : (D.host.E →+* ℂ) × ℕ → ℕ, Formalism.L2.Pj.Dom a n → C.IsPinned a n

def InField (z : ℂ) : Prop := ∃ y : C.d.c₂.F, C.σ₂ y = z

def InInt (l : ℕ) (z : ℂ) : Prop := ∃ y : C.d.c₂.F, IntOver l y ∧ C.σ₂ y = z

def HasRay : Prop :=
  ∃ Rf : IntermediateField ℚ ℂ,
    GlobalTheory.Mem.Fld.IsRayFieldIn D.host.φ₀ (GlobalTheory.Mem.Fld.natIdeal D.host.E (T.Q.l.M * C.d.pd)) Rf ∧ ∀ z ∈ Rf, InField C z

def IsTwist (W : HSp D) (u : GA D W → ℂ) : Prop :=
  ∃ δ : (AE D)ˣ →* Circle, IsHeckeChar D δ ∧ (∀ a, δ (idF D a) = 1) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x, δ x ^ m = 1) ∧
    (∀ x, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = C.d.pd • y) → δ x = 1) ∧
    (∀ x, InField C ((δ x : Circle) : ℂ)) ∧ MuVal W δ u

end Cover

section Series

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev latVW : AddSubgroup (WO (Vc D i) (Wc D i)) := latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True

def IsLevDatum (N : ℕ) (val : ℂ → Prop) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∃ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (Φ : WO (Vc D i) (Wc D i) → ℂ),
    IsIdemSum e P ∧ (∀ PP ∈ P, (N : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    (∀ t, Φ t ≠ 0 → t ∈ latVW R i ∧ IsHalf (cA D e) t) ∧
    (∀ u ∈ latVW R i, IsHalf (cA D e) u → ∀ t, Φ (t + N • u) = Φ t) ∧ (∀ t, val (Φ t)) ∧
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D e) (latVW R i) 1 (R.vacP i) Φ f

def fock (B : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) (f : WO (Vc D i) (Wc D i) → ℂ)
    (P : PolF D (Wc D i).rank (Vc D i).rank) : WO (Vc D i) (Wc D i) → ℂ :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) B (onb (R.MW i (sg0 D A))) f P

def ratB {n : ℕ} (b : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ := b.map (tauE D τ)

def IsHarm (v₀ : (R.MW i (sg0 D A)).Vec) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E)
    (P : PolF D (Wc D i).rank (Vc D i).rank) : Prop :=
  ∃ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ ρ) ∧
    fock R i (ratB b) (R.vacP i) P = fock R i (R.BV i) (R.vacP i) (R.ioP i (PiTensorProduct.tprod ℂ u) w)

def series (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E) (s : GA D (Vc D i))
    (f : WO (Vc D i) (Wc D i) → ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank) (g : GA D (Wc D i)) : ℂ :=
  thetaKO (R.ωP i A.μ0) s g (fock R i (ratB b) f P)

end Series

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ)
  (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

def SerIntAt (v₀ : (R.MW i (sg0 D A)).Vec) : Prop :=
  ∃ ph : ℂ, ‖ph‖ = 1 ∧
    ∀ l : ℕ, l.Prime → ∀ s ∈ GfC (Vc D i),
    ∀ b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b →
    ∀ (m : ℕ) (Pb : Fin m → PolF D (Wc D i).rank (Vc D i).rank), (∀ k, IsHarm R i v₀ b (Pb k)) →
    ∃ c : ℕ, ∀ C : Cover T ((i : ℕ) + 1) σ, IsPinnedCover C κ.n → Nat.Coprime C.d.pd l → HasRay C →
      (R.C.mu0 i * R.C.eta⁻¹).ValuesIn (-1 / 2) C.σ₂ → (∀ k d, InField C ((Pb k).coeff d)) →
      ∀ f, IsLevDatum R i (T.Q.l.M * C.d.pd) (InInt C l) f →
      ∀ a : Fin m → ℂ, (∀ k, InInt C l (a k)) → ∀ u, IsTwist C (Wc D i) u →
        ∃ φ ∈ C.intForms (wtA κ) κ.n (placesOver C.d.c₂.F l), ∀ g,
          castDict hV φ g = (l : ℂ) ^ c * (ph * u g * series R i b s f (∑ k, a k • Pb k) g)

omit [Algebra T.Q.c.F D.what₂.LL] in

def DescIntAt (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ l : ℕ, l.Prime → ∀ C : Cover T j σ, IsPinnedCover C n → Nat.Coprime C.d.pd l → UnramOver C.inc l →
    ∀ φ ∈ C.intForms a n (placesOver C.d.c₂.F l), (∀ k ∈ T.Kf j σ, ∀ h, φ (h * k) = φ h) →
      ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (f : Fin m → GA D (T.V j σ) → ℂ), (∀ k, IntOver l (x k)) ∧
        (∀ k, f k ∈ baseInt T j σ a n (placesOver T.Q.c.F l)) ∧ ∀ h, φ h = ∑ k, C.σ₂ (x k) * f k h

def SerInt : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
        SerIntAt T R i σ hV (κ i) (v₀ i (sg0 D A)) ∧ DescIntAt T σ ((i : ℕ) + 1) (wtA (κ i)) (κ i).n

section Checks

variable {T σ} {j : ℕ} (C : Cover T j σ)

example (K : Type) [Field K] [NumberField K] (l : ℕ) : UnramOver (RingHom.id K) l := by
  intro P _ h
  have e : RingOfIntegers.mapRingHom (RingHom.id K) = RingHom.id _ := RingHom.ext fun _ => rfl
  rw [e, Ideal.comap_id, Ideal.map_id] at h
  exact (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl).not_ge h

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralSeries
