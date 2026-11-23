import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift

open scoped ComplexConjugate InnerProductSpace Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.AutMult GlobalTheory.Cont
open GlobalTheory.Mem.Th (CptF)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev FinPl (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.F)

abbrev RealMat (V : HSp D) : Type := D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

section Vectors

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : RealMat S) (sT : RealMat T)

def IsFockVec (Φ : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T Φ ∧ ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N →
    l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) Φ = 0

def IsSphOff (LS : Lat S) (LT : Lat T) (Sf : Finset (FinPl D)) (Φ : WO S T → ℂ) : Prop :=
  IsLatVac (heisO ψ S T) (latO S T LS LT fun v => v ∉ Sf) Φ

def IsCoef {X : Type} (x : X → WO S T → ℂ) (Φ : WO S T → ℂ) (c : X → ℂ) : Prop :=
  ∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧
    ∀ p, c p = ∫ w in 𝓕, x p w * conj (Φ w) ∂μ

end Vectors

section Kernel

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle)
  (sA : RealMat A) (sB : RealMat B)

def IsKernelPair (o : Bool) (P : (WO B A → ℂ) → Prop) (Q : (WO A B → ℂ) → Prop) (K₁ K₂ : GA D A → GA D B → ℂ)
    (c : GA D A → ℂ) : Prop :=
  match o with
  | true => ∃ (om : GA D B × GA D A →* Module.End ℂ (WO B A → ℂ)) (Φ₁ Φ₂ : WO B A → ℂ),
      IsWeilDatumO ψ B A χB χA om ∧ IsFockVec ψ θ B A sB sA Φ₁ ∧ IsFockVec ψ θ B A sB sA Φ₂ ∧ P Φ₁ ∧ P Φ₂ ∧
      (∀ g h, K₁ g h = thetaKO om h g Φ₁) ∧ (∀ g h, K₂ g h = thetaKO om h g Φ₂) ∧
      IsCoef B A (fun g : GA D A => om (1, g) Φ₁) Φ₂ c
  | false => ∃ (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (Φ₁ Φ₂ : WO A B → ℂ),
      IsWeilDatumO ψ A B χA χB om ∧ IsFockVec ψ θ A B sA sB Φ₁ ∧ IsFockVec ψ θ A B sA sB Φ₂ ∧ Q Φ₁ ∧ Q Φ₂ ∧
      (∀ g h, K₁ g h = conj (thetaKO om g h Φ₁)) ∧ (∀ g h, K₂ g h = conj (thetaKO om g h Φ₂)) ∧
      IsCoef A B (fun g : GA D A => om (g, 1) Φ₁) Φ₂ fun g => conj (c g)

variable {A B}

def lift (m : Measure (GA D A)) (K : GA D A → GA D B → ℂ) (f : GA D A → ℂ) : GA D B → ℂ :=
  fun h => petersson A m (fun g => K g h) f

def LiftConv (m : Measure (GA D A)) (ν : Measure (GA D B)) (K : GA D A → GA D B → ℂ) (f : GA D A → ℂ) : Prop :=
  (∀ h, Integrable (AutomorphicL2Unitary.descend (GQ A) fun g => K g h * conj (f g)) (autMeasure A m)) ∧ MemL2Quotient (GQ B) ν (lift m K f)

variable (B) in

def volQ (ν : Measure (GA D B)) : ℝ := (autMeasure B ν).real Set.univ

variable (A B) in

def HidaSetting (t : ℕ) (cA : CptF A) : Prop :=
  1 ≤ A.rank ∧ 1 ≤ t ∧ B.rank = A.rank + t ∧ IsInfFam θ ∧ HSpace.SigOK A ∧ IsCartanFrame A cA ∧
    (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) ∧ (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) ∧
    ∀ τ, cA τ * sA τ = Formalism.UG.Jpq (A.sig (tauE D τ)).1 (A.sig (tauE D τ)).2 * cA τ

end Kernel

def Convergent (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (o : Bool) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ)
    (m : Measure (GA D A)) (ν : Measure (GA D B)) (f₁ f₂ : GA D A → ℂ),
    HidaSetting θ A B sA sB t cA → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t →
    IsKernelPair ψ θ A B χA χB sA sB o (fun _ => True) (fun _ => True) K₁ K₂ c →
    m.IsHaarMeasure → ν.IsHaarMeasure → f₁ ∈ A0 θ A cA → f₂ ∈ A0 θ A cA →
    LiftConv m ν K₁ f₁ ∧ LiftConv m ν K₂ f₂ ∧
      Integrable (fun g => c g * conj (petersson A m (rTr A g f₁) f₂)) m ∧
      petersson B ν (lift m K₁ f₁) (lift m K₂ f₂) = volQ B ν * ∫ g, c g * conj (petersson A m (rTr A g f₁) f₂) ∂m

section Local

variable (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D))

def hgtW (w : InfinitePlace D.host.F) (g : Gw A w) : ℝ :=
  Doubling.hgtArch D.sp.cm.sig (Doubling.dblSp A).gram w (Formalism.UG.bc (compInf _ _ w) a)
    (Doubling.ioH _ D.sp.cm.sig (Doubling.gram_hdbl A) (g, 1))

def hgtV (v : FinPl D) (g : Gv A v) : ℝ :=
  Doubling.hgtFin D.sp.cm.sig (Doubling.dblSp A).gram L v (Doubling.ioH _ D.sp.cm.sig (Doubling.gram_hdbl A) (g, 1))

variable {Hs : Formalism.MainNotions.SchurIrreducible.Pl D.host.F → Type} [∀ v, NormedAddCommGroup (Hs v)] [∀ v, InnerProductSpace ℂ (Hs v)]
  (δ : ∀ v, GPl D.sp.cm.sig A.gram v →* (Hs v →L[ℂ] Hs v)) (x y : ∀ v, Hs v) (s₀ s : ℂ)

def integrandW (w : InfinitePlace D.host.F) (c : Gw A w → ℂ) : Gw A w → ℂ :=
  fun g => c g * (hgtW A a w g : ℂ) ^ (s - s₀) * conj ⟪y (.inl w), δ (.inl w) g (x (.inl w))⟫_ℂ

def integrandV (v : FinPl D) (c : Gv A v → ℂ) : Gv A v → ℂ :=
  fun g => c g * (hgtV A L v g : ℂ) ^ (s - s₀) * conj ⟪y (.inr v), δ (.inr v) g (x (.inr v))⟫_ℂ

variable (Sf : Finset (FinPl D)) (ca : ∀ w, Gw A w → ℂ) (cf : ∀ v, Gv A v → ℂ) (ma : ∀ w, Measure (Gw A w))
  (mf : ∀ v, Measure (Gv A v))

def zetaS : ℂ :=
  (∏ w, ∫ g, integrandW A a δ x y s₀ s w (ca w) g ∂ma w) * ∏ v ∈ Sf, ∫ g, integrandV A L δ x y s₀ s v (cf v) g ∂mf v

def ConvLeft (r : ℝ) : Prop :=
  (∀ w, ∃ s₁ : ℝ, s₁ < r ∧ Integrable (integrandW A a δ x y r s₁ w (ca w)) (ma w)) ∧
    ∀ v ∈ Sf, ∃ s₁ : ℝ, s₁ < r ∧ Integrable (integrandV A L δ x y r s₁ v (cf v)) (mf v)

def FactorsOn (c : GA D A → ℂ) : Prop :=
  ∀ g : GA D A, (∀ v ∉ Sf, proj D.sp.cm.sig A.gram v g = 1) →
    c g = (∏ w, ca w (projArch D.sp.cm.sig A.gram w g)) * ∏ v ∈ Sf, cf v (proj D.sp.cm.sig A.gram v g)

def UnitSphOff : Prop :=
  ∀ v ∉ Sf, x (.inr v) = y (.inr v) ∧ ‖x (.inr v)‖ = 1 ∧
    ∀ k : Gv A v, k ∈ stabLoc D.sp.cm.sig A.gram L v → δ (.inr v) k (x (.inr v)) = x (.inr v)

end Local

def EulerShape (D : D7)
    (Case : ∀ (_ : AddChar (AF D.host.F) ℂ) (_ : InfFam D) (A _ : HSp D) (_ _ : (AE D)ˣ →* Circle) (_ : RealMat A) (_ : ℕ)
      (_ : Bool) (_ : Measure (GA D A)) (_ : Set (GA D A → ℂ)), Prop)
    (Val : (ℂ → ℂ) → ℂ → ℂ → Prop) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D))
    (o : Bool) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ)
    (ca : ∀ w, Gw A w → ℂ) (cf : ∀ v, Gv A v → ℂ)
    (ma : ∀ w, Measure (Gw A w)) (mf : ∀ v, Measure (Gv A v)) (m : Measure (GA D A)) [m.IsHaarMeasure]
    [m.IsMulRightInvariant] (ν : Measure (GA D B)) [ν.IsHaarMeasure]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : GA D A →* (H →L[ℂ] H))
    (Hs : Formalism.MainNotions.SchurIrreducible.Pl D.host.F → Type) [∀ v, NormedAddCommGroup (Hs v)] [∀ v, InnerProductSpace ℂ (Hs v)]
    (δ : ∀ v, GPl D.sp.cm.sig A.gram v →* (Hs v →L[ℂ] Hs v)) (ξ : ∀ v, Hs v) (tens : (∀ v, Hs v) → H)
    (y₁ y₂ : ∀ v, Hs v) (x₁ x₂ : finVec A θ cA σ) (ι₁ ι₂ : finVec A θ cA σ →ₗ[ℂ] (GA D A → ℂ))
    (par : LFun.Fam D.host.E),

    HidaSetting θ A B sA sB t cA → Doubling.IsMaj A a →
    (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1) →
    IsSelfDualC A LA → IsSelfDualC B LB →

    (∀ v ∉ Sf, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) →
    LFun.UnrOff χA (Sf : Set (FinPl D)) → LFun.UnrOff χB (Sf : Set (FinPl D)) →

    IsRestrictedProd D.sp.cm.sig A.gram LA ma mf m → (∀ v ∉ Sf, mf v (stabLoc D.sp.cm.sig A.gram LA v) = 1) →

    IsKernelPair ψ θ A B χA χB sA sB o (IsSphOff ψ B A LB LA Sf) (IsSphOff ψ A B LA LB Sf) K₁ K₂ c →
    FactorsOn A Sf ca cf c →

    IsIrrUnitary σ → IsFactorisation D.sp.cm.sig A.gram δ ξ σ tens →
    LFun.HasParamOffAd D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) (toRep σ) par →
    Formalism.MainNotions.KudlaSiegelWeil.Restr ξ y₁ → Formalism.MainNotions.KudlaSiegelWeil.Restr ξ y₂ → (x₁ : H) = tens y₁ → (x₂ : H) = tens y₂ →
    UnitSphOff A LA δ y₁ y₂ Sf →
    formHom A θ cA m σ ≠ ⊥ → ι₁ ∈ formHom A θ cA m σ → ι₂ ∈ formHom A θ cA m σ →
    Case ψ θ A B χA χB sA t o m (Set.range ι₁ ∪ Set.range ι₂) →

    ConvLeft A LA a δ y₁ y₂ Sf ca cf ma mf (t / 2) →
    let L : ℂ → ℂ := fun s => LFun.LSD D Sf par χB (s + 1 / 2)
    let d : ℂ → ℂ := fun s => LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank s
    let Z : ℂ → ℂ := fun s => zetaS A LA a δ y₁ y₂ (t / 2) s Sf ca cf ma mf
    let ip : ℂ := petersson B ν (lift m K₁ (ι₁ x₁)) (lift m K₂ (ι₂ x₂))
    LiftConv m ν K₁ (ι₁ x₁) ∧ LiftConv m ν K₂ (ι₂ x₂) ∧
      (∃ z, Val (fun s => L s / d s * Z s) (t / 2) z ∧ ip = volQ B ν * conj (beF m ι₁ ι₂) * z) ∧
      ∀ l, HolValueAt L (t / 2) l → ip = volQ B ν * conj (beF m ι₁ ι₂) * (l / d (t / 2) * Z (t / 2))

def EulerForm (D : D7) : Prop :=
  EulerShape D (fun _ _ A B _ _ _ t _ _ _ => (wittIndex B = 0 ∨ wittIndex B < t) ∧ (wittIndex B = 0 ∨ A.rank < t))
    HolValueAt

def LowerLiftsVanish (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle)
    (sA : RealMat A) (o : Bool) (m : Measure (GA D A)) (U : Set (GA D A → ℂ)) : Prop :=
  ∀ (i : ℕ) (hi : i ≤ wittIndex B), 1 ≤ i → ∀ (s' : RealMat (minusHyp B i hi))
    (K K' : GA D A → GA D (minusHyp B i hi) → ℂ) (c : GA D A → ℂ),
    (∀ τ, IsCartanInv (gramAt D (minusHyp B i hi) τ) (s' τ)) →
    IsKernelPair ψ θ A (minusHyp B i hi) χA χB sA s' o (fun _ => True) (fun _ => True) K K' c →
    ∀ f ∈ U, lift m K f = 0

def TowerForm (D : D7) : Prop :=
  EulerShape D (fun ψ θ A B χA χB sA t o m U => 0 < wittIndex B ∧ wittIndex B < t ∧ t ≤ A.rank ∧
    LowerLiftsVanish ψ θ A B χA χB sA o m U) ValueAt

def RallisFormula (D : D7) : Prop := Convergent D ∧ EulerForm D ∧ TowerForm D

example {A B : HSp D} (m : Measure (GA D A)) (K : GA D A → GA D B → ℂ) (f : GA D A → ℂ) (z : ℂ) (h : GA D B) :
    lift m K (z • f) h = conj z * lift m K f h := by
  simp only [lift, petersson, pet, AutomorphicL2Unitary.descend, Pi.smul_apply, smul_eq_mul, map_mul, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun q => by ring)

example {A B : HSp D} {t : ℕ} (hb : B.rank = A.rank + t) (ht : A.rank < t) : wittIndex B < t := by
  have := two_mul_wittIndex_le B
  omega

example {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : RealMat S} {sT : RealMat T} {LS : Lat S}
    {LT : Lat T} {Φ : WO S T → ℂ} (h : IsVacO ψ θ S T sS sT LS LT Φ) :
    IsFockVec ψ θ S T sS sT Φ ∧ IsSphOff ψ S T LS LT ∅ Φ := by
  refine ⟨⟨h.2.theta, 1, fun l hl => ?_⟩, by simpa [IsSphOff] using h.2.lat⟩
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl
  exact h.2.fock p.1 p.2

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift

end
