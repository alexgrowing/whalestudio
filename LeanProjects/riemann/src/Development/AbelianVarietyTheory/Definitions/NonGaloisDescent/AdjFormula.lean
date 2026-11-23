import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def ThetaSchur (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T' : HSp D), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (WO S T')) (𝓕 : Set (WO S T')), IsCovolOne (ratL T' S) μ 𝓕 →
    ∀ L : Module.End ℂ (WO S T' → ℂ), (∀ f, IsThetaFunO ψ S T' f → IsThetaFunO ψ S T' (L f)) →
      (∃ C : ℝ, ∀ f, IsThetaFunO ψ S T' f → nrm2 μ 𝓕 (L f) ≤ C * nrm2 μ 𝓕 f) →
      (∀ w f, IsThetaFunO ψ S T' f → L (heisO ψ S T' w f) = heisO ψ S T' w (L f)) →
      ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T' f → L f = c • f

abbrev levW (R : RealDat D A Ks) (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) := levG _ (R.βW i) (R.datWp i R.triv)

def coef (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i)))
    (g : GA D (Wc D i)) : ℂ :=
  thetaIP μ 𝓕 (R.ωP i t (1, g) (R.vP i t)) (R.vP i t) / thetaIP μ 𝓕 (R.vP i t) (R.vP i t)

def jointVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W) :
    WO (Vc D i) (Wc D i) → ℂ :=
  R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)

def IsUnitVec (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) : Prop :=
  ∀ ρ, ‖((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)‖ = 1

def val (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : (R.HW i (sg0 D A)).H) :
    GA D (Wc D i) → ℂ :=
  (R.HW i (sg0 D A)).e x fun ρ => v ρ

def AdjFormula (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ th, IsRaw R i t th → ∀ v, IsUnitVec R i v → ∀ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W),
    ∃ a : ℝ, 0 < a ∧ ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
      (a : ℂ) * ∑ k, ∫ h in R.fdV i t,
        star (upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v x) h) *
          upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h ∂(R.νV i t)

def LevFix (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ k ∈ levW R i, ∀ P, R.ωP i t (1, k) (R.ptP i t P) = R.ptP i t P

def FactInf (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), ∀ P P',
    thetaIP μ 𝓕 (R.ωP i t (1, u * γ) (R.ptP i t P)) (R.ptP i t P') =
      thetaIP μ 𝓕 (R.ωP i t (1, u) (R.ptP i t P)) (R.ptP i t P') * coef R i t μ 𝓕 γ

def RealLow (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v, IsUnitVec R i v → ∀ w, ∀ u ∈ GinfC (Wc D i),
    thetaIP μ 𝓕 (jointVec R i t v w) (R.ωP i t (1, u) (jointVec R i t v w)) =
      thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) *
        ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
          (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u)
            ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ

def VecNe (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → thetaIP μ 𝓕 (R.vP i t) (R.vP i t) ≠ 0 ∧
    ∃ v w, IsUnitVec R i v ∧ thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) ≠ 0

def trPair (R : RealDat D A Ks) (i : Fin D.R.m) (γ : GA D (Wc D i)) (x y : (R.HW i (sg0 D A)).H) : ℂ :=
  ipAt (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) ((R.HW i (sg0 D A)).e x)
    (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y))

def FinSum (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ th, IsRaw R i t th → ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ a : ℝ, 0 < a ∧ ∀ x y,
    HasSum (fun q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) =>
      (a : ℂ) * (coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y))
      ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ

def TrivAt (V : HSp D) (f : AE D) (g : GA D V) : Prop := ∀ a b, f * (mt V g - 1) a b = 0

def IsFinIdem (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D) : Prop :=
  ∃ ε, IsPlaceIdem D v ε ∧ f = algebraMap (AF D.host.F) (AE D) ε

def FinMult (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f →
    ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → ∀ k, SuppF (Wc D i) f k →
      coef R i t μ 𝓕 (γ * k) = coef R i t μ 𝓕 γ * coef R i t μ 𝓕 k

def BadSupp (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f →
    ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → coef R i t μ 𝓕 k = 0

def latIndex (W : HSp D) (g : GA D W) : ℕ :=
  ((Formalism.L2.NTheta.LamHat W).map (finMat D.sp.cm.sig W.gram g).mulVecLin.toAddMonoidHom).relIndex (Formalism.L2.NTheta.LamHat W)

def GoodMod (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f →
    (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ k, SuppF (Wc D i) f k →
      ‖coef R i t μ 𝓕 k‖ ^ 2 * (latIndex (Wc D i) k : ℝ) ^ (Vc D i).rank = 1

def IndexSum (W : HSp D) (n : ℕ) : Prop :=
  ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v f, IsFinIdem D v f →
    ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') →
      ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ s v

def LocSmall (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 →
    ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v f, IsFinIdem D v f →
      ∀ C : Finset (GA D (Wc D i)), (∀ g ∈ C, SuppF (Wc D i) f g ∧ g ∉ levW R i) →
        (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ levW R i → g = g') → ∑ g ∈ C, ‖coef R i t μ 𝓕 g‖ ≤ s v

def LevProd (R : RealDat D A Ks) (i : Fin D.R.m) : Prop :=
  levW R i ≤ GfC (Wc D i) ∧ (∀ k ∈ levW R i, levChi _ (R.βW i) (R.datWp i R.triv) k = 1) ∧
  ∃ cmp : HeightOneSpectrum (𝓞 D.host.F) → (GA D (Wc D i) →* GA D (Wc D i)),
    (∀ v f, IsFinIdem D v f → ∀ g, SuppF (Wc D i) f (cmp v g) ∧ TrivAt (Wc D i) f (g * (cmp v g)⁻¹)) ∧
    (∀ g ∈ GfC (Wc D i), (g ∈ levW R i ↔ ∀ v, cmp v g ∈ levW R i) ∧ {v | cmp v g ∉ levW R i}.Finite)

def TransLaws (R : RealDat D A Ks) (i : Fin D.R.m) : Prop :=
  (∀ v f, IsFinIdem D v f → ∀ α, SuppF (Wc D i) f α → ∃ C : Finset (GA D (Wc D i)), (∀ γ ∈ C, SuppF (Wc D i) f γ) ∧
      IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) ∧
  (∀ v f, IsFinIdem D v f → ∀ α, SuppF (Wc D i) f α → ∀ C : Finset (GA D (Wc D i)), (∀ γ ∈ C, SuppF (Wc D i) f γ) →
      IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C →
      ∀ y, ∃ y', (R.HW i (sg0 D A)).e y' = heckeOn (R.MW i (sg0 D A)) C ((R.HW i (sg0 D A)).e y) ∧
        ∀ γ ∈ GfC (Wc D i), ∀ x, trPair R i γ x y' = ∑ δ ∈ C, trPair R i (γ * δ) x y) ∧
  (∀ γ ∈ GfC (Wc D i), ∃ B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H, ‖B‖ ≤ 1 ∧ ∀ x y, trPair R i γ x y = ⟪x, B y⟫_ℂ) ∧
  (∀ γ ∈ GfC (Wc D i), ∀ k ∈ levW R i, ∀ k' ∈ levW R i, ∀ x y, trPair R i (k * γ * k') x y = trPair R i γ x y) ∧
  (∀ γ ∈ GfC (Wc D i), ∀ x y, trPair R i γ⁻¹ x y = star (trPair R i γ y x)) ∧
  ∀ x y, trPair R i 1 x y = ⟪x, y⟫_ℂ

end GlobalTheory.RawLift

end
