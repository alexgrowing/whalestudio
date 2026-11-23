import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

def detInv (χ : Chr F E) (h : UA σ Y.J) : ℂ := ((χ (Matrix.GeneralLinearGroup.det h.1))⁻¹ : Circle)

def pet {G : Type} [MeasurableSpace G] (μ : Measure G) (D : Set G) (f f' : G → ℂ) : ℂ := ∫ h in D, f h * star (f' h) ∂μ

def th {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J))
    (φ : UA σ W.J → ℂ) (Ψ : Fn F n d) (g : UA σ X.J) : ℂ := pet μ D φ (theta om Ψ g)

def IsRapid (φ : UA σ Y.J → ℂ) : Prop :=
  Continuous φ ∧ (∀ γ ∈ ratU σ Y.J, ∀ h, φ (γ * h) = φ h) ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖φ h‖ * (qht h : ℝ) ^ N ≤ C

def pairs {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a') :
    Set (Fn F a (a + a') × Fn F a' (a + a')) := {y | y.2 ∈ G.M'.So B.ψ B.τ₁ ∧ PolMatch B G X R Rf y.1 y.2}

def comb {a a' : ℕ} (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (s t : ℂ)
    (y : Fn F a (a + a') × Fn F a' (a + a')) : UA σ G.W.J → ℂ := s • G.M.I om y.1 + t • G.M'.I om' y.2

def DblW : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∃ dd om₂ S l, IsDbl (σ := σ) (A := X) (Y := W) (κ := (Fin n × Fin d) ⊕ (Fin n × Fin d)) B.ψ dd χX om₂ S l ∧
      (∀ Φ₁ ∈ schA F _, ∀ Φ₂ ∈ schA F _, boxFun Φ₁ (star Φ₂) ∈ schA F _ ∧ ∀ g h h' x, IsEmb h h' x →
        detInv χX h' * thetaSum F (om₂ x (S g (boxFun Φ₁ (star Φ₂)))) = theta om Φ₁ g h * star (theta om Φ₂ g h') ∧
        detInv χX h' • om₂ x (boxFun Φ₁ (star Φ₂)) = boxFun (om (1, h) Φ₁) (star (om (1, h') Φ₂))) ∧
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd ∧
      ∀ ν : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∃ c' : ℝ, 0 < c' ∧
        ∀ Ψ₁ ∈ schA F _, ∀ Ψ₂ ∈ schA F _, l (boxFun Ψ₁ (star Ψ₂)) = c' * ∫ u, Ψ₁ u * star (Ψ₂ u) ∂ν

def BoxSec : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n) (M : Model σ A Y) r s r' s', B.IsGood σ → 1 ≤ m → 1 ≤ n → A.IsHerm σ B r s →
    min r s = 0 → Y.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ dd om S l, IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) M.co dd → IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a → ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      IsSec K χ (((m : ℂ) - n) / 2) fun x => l (om x (boxFun Φ₁ (star Φ₂)))

def SWFull : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n) (M : Model σ A Y) r s r' s', B.IsGood σ → 1 ≤ m → 1 ≤ n → A.IsHerm σ B r s →
    min r s = 0 → Y.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ dd om S l, IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) M.co dd → IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a → ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      ∃ U Ê, IsEisCont (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((m : ℂ) - n) / 2)) U Ê ∧ ((m : ℂ) - n) / 2 ∈ U ∧
        ∀ x, Ê (((m : ℂ) - n) / 2) x = (if n < m then 1 else 2) * ⨍ g in M.dom, thetaSum F (om x (S g (boxFun Φ₁ (star Φ₂)))) ∂M.μ

def HgtEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    (∃ K a, IsStab2 (σ := σ) (Y := Y) B K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x) ∧
    ∃ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, Continuous e ∧ ∀ h h', IsEmb h h' (e (h, h'))

def Unfold0 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 →
    ∀ (χ : Chr F E) (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsHecke F E χ → (∀ h h', IsEmb h h' (e (h, h'))) →
    ∀ (f Ê : G2 σ Y → ℂ) (z : ℂ), Continuous f → Continuous Ê → (∀ x, HasSum (eisTerm f x) (Ê x)) →
      (∀ p t x, IsPar p t → f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z * f x) →
    ∀ (μ : Measure (UA σ Y.J)) (D : Set (UA σ Y.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ Y.J) D μ →
      Integrable (fun g => f (e (1, g))) μ → ∀ φ : UA σ Y.J → ℂ, IsRapid φ → ∀ h,
        ∫ h' in D, Ê (e (h, h')) * detInv χ h' * φ h' ∂μ = ∫ g, f (e (1, g)) * detInv χ g * φ (h * g) ∂μ

def HgtInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K a (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → IsHgt K a → (∀ h h', IsEmb h h' (e (h, h'))) →
    ∀ μ : Measure (UA σ Y.J), μ.IsHaarMeasure → ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ

def LocDist : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (n d : ℕ) (ξ : (Fv F v)ˣ →* ℂˣ),
    (∀ t : ℝ, 0 < t → (ξ (unifAt v) : ℂ) ≠ t) → ∀ l : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ φ ∈ SB _, ∀ h : GL (Fin d) (Fv F v), l (fun y => φ (y * h.1)) = ξ (Matrix.GeneralLinearGroup.det h) * l φ) →
    (n < d → ∀ φ ∈ SB _, l φ = 0) ∧
    (n = d → ∀ φ ∈ SB _, ∀ g : GL (Fin n) (Fv F v), l (fun y => φ (g.1 * y)) = ξ (Matrix.GeneralLinearGroup.det g) * l φ)

def GoodNe : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∀ v, X.Good v →
    Nonempty (E →ₐ[F] Fv F v) ∧ ∀ t : E →ₐ[F] Fv F v, chrW X.ν t (unifAt v) ≠ 1

def ConstOfGood : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) r s, B.IsGood σ → X.IsHerm σ B r s → 2 ≤ n → ∀ (T : Finset (Pl F)) (f : UA σ X.J → ℂ),
    Continuous f → (∀ γ ∈ ratU σ X.J, ∀ g, f (γ * g) = f g) →
    (∀ v ∉ T, SplitsFully E v → ∀ u ∈ UAt σ X (evFin F v), ∀ g, f (g * u) = f g) → ∀ g, f g = f 1

def ThConst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ s t, (∀ y ∈ pairs B G X R Rf, IsRapid (comb G om om' s t y)) →
    ∀ (μ : Measure (UA σ G.W.J)) (D : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) D μ →
    ∀ y ∈ pairs B G X R Rf, (∀ Ψ ∈ schA F _, ∀ g, th om μ D (comb G om om' s t y) Ψ g = th om μ D (comb G om om' s t y) Ψ 1) ∧
      ∀ Ψ ∈ schA F _, ∀ g, th om' μ D (comb G om om' s t y) Ψ g = th om' μ D (comb G om om' s t y) Ψ 1

def PairsStable : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.p = 0 → G.q = 0 → (∀ y ∈ pairs B G X R Rf, ∀ y' ∈ pairs B G X R Rf, ∀ c : ℂ, y + c • y' ∈ pairs B G X R Rf) ∧
    ∀ y ∈ pairs B G X R Rf, ∀ h, (om (1, h) y.1, om' (1, h) y.2) ∈ pairs B G X R Rf

def PairsIrr : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.p = 0 → G.q = 0 → ∀ N : Submodule ℂ (Fn F a (a + a') × Fn F a' (a + a')), (N : Set _) ⊆ pairs B G X R Rf →
    (∀ y ∈ pairs B G X R Rf, PolMatch B G X R Rf y.1 0 → y ∈ N) → (∀ y ∈ N, ∀ h, (om (1, h) y.1, om' (1, h) y.2) ∈ N) →
    (∀ y ∈ N, PolMatch B G X R Rf y.1 0) ∨ pairs B G X R Rf ⊆ N

def HermLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.p = 0 → G.q = 0 →
    ∀ (μ : Measure (UA σ G.W.J)) (D : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) D μ →
    ∀ s t s' t', ∃ lam : ℂ, ∀ y ∈ pairs B G X R Rf, ∀ y' ∈ pairs B G X R Rf,
      pet μ D (comb G om om' s t y) (comb G om om' s' t' y') = lam * pet μ D (comb G om om' 0 1 y) (comb G om om' 0 1 y')

def CoefLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.p = 0 → G.q = 0 →
    ∀ (μ : Measure (UA σ G.W.J)) (D : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) D μ →
    ∀ s t (lam : ℂ), (∀ y ∈ pairs B G X R Rf, ∀ y' ∈ pairs B G X R Rf,
      pet μ D (comb G om om' s t y) (comb G om om' s t y') = lam * pet μ D (comb G om om' 0 1 y) (comb G om om' 0 1 y')) →
    ∀ y ∈ pairs B G X R Rf, ∀ Ψ ∈ PolData B G.M',
      pet G.M'.μ G.M'.dom (th om' μ D (comb G om om' s t y) Ψ) (th om' μ D (comb G om om' s t y) Ψ) =
        lam * pet G.M'.μ G.M'.dom (th om' μ D (comb G om om' 0 1 y) Ψ) (th om' μ D (comb G om om' 0 1 y) Ψ)

def LInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
    (∀ s : ℂ, 1 < s.re → Λ s = charL X.ν (∅ : Set (Pl F)) s ∧ Λ s = charL X.ν⁻¹ (∅ : Set (Pl F)) s) ∧
    ∀ z : ℤ, -((a + a' : ℕ) : ℤ) ≤ 2 * z → Λ z ≠ 0

def NonZeroBot : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → G.p = 0 → G.q = 0 →
    (∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0) ∧ ∃ Φ' ∈ PolData B G.M', G.M'.I om' Φ' ≠ 0

end GlobalTheory.ThK.Dbl

end
