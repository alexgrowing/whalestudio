import Development.WeilBound.ThetaLifts.CTKernel

noncomputable section

namespace PositivityTheory.ThKG

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

def LeviEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁)
    (H' : Plane E d d₁) (i₀ i₁ r s : ℕ), B.IsGood σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ h₁ : UA σ W₁.J, ∃ m : UA σ W.J, IsLevi H' 1 h₁ m

def PolDense : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    Dense (M.Pol B.ψ B.emb : Set (SInf F (Fin n × Fin d)))

def Claim {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a') : Prop :=
  (∃ c, c ≠ 0 ∧ PolConst B G X om om' R Rf c) ∧ (∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0) ∧
    ∃ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' Φ' ≠ 0

def Below (n : ℕ) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.p + G.q < n → Claim B G X om om' R Rf

def EndB' : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → 1 ≤ G.q → Below (G.p + G.q) →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      (∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ fa fb fa' fb', Split2 W₁ H' X (G.M.I om Φ) fa fb →
        Split2 W₁ H' X (G.M'.I om' Φ') fa' fb' → ∀ h₁ m, IsLevi (W₁ := W₁) H' 1 h₁ m → fb m = c * fb' m) → PolConst B G X om om' R Rf c

def EndA' : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p → Below (G.p + G.q) →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      (∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ fa fb fa' fb', Split2 W₁ H' X (G.M.I om Φ) fa fb →
        Split2 W₁ H' X (G.M'.I om' Φ') fa' fb' → ∀ h₁ m, IsLevi (W₁ := W₁) H' 1 h₁ m → fa m = c * fa' m) → PolConst B G X om om' R Rf c

def LocB' : Prop :=
  ∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (R : RealMaps F a (b + 2)) (R₁ : RealMaps F a b) e e', IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e →
      IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ → Below (G.p + G.q) →
      ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) Φ' ∈ G₁.M'.So B.ψ B.τ₁ ∧
        PolMatch B G₁ X R₁ Rf₁ ((C * stepFac B X e₁ e₂ s H.𝔟 H'.𝔟 (-(((a - (b + 2)) / 2 : ℕ) : ℤ)) *
          charL X.ν (X.S₀ : Set (Pl F)) ((((a - (b + 2)) / 2 : ℕ) : ℂ) + 1)) • e Φ) (cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) Φ')

def LocA' : Prop :=
  ∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (R : RealMaps F (b + 2) a') (R₁ : RealMaps F b a') e e', IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
      IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ → Below (G.p + G.q) →
      ∀ Φ Φ', PolMatch B G X R Rf Φ Φ' →
        PolMatch B G₁ X R₁ Rf₁ (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Φ) ((C * stepFac B X e₁ e₂ s H.𝔟 H'.𝔟 (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) *
          charL X.ν (X.S₀ : Set (Pl F)) (((b + 2 - a') / 2 : ℕ) : ℂ)) • e' Φ')

theorem endB'_of (h : EndB) : EndB' := fun F E _ _ _ _ _ σ B a a' G X om om' R Rf m q _ =>
  h F E σ B a a' G X om om' R Rf m q

theorem endA'_of (h : EndA) : EndA' := fun F E _ _ _ _ _ σ B a a' G X om om' R Rf m q p _ =>
  h F E σ B a a' G X om om' R Rf m q p

end PositivityTheory.ThKG

end
