import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsLocPart {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ) : Prop :=
  ei ≠ 0 ∧ (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
    ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)

def fac (χ : Chr F E) (z : ℝ) (t : (AE F E)ˣ) : ℂ := (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)

def LocOpMul : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ v : Pl F, ∀ x y : UA σ X.J × UA σ W.J,
      x.1 ∈ UAt σ X (evFin F v) → x.2 ∈ UAt σ W (evFin F v) → y.1 ∈ UAt σ X (evFin F v) → y.2 ∈ UAt σ W (evFin F v) →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), locOp v (om (x * y)) φ = locOp v (om x) (locOp v (om y) φ)

def EvZeroLocLaw : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ ei ev, IsLocPart M M₁ e ei ev → ∀ v : Pl F, ∀ g ∈ UAt σ X (evFin F v), ∀ t h₁ m, IsLevi H' t h₁ m →
      m ∈ UAt σ W (evFin F v) → h₁ ∈ UAt σ W₁ (evFin F v) → ∀ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        ev v (locOp v (om (g, u * m)) φ) = fac χX ((n : ℝ) / 2) t • locOp v (om₁ (g, h₁)) (ev v φ)

def EvZeroInfLaw : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ ei ev, IsLocPart M M₁ e ei ev → ∀ g ∈ UAt σ X (evI F), ∀ t h₁ m, IsLevi H' t h₁ m →
      m ∈ UAt σ W (evI F) → h₁ ∈ UAt σ W₁ (evI F) → ∀ u ∈ unip σ W H', u ∈ UAt σ W (evI F) →
      ∀ f : SInf F (Fin n × Fin d),
        ei (locOpInf (om (g, u * m)) f) = fac χX ((n : ℝ) / 2) t • locOpInf (om₁ (g, h₁)) (ei f)

def ConeLawB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      (∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ ∈ SB (Fin b × Fin (a + b) → Fv F v)) ∧
      (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, u)) φ) =
          coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ) ∧
      ∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, m)) φ) =
          fac X.β ((a : ℝ) / 2) t •
            locOp v (om₁' (1, h₁)) (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ)

def ConeLawA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      (∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ ∈ SB (Fin b × Fin (b + a') → Fv F v)) ∧
      (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, u)) φ) =
          coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ) ∧
      ∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, m)) φ) =
          fac X.α ((a' : ℝ) / 2) t •
            locOp v (om₁ (1, h₁)) (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ)

def ConeInvB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ l : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V' (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v), l (locOp v (om₁' (g₀, 1)) ψ) = l ψ) →
      ∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        l (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (g, 1)) φ)) =
          l (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ)

def ConeInvA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (b + a') → Fv F v), l (locOp v (om₁ (g₀, 1)) ψ) = l ψ) →
      ∀ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        l (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (g, 1)) φ)) =
          l (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ)

def EvInvB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (l : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      (∀ g₀ ∈ UAt σ G₁.V' (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v), l (locOp v (om₁' (g₀, 1)) ψ) = l ψ) →
      (∀ u ∈ unip σ G.V' H, u ∈ UAt σ G.V' (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        l (ev' v (locOp v (om' (u, 1)) φ)) = l (ev' v φ)) ∧
      ∀ g₀ g, IsLevi H 1 g₀ g → g ∈ UAt σ G.V' (evFin F v) → g₀ ∈ UAt σ G₁.V' (evFin F v) →
        ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), l (ev' v (locOp v (om' (g, 1)) φ)) = l (ev' v φ)

def EvInvA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      (∀ g₀ ∈ UAt σ G₁.V (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (b + a') → Fv F v), l (locOp v (om₁ (g₀, 1)) ψ) = l ψ) →
      (∀ u ∈ unip σ G.V H, u ∈ UAt σ G.V (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        l (ev v (locOp v (om (u, 1)) φ)) = l (ev v φ)) ∧
      ∀ g₀ g, IsLevi H 1 g₀ g → g ∈ UAt σ G.V (evFin F v) → g₀ ∈ UAt σ G₁.V (evFin F v) →
        ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), l (ev v (locOp v (om (g, 1)) φ)) = l (ev v φ)

def InfInvB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ l : SInf F (Fin b × Fin (a + b)) →L[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V' (evI F), ∀ f, l (locOpInf (om₁' (g₀, 1)) f) = l f) →
      (∀ u ∈ unip σ G.V' H, u ∈ UAt σ G.V' (evI F) → ∀ f, l (ei' (locOpInf (om' (u, 1)) f)) = l (ei' f)) ∧
      (∀ g₀ g, IsLevi H 1 g₀ g → g ∈ UAt σ G.V' (evI F) → g₀ ∈ UAt σ G₁.V' (evI F) →
        ∀ f, l (ei' (locOpInf (om' (g, 1)) f)) = l (ei' f)) ∧
      ∀ g ∈ UAt σ G.V' (evI F), ∀ f : SInf F (Fin (b + 2) × Fin (a + (b + 2))),
        ∫ k, ∫ y, l (coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOpInf (om' (g, 1)) f)
          k.1 y.1) ∂μ ∂μK =
        ∫ k, ∫ y, l (coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f k.1 y.1) ∂μ ∂μK

def InfInvA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ l : SInf F (Fin b × Fin (b + a')) →L[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V (evI F), ∀ f, l (locOpInf (om₁ (g₀, 1)) f) = l f) →
      (∀ u ∈ unip σ G.V H, u ∈ UAt σ G.V (evI F) → ∀ f, l (ei (locOpInf (om (u, 1)) f)) = l (ei f)) ∧
      (∀ g₀ g, IsLevi H 1 g₀ g → g ∈ UAt σ G.V (evI F) → g₀ ∈ UAt σ G₁.V (evI F) →
        ∀ f, l (ei (locOpInf (om (g, 1)) f)) = l (ei f)) ∧
      ∀ g ∈ UAt σ G.V (evI F), ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
        ∫ k, ∫ y, l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) (locOpInf (om (g, 1)) f) k.1 y.1) ∂μ ∂μK =
        ∫ k, ∫ y, l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f k.1 y.1) ∂μ ∂μK

def LemFZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ ei ev, IsLocPart M M₁ e ei ev → ∀ v : Pl F,
      (∀ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) → ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        ev v (locOp v (om (1, u * h)) φ) = ev v (locOp v (om (1, h)) φ)) ∧
      (∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ W (evFin F v) → h₁ ∈ UAt σ W₁ (evFin F v) → ∀ h ∈ UAt σ W (evFin F v),
        ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (locOp v (om (1, m * h)) φ) =
          fac χX ((n : ℝ) / 2) t • locOp v (om₁ (1, h₁)) (ev v (locOp v (om (1, h)) φ))) ∧
      ∀ (P₁ : Type) [AddCommGroup P₁] [Module ℂ P₁] (p₁ : ((Fin n × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] P₁),
        augAt om₁ v ≤ LinearMap.ker p₁ → ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v),
        ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
          p₁ (ev v (locOp v (om (1, h)) (locOp v (om (g, 1)) φ))) = p₁ (ev v (locOp v (om (1, h)) φ))

def LemFConeB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, u * h)) φ) =
          coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, h)) φ)) ∧
      (∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, m * h)) φ) =
          fac X.β ((a : ℝ) / 2) t • locOp v (om₁' (1, h₁))
            (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, h)) φ))) ∧
      ∀ (P₁ : Type) [AddCommGroup P₁] [Module ℂ P₁] (p₁ : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] P₁),
        augAt om₁' v ≤ LinearMap.ker p₁ → ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
          p₁ (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1)
            (locOp v (om' (1, h)) (locOp v (om' (g, 1)) φ))) =
          p₁ (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, h)) φ))

def LemFConeA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, u * h)) φ) =
          coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, h)) φ)) ∧
      (∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, m * h)) φ) =
          fac X.α ((a' : ℝ) / 2) t • locOp v (om₁ (1, h₁))
            (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, h)) φ))) ∧
      ∀ (P₁ : Type) [AddCommGroup P₁] [Module ℂ P₁] (p₁ : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] P₁),
        augAt om₁ v ≤ LinearMap.ker p₁ → ∀ g ∈ UAt σ G.V (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
          p₁ (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2)
            (locOp v (om (1, h)) (locOp v (om (g, 1)) φ))) =
          p₁ (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, h)) φ))

end GlobalTheory.ThK.LemF

end
