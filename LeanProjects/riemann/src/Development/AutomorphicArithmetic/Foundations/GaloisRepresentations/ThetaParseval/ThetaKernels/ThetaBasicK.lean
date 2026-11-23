import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Pair
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
structure IsPair_k (B : Base F E) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ) : Prop where
  base : _root_.UpperTheory.TP.W.GoodK σ B
  herm : X.IsHerm σ B r s
  skew : W.IsSkew σ B r' s'
  good : M.IsGood B.ψ
  hX : IsHecke F E χX
  hW : IsHecke F E χW
  resX : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n
  resW : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d
  weil : M.IsWeil B.ψ χX χW om
end Pair
variable {a a' : ℕ}
def ThetaBasic_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' →
    (∀ Φ ∈ schA F _, Continuous (fun x : UA σ X.J × UA σ W.J => theta om Φ x.1 x.2) ∧
      (∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Φ (γ * g) (γ' * h) = theta om Φ g h) ∧
      ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k) ∧
    ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ g h, Continuous fun f : SInf F (Fin n × Fin d) => theta om (pureA F f φ) g h
def StabEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B r s →
    ∃ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K ∧ IsCompact (K : Set (UA σ X.J)) ∧
      μK.IsHaarMeasure ∧ μ.IsHaarMeasure
def ActsEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ v : Pl F,
    (∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃! φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (om (g, h)) φ φ₁) ∧
    (∀ u, At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃! φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁) ∧
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ U ∈ 𝓝 (1 : UA σ X.J × UA σ W.J), ∀ x ∈ U, x.1 ∈ UAt σ X (evFin F v) →
      x.2 ∈ UAt σ W (evFin F v) → Acts (evFin F v) (om x) φ φ
end GlobalTheory.ThK
end
end
